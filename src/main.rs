/*

SAT SOLVER

Author: Ang Ray Yan
Ported to Rust by jarsp

Functionality Overview (Relevant resource links in code):
- Conflict Driven Clause Learning (CDCL) Algorithm
- Basic preprocessing: Existing unit clauses and pure literal detection
- 2 Watch Literals structure for Unit Propagation
- Recursive clause minimization on learnt 1-UIP clause
- Learning Rate Branching (LRB) Heuristic (with reason-side rate + locality extension)
- Literal block distance (LBD) computation
- Luby (Sequence) Restart
- Clause reduction: keep LBD <= 4, clause subsumption test (no self-subsumption)

Abbreviations used (if any):
* Lit (Literal)      - A variable or the negation of a variable
* Asgmt (Assignment) - A combination of a literal and true/false value
* Var (Variable)     - A symbol that represents an object. Can be assigned true or false
* Dec (Decision)     - The current decision made by CDCL algorithm on true/false value of literals
* WL (Watch Literal) - A literal in a clause that when turned false, will trigger unit propagation on the other
* (UN)SAT            - (UN)Satisfied (i.e. all (UN)true, be it variable / clause / entire CNF formula)
*/

use std::{fs::File, path::Path, io::{self, BufRead}, num, process};
use thiserror::Error;

// -------------------- DEFINITIONS / STRUCTS --------------------

const ENABLE_RANDOM: bool = false;
const DEBUG: bool = true;

macro_rules! ternary { ($cond:expr, $t:expr, $f:expr) => (if $cond { $t } else { $f }) }

const INVALID_LIT: Lit = 0;
const INVALID_CLAUSE_INDEX: u32 = 1 << 30;
const INVALID_DEC_INDEX: u32 = 1 << 30;
const INVALID_DECISION: Decision = Decision {
    lit: INVALID_LIT,
    dec_level:  -1,
    dec_trail_index: INVALID_DEC_INDEX,
    reason_clause_index: INVALID_CLAUSE_INDEX,
};

const LRB_ALPHA_INITIAL_VALUE: f64 = 0.4;
const LRB_DECAY_RATE: f64 = 0.95;
const LRB_ALPHA_DECAY: f64 = 0.000001;
const LRB_ALPHA_MIN: f64 = 0.06;

// 1 = positive, 0 = negative
type Lit = u32;
macro_rules! lit_make { ($x:expr, $y:expr) => (($x << 1) as Lit + $y as Lit); }
macro_rules! lit_neg { ($x:expr) => ($x ^ 1); }
macro_rules! lit_sign { ($x:expr) => (($x & 1) != 0); }
macro_rules! lit_var { ($x:expr) => (($x >> 1) as usize);}

#[derive(Debug, PartialEq, Eq)]
enum ClauseStatus {
    Unknown,
    UnknownUnit,
    Satisfied,
    Unsatisfied,
}

// Learing Rate Branching (LRB) Statistics implemented with Reason Side Rate (RSR) and locality extension
// Source: https://cs.uwaterloo.ca/~ppoupart/publications/sat/learning-rate-branching-heuristic-SAT.pdf
#[derive(Debug, Clone)]
struct LrbVarStats {
    value: f64,                     // EMA (exp. Moving Average) value associated with ERWA algo. for MAB
    assigned: u32,                  // learntCounter value when variable was assigned
    participated_or_reasoned: u32,  // participated: incremented whenever variable participated in
                                    //               generating conflict / part of learnt clause
                                    // reasoned: number of learnt clauses v reasoned since assigned(v)
}

#[derive(Debug)]
struct LrbStats {
    alpha: f64,
    learnt_counter: u32,
    var_stats: Vec<LrbVarStats>,
}

// Source: https://hal-univ-artois.archives-ouvertes.fr/hal-03299473/document (On the Glucose SAT Solver)
#[derive(Debug)]
struct Clause {
    last_sat_lit: Lit,              // Last known assignment satisfying clause
    lits: Vec<Lit>,                 // List of literals in the clause
    wl: [Lit; 2],                   // 2x Watch Literals for this clause
    lbd: i16,                       // Literal Block Distance (LBD) - not expecting to exceed "short" MAX value
}

#[derive(Debug, Clone)]
struct Decision {
    lit: Lit,
    dec_level: i32,                 // Value of decision level when this decision was made
    dec_trail_index: u32,           // Index of decision in the decision trail
    reason_clause_index: u32,       // Index of clause that induced this decision (e.g. due to unit prop)
}

// Common structures used by all parts of the algorithm
// Note: for STL vector, refrain from using pop_back() to achieve performance (time) improvement

#[derive(Debug)]
struct SatContext {
    num_generated_unit_clauses: u32,
    is_sat: bool,
    num_vars: u32,
    num_decisions: u32,
    lit_array_size: u32,
    num_given_clauses: u32,
    num_core_clauses: u32,
    dec_level: i32,
    conflicts_since_restart: u32,
    luby_restart: (u32, u32),
    dec_map: Vec<Decision>,
    dec_trail: Vec<Lit>,
    clauses: Vec<Box<Clause>>,
    two_wl: Vec<Vec<u32>>,
    lrb: LrbStats,
    temp_lit: Lit,
}

// Error handling
// TODO: Improve display of errors
#[derive(Error, Debug)]
pub enum SatError {
    #[error("File I/O error")]
    Io(#[from] io::Error),
    #[error("Generic parsing error")]
    ParseGeneric,
    #[error("Int parsing error")]
    ParseInt(#[from] num::ParseIntError),
}

// -------------------- NICE --------------------

impl SatContext {
    // -------------------- DISPLAY / DEBUG FUNCTIONALITY --------------------

    fn display_lit(lit: Lit) {
        print!("{}{}", ternary!(lit_sign!(lit), "", "-"), lit_var!(lit));
    }

    fn display_clause(&self, clause_index:u32) {
        let clause = &self.clauses[clause_index as usize];

        print!("(");
        clause.lits.iter().for_each(|&l| { SatContext::display_lit(l); print!(" ") });
        print!("<{} ", ternary!(clause_index < self.num_given_clauses, "G", "L"));
        SatContext::display_lit(clause.wl[0]);
        print!(" ");
        SatContext::display_lit(clause.wl[1]);
        print!("> LBD: {}", clause.lbd);
        print!(")");
    }

    fn display_decisions(&self) {
        print!("\nc Decisions (Level 0 reason clauses may be absent):\nc ---------------");
        for i in 0..self.num_decisions as usize {
            let dec = &self.dec_map[lit_var!(self.dec_trail[i])];
            let new_dec_level =
                if i == 0 {
                    true
                } else {
                    dec.dec_level != self.dec_map[lit_var!(self.dec_trail[i - 1])].dec_level
                };
            if new_dec_level { print!("\nc Level #{}: ", dec.dec_level) };
            if dec.reason_clause_index != INVALID_CLAUSE_INDEX {
                print!(" ->")
            } else {
                print!("\nc[!]");
            }
            print!(" (");
            SatContext::display_lit(dec.lit);
            print!(" )");
            if dec.reason_clause_index != INVALID_CLAUSE_INDEX {
                print!(" [#{}-", dec.reason_clause_index);
                self.display_clause(dec.reason_clause_index);
                print!("]");
            }
        }
        println!("");
    }

    fn display_model(&self) {
        // Unsatisifiable
        if !self.is_sat {
            println!("s UNSATISFIABLE");
            return;
        }

        // Satisfiable
        self.display_decisions();
        println!("s SATISFIABLE");
        print!("v ");
        for i in 1..(self.num_vars as usize + 1) {
            SatContext::display_lit(self.dec_map[i].lit);
            print!(" ");
            if i % 20 == 0 && i < (self.num_vars as usize) {
                print!("\nv ");
            }
        }
        println!("");
    }

    // -------------------- DIMACS PARSING / IO --------------------

    fn read_dimacs(&mut self, filename: &Path) -> Result<(), SatError> {
        // Prepare file
        let file = File::open(filename)?;
        let mut lines = io::BufReader::new(file).lines();

        // Parse header
        let header = lines.next().ok_or(SatError::ParseGeneric)??;
        let header_tokens: Vec<&str> = header.split_whitespace().collect();
        if header_tokens.len() != 4 ||
           header_tokens[0] != "p" ||
           header_tokens[1] != "cnf" {
            return Err(SatError::ParseGeneric)
        }

        self.num_vars = header_tokens[2].parse()?;
        self.num_given_clauses = header_tokens[3].parse()?;

        // Initialize context (assume SAT first until proven otherwise)
        self.is_sat = true;
        self.dec_level = 0;
        self.num_generated_unit_clauses = 0;
        self.num_decisions = 0;
        self.lit_array_size = (self.num_vars + 1) << 1;
        self.num_core_clauses = self.num_given_clauses;
        self.luby_restart = (1, 1);

        // Resize various arrays for performance
        self.clauses.clear();
        self.clauses.reserve(self.num_given_clauses as usize);
        self.dec_trail = vec![INVALID_LIT; self.num_vars as usize + 1];
        self.dec_map = vec![INVALID_DECISION; self.num_vars as usize + 1];
        self.two_wl = vec![vec![]; self.lit_array_size as usize];

        // Process literals and clauses
        for (i, line) in lines.enumerate() {
            let mut clause = Box::new(Clause {
                last_sat_lit: INVALID_LIT,
                lits: vec![],
                wl: [INVALID_LIT, INVALID_LIT],
                lbd: 0,
            });

            // Parse lits
            for lit_str in line?.split_whitespace() {
                let l: i32 = lit_str.parse()?;
                let lit = lit_make!(l.abs(), l > 0);
                if lit == INVALID_LIT { break };
                clause.lits.push(lit);
            }

            // Setup 2-WL structure (maybe random or not)
            // TODO: Panics if too many clauses
            for j in 0..2.min(clause.lits.len()) {
                // Locate a watch literal candidate (possibly at random)
                let mut index;
                loop {
                    index = ternary!(ENABLE_RANDOM, rand::random::<usize>() % clause.lits.len(), j) as usize;
                    if clause.wl[index] == INVALID_LIT { break };
                }
                self.two_wl[clause.lits[index] as usize].push(i as u32);
                clause.wl[j] = clause.lits[index];
            }

            self.clauses.push(clause);
        }

        if self.clauses.len() != self.num_given_clauses as usize {
            return Err(SatError::ParseGeneric);
        }

        Ok(())
    }

    // -------------------- CLAUSE MINIMIZATION --------------------
    
    fn is_marked(&self, initial_var: usize, current_var: usize, marked: &mut Vec<bool>, visited: &mut Vec<bool>) -> bool {
        // If visited, use the marked value
        if visited[current_var] { return marked[current_var] };
        visited[current_var] = true;

        // Found something that is already marked
        if initial_var != current_var && marked[current_var] { return true };

        // If no reason clause exists, cannot check for marked literals, not subsumed
        let new_reason_clause_index = self.dec_map[current_var].reason_clause_index;
        if new_reason_clause_index == INVALID_CLAUSE_INDEX ||
           self.dec_map[current_var].dec_level == 0 {
            return false;
        }

        // Otherwise, continue searching based on reason clause
        let new_reason_clause = &self.clauses[new_reason_clause_index as usize];

        // https://www.researchgate.net/publication/220944584_Minimizing_Learned_Clauses
        // Expecting about 30% less literals generated total --> speeds up unit prop.
        // during clause checking for LARGER problems
        // Check if literal in reason clause is marked or not (1 is not marked = currentVar is not marked)
        // (1) Local clause minimization
        //result = result && (*marked)[newReasonClause->lits[j]];
        // (2) Recursive clause minimization
        let mut result = true;
        for lit in &new_reason_clause.lits {
            result &= self.is_marked(initial_var, lit_var!(lit), marked, visited);
        }
        marked[current_var] = result;

        result
    }

    fn minimize_learnt_clause(&self, learnt_clause_lits: &mut Vec<Lit>) {
        // Literal marking (mark all those existing in learnt clause except 1UIP)
        let mut marked = vec![false; self.num_vars as usize + 1];
        let mut visited = vec![false; self.num_vars as usize + 1];

        // For each marked literal X, if all "antecedents" (literals in reason clauses) are marked at some point,
        // then X can be removed from clause as it can be "inferred" by others (i.e. clause minimized)
        let mut back = learnt_clause_lits.len();
        let mut i = 0;
        while i < back {
            let learnt_var = lit_var!(learnt_clause_lits[i]);
            
            // Note: must at least check for reason clause of learnt_var, regardless visited in previous iterations or not
            visited[learnt_var] = false;
            marked[learnt_var] = true;

            // If literal can be inferred, can be removed (move another literal from the back to replace it)
            if self.is_marked(learnt_var, learnt_var, &mut marked, &mut visited) {
                back -= 1;
                learnt_clause_lits[i] = learnt_clause_lits[back];
            } else {
                i += 1;
            }
            marked[learnt_var] = true;
        }
        learnt_clause_lits.truncate(back);
    }

    // -------------------- DECISION MAKING/UNDOING --------------------

    fn make_decision(&mut self, lit: Lit, reason_clause_index: u32) {
        let var = lit_var!(lit);
        self.dec_map[var] = Decision {
            lit,
            dec_level: self.dec_level,
            dec_trail_index: self.num_decisions,
            reason_clause_index,
        };
        self.dec_trail[self.num_decisions as usize] = lit;
        self.num_decisions += 1;

        // LRB statistic update (new direct assignment, not used in reason/conflict yet)
        self.lrb.var_stats[var].assigned = self.lrb.learnt_counter;
        self.lrb.var_stats[var].participated_or_reasoned = 0;
    }

    fn undo_decision(&mut self) {
        if self.num_decisions <= 0 { return };
        self.num_decisions -= 1;
        let var = lit_var!(self.dec_trail[self.num_decisions as usize]);
        self.dec_map[var] = INVALID_DECISION;

        // LRB statistic update
        let var_stat = &mut self.lrb.var_stats[var];
        let interval = self.lrb.learnt_counter - var_stat.assigned;
        if interval <= 0 { return };
        var_stat.value = ((1.0 - self.lrb.alpha) * var_stat.value) +
                         (self.lrb.alpha * (var_stat.participated_or_reasoned as f64) / (interval as f64));
    }

    fn make_heuristic_decision(&mut self) {
        // Assign true/false value at random for initial decision
        let mut var_decided = 0usize;
        
        // Branching based on LRB statistics
        for i in 1..self.num_vars as usize + 1 {
            if self.dec_map[i].lit != INVALID_LIT { continue };

            // Decide on current literal if
            // 1) No variable is selected yet
            // 2) Current variable statistic is superior
            // 3) Current variable statistic is comparable (within 1e-6), random coin flip says use it instead
            // - Disable option 3 to eliminate randomness
            let var_stats = &self.lrb.var_stats;
            if var_decided == 0 ||
               var_stats[var_decided].value < var_stats[i].value ||
               ENABLE_RANDOM && var_stats[var_decided].value - var_stats[i].value <= 1e-6 && rand::random::<bool>() {
                var_decided = i;
            }
        }

        // Make a decision (true/false) at random at new decision level
        self.dec_level += 1;
        self.make_decision(
            lit_make!(var_decided, ternary!(ENABLE_RANDOM, rand::random::<bool>(), false)),
            INVALID_CLAUSE_INDEX
        );
    }

    // -------------------- RESTART MECHANISM(S) --------------------

    fn initialize_lrb_stats(&mut self) {
        let stats = &mut self.lrb;
        stats.alpha = LRB_ALPHA_INITIAL_VALUE;
        stats.learnt_counter = 0;
        stats.var_stats = vec![LrbVarStats { value: 0.0, assigned: 0, participated_or_reasoned: 0 };
                               self.num_vars as usize + 1];
    }

    fn includes(clause1: &Vec<Lit>, clause2: &Vec<Lit>) -> bool {
        // Check if the literals of clause2 are a subsequence of the literals of clause1
        // If so, then a model for clause1 /\ clause2 must be a model for clause1, so clause1 is subsumed by clause2
        // Both must already be sorted
        let mut last1 = 0usize;
        for lit in clause2 {
            if last1 >= clause1.len() { return false };
            let found = *lit == clause1[last1];
            last1 += 1;
            if found { continue };
        }

        true
    }

    fn clause_deletion(&mut self) {
        // Ignore deletion if there is nothing to delete
        if self.clauses.len() == self.num_given_clauses as usize { return };
        if DEBUG {
            print!("c Clause Deletion: {}", self.clauses.len());
        }

        // Note: Level-0 reason clauses may be modified as a result (i.e. not preserved)
        //       However, result remains correct (level-0 items will not be changed/removed).
        let mut back = self.clauses.len();
        let mut i = 0;
        'outer: while i < back {
            // Sort literals for subsequent "includes" comparison
            self.clauses[i].lits.sort();

            // Keep core clauses
            if i < self.num_core_clauses as usize { continue };

            // Only consider keeping any clause with LBD <= 4 (note: LBD = 2 is "glue" clause),
            // and any clause causing level-0 unit prop.
            if self.clauses[i].lbd > 4 {
                back -= 1;
                self.clauses.swap_remove(i);
                continue;
            }

            // Check if clause i can be subsumed by a clause to be kept. If so, don't need to keep
            for k in 0..i {
                if self.clauses[k].lits.len() > self.clauses[i].lits.len() { continue };
                if SatContext::includes(&self.clauses[i].lits, &self.clauses[k].lits) {
                    back -= 1;
                    self.clauses.swap_remove(i);
                    continue 'outer;
                }
            }

            // Keep the clause
            i += 1;
        }

        // Rebuild entire 2WL structure
        for wl in &mut self.two_wl {
            wl.clear();
        }

        for (i, clause) in self.clauses.iter().enumerate() {
            // Note: must restore original watch literals before rebuilding
            if clause.wl[0] != INVALID_LIT {
                self.two_wl[clause.wl[0] as usize].push(i as u32);
            }

            if clause.wl[1] != INVALID_LIT {
                self.two_wl[clause.wl[1] as usize].push(i as u32);
            }
        }

        // Update core clause count
        self.num_core_clauses = self.clauses.len() as u32;
        if DEBUG {
            println!(" -> {}", self.num_core_clauses);
        }
    }

    fn restart(&mut self) {
        // Undo all decisions except decision level 0
        while self.num_decisions > 0 && 
              self.dec_map[lit_var!(self.dec_trail[self.num_decisions as usize - 1])].dec_level != 0 {
            self.undo_decision();
        }

        // Start from decision level 0, no conflicts, no statistics
        self.dec_level = 0;
        self.conflicts_since_restart = 0;
        self.initialize_lrb_stats();
        
        // Reduce number of learnt
        self.clause_deletion();

        // Compute next Luby restart values
        if self.luby_restart.0 > self.luby_restart.1 {
            self.luby_restart.0 = 1;
            self.luby_restart.1 <<= 1;
        } else {
            self.luby_restart.0 <<= 1;
        }
    }

    // -------------------- CONFLICT RESOLUTION --------------------

    // Assumes that all literals have an associated decision when calling this function
    fn find_last_dec_index(&self, lits: &Vec<Lit>) -> (u32, u32) {
        let mut last_dec_index = self.dec_map[lit_var!(lits[0])].dec_trail_index;
        let mut second_last_dec_index = INVALID_DEC_INDEX;
        for i in 1..lits.len() {
            let dec_index = self.dec_map[lit_var!(lits[i])].dec_trail_index;
            if dec_index > last_dec_index {
                second_last_dec_index = last_dec_index;
                last_dec_index = dec_index;
            } else if dec_index > second_last_dec_index || second_last_dec_index == INVALID_DEC_INDEX {
                second_last_dec_index = dec_index;
            }
        }

        (second_last_dec_index, last_dec_index)
    }

    fn resolve_conflict(&mut self, unsat_clause_index: u32) {
        // Construct learnt clause (incl. placeholder values)
        // - LBD starts from 1 (representing current decision level)
        let mut learnt_clause = Box::new(Clause {
            last_sat_lit: INVALID_LIT,
            lits: vec![],
            wl: [INVALID_LIT, INVALID_LIT],
            lbd: 1,
        });
        
        // Found a conflict, get index to key decisions, undo
        self.conflicts_since_restart += 1;
        let last_dec_index;
        {
            // NB: Last decision cannot be our new clause
            let unsat_clause = &self.clauses[unsat_clause_index as usize];
            (_, last_dec_index) = self.find_last_dec_index(&unsat_clause.lits);
        }
        while last_dec_index + 1 < self.num_decisions {
            self.undo_decision();
        }

        // Track variables seen, decision levels seen
        let mut var_seen = vec![false; self.num_vars as usize + 1];
        let mut dec_level_seen = vec![false; self.num_vars as usize + 1];

        // Count for the number of unprocessed but seen variables from current decision level, uninitialized to 0
        let mut count = 0;

        // Process in reverse-chronological order of decisions
        let mut last_decision_var = lit_var!(self.dec_trail[self.num_decisions as usize - 1]);
        let last_dec_level = self.dec_map[last_decision_var].dec_level;
        dec_level_seen[last_dec_level as usize] = true;

        // Find 1UIP procedure (https://efforeffort.wordpress.com/2009/03/09/linear-time-first-uip-calculation/)
        // Start from UNSAT clause
        let mut first_clause = true;
        loop {
            let reason_clause;
            if first_clause {
                reason_clause = &self.clauses[unsat_clause_index as usize];
            } else {
                let reason_clause_index = self.dec_map[last_decision_var].reason_clause_index;

                // Reached a decision made by heuristics alone, no more reasoning, stop
                if reason_clause_index == INVALID_CLAUSE_INDEX {
                    break;
                } 
                reason_clause = &self.clauses[reason_clause_index as usize];
            }

            // Process literals of reason_clause
            for lit in &reason_clause.lits {
                // For each literal causing the unit propagation to last_decision
                let reason_clause_var = lit_var!(lit);

                // Ignore seen literals
                if var_seen[reason_clause_var] {
                    continue;
                }
                var_seen[reason_clause_var] = true;

                // If reason literal is from current decision level, increment count (seen but unprocessed)
                // Note: reason clause should not have any literals whose variables are undecided
                let reason_clause_lit_decision = &self.dec_map[reason_clause_var];
                if reason_clause_lit_decision.dec_level == last_dec_level {
                    count += 1;
                    continue;
                }

                // Otherwise it is part of learnt clause (from another decision level) - NEGATE IT!
                learnt_clause.lits.push(lit_neg!(reason_clause_lit_decision.lit));

                // Update LBD statistic for learnt clause
                let reason_dec_level = reason_clause_lit_decision.dec_level as usize;
                if reason_clause_lit_decision.lit != INVALID_LIT &&
                !dec_level_seen[reason_dec_level] {
                    dec_level_seen[reason_dec_level] = true;
                    learnt_clause.lbd += 1;
                }
            }

            loop {
                if first_clause {
                    break;
                }

                // Undo decision
                self.undo_decision();

                // Look for next candidate for 1UIP
                last_decision_var = lit_var!(self.dec_trail[self.num_decisions as usize - 1]);

                if var_seen[last_decision_var] {
                    break;
                }
            }

            first_clause = false;
            count -= 1;

            if count <= 0 {
                break;
            }
        }

        // Clauses minimization for anything that is not 1UIP
        // NB: I assume you don't need learnt_clause itself to be in the clause list (avoids borrow issues)
        self.minimize_learnt_clause(&mut learnt_clause.lits);

        // Add 1UIP to learnt clause (negation of decision), set it as watch literal of learnt clause
        let one_uip_lit = lit_neg!(self.dec_map[last_decision_var].lit);
        learnt_clause.lits.push(one_uip_lit);
        self.two_wl[one_uip_lit as usize].push(self.clauses.len() as u32);  // index of learnt clause (not pushed yet)
        learnt_clause.wl[0] = one_uip_lit;

        // Idea: Locate second-last decision for potential backtracking to
        let (second_last_dec_index, _) = self.find_last_dec_index(&learnt_clause.lits);

        // For backtracking to unit clause, backtrack to decision level 0, then add unit clause
        if second_last_dec_index == INVALID_DEC_INDEX {
            // Backtrack to last unit clause (if any) at decision level 0
            self.dec_level = 0;
            while self.num_decisions != 0 &&
                  self.dec_map[lit_var!(self.dec_trail[self.num_decisions as usize - 1])].dec_level != 0 {
                self.undo_decision();
            }

            // Previously assigned unit clause for same variable but different truth values = UNSAT
            let dec = &self.dec_map[lit_var!(learnt_clause.lits[0])];
            self.is_sat = dec.lit == INVALID_LIT || dec.lit == learnt_clause.lits[0];

            // Make the decision for this unit clause for displaying UNSAT if need be
            self.make_decision(learnt_clause.lits[0], INVALID_CLAUSE_INDEX);

            // Progress tracking purposes (esp. UNSAT instances)
            self.num_generated_unit_clauses += 1;
            print!("c Unit clause (");
            SatContext::display_lit(learnt_clause.lits[0]);
            println!(") generated from conflict. Count: {}", self.num_generated_unit_clauses);
        } else {
            // Otherwise, for non-unit clauses, backtrack till second-last decision
            // (for subsequent unit propagation from there)
            // Undo all decisions until second-last decision in learnt clause
            while self.num_decisions > 0 &&
                  second_last_dec_index + 1 < self.num_decisions {
                self.undo_decision();
            }

            // Add learnt clause to 2WL for unit propagation
            let last_dec_lit_neg = lit_neg!(self.dec_trail[self.num_decisions as usize - 1]);
            self.two_wl[last_dec_lit_neg as usize].push(self.clauses.len() as u32); // index of learnt clause (not pushed yet)
            learnt_clause.wl[1] = last_dec_lit_neg;

            // In the end, allow for unit propagation from the right decision level
            self.dec_level = self.dec_map[lit_var!(self.dec_trail[self.num_decisions as usize - 1])].dec_level;
        }

        // Finally push learnt clause
        // NB: This was delayed to make borrow checking easier. As far as I can tell,
        // it is not an issue to delay it until the end.
        self.clauses.push(learnt_clause);
    }

    fn after_conflict_analysis(&mut self, unsat_clause_index: u32) {
        let unsat_clause = &self.clauses[unsat_clause_index as usize];
        let learnt_clause = self.clauses.last().unwrap();

        // LRB statistic update
        // Learnt a clause
        self.lrb.learnt_counter += 1;

        // Eery literal in learnt clause and UNSAT clause participated
        let mut seen = vec![false; self.num_vars as usize];

        // Update literals that participated in conflict
        for lit in unsat_clause.lits.iter().chain(unsat_clause.lits.iter()) {
            let var = lit_var!(lit);
            if seen[var] {
                continue;
            }
            seen[var] = true;
            self.lrb.var_stats[var].participated_or_reasoned += 1;
        }

        // Slow down rate of learning
        if self.lrb.alpha > LRB_ALPHA_MIN {
            self.lrb.alpha -= LRB_ALPHA_DECAY;
        }

        // RSR extension (less "need" to apply on unit clauses learnt):
        for non_uip_lit in learnt_clause.lits.iter().take(learnt_clause.lits.len() - 1) {
            let var = lit_var!(non_uip_lit);
            self.lrb.var_stats[var].participated_or_reasoned += 1;
            if self.dec_map[var].lit == INVALID_LIT ||
               self.dec_map[var].reason_clause_index == INVALID_CLAUSE_INDEX {
                continue;
            }
            
            // Found a reason clause for the learnt clause literals, include in computation
            let reason_clause = &self.clauses[self.dec_map[var].reason_clause_index as usize];
            for lit in &reason_clause.lits {
                self.lrb.var_stats[lit_var!(lit)].participated_or_reasoned += 1;
            }
        }

        // Locality extension: For every unassigned variable, decay the LRB statistic value
        for i in 1..(self.num_vars as usize + 1) {
            if self.dec_map[i].lit != INVALID_LIT {
                continue;
            }
            self.lrb.var_stats[i].value *= LRB_DECAY_RATE;
        }
    }

    // -------------------- UNIT PROPAGATION --------------------

    // Note: Bottleneck method
    fn check_clause(&mut self, clause_index: usize) -> ClauseStatus {
        let mut clause = &mut self.clauses[clause_index];

        // If clause was previously satisfied by something that is still "decided", no need process
        if clause.last_sat_lit != INVALID_LIT &&
           self.dec_map[lit_var!(clause.last_sat_lit)].lit == clause.last_sat_lit {
            return ClauseStatus::Satisfied;
        }
        clause.last_sat_lit = INVALID_LIT;

        // Note: Search for some unassigned variable (for unit prop. and watch) at the same time
        self.temp_lit = INVALID_LIT;
        for &clause_lit in &clause.lits {
            let dec = &self.dec_map[lit_var!(clause_lit)];
            
            // variable is assigned -> (1) assigned true and not negated, (2) assigned false and negated
            if dec.lit == clause_lit {
                clause.last_sat_lit = clause_lit;
                return ClauseStatus::Satisfied;
            }

            // Unassigned variable remaining, check if it can become a new watch literal (i.e. not currently one)
            if dec.lit == INVALID_LIT {
                self.temp_lit = clause_lit;
                // Optimization: more than 1 unassigned literal = unknown/SAT -> stop checking immediately + mark new WL
                if clause.wl[0] != clause_lit && clause.wl[1] != clause_lit {
                    return ClauseStatus::Unknown;
                }
            }
        }

        if self.temp_lit != INVALID_LIT {
            return ClauseStatus::UnknownUnit;
        }

        return ClauseStatus::Unsatisfied;
    }

    // Note: Bottleneck method
    fn do_unit_propagation(&mut self) -> u32 {
        // No decisions = nothing to propagate
        if self.num_decisions == 0 {
            return INVALID_CLAUSE_INDEX;
        }

        // Propagate from last decision made
        let mut queue_start = self.num_decisions - 1; // Note: queue_end = self.num_decisions
        while queue_start < self.num_decisions {
            // Obtain negation of literal for unit propagation (was set to false)
            let up_lit_neg = lit_neg!(self.dec_trail[queue_start as usize]);
            queue_start += 1;

            // Use 2WL (2 Watched Literal) structure to locate relevant clauses
            // Look for clauses where literal became "false"
            let mut back = self.two_wl[up_lit_neg as usize].len();
            let mut i = 0;
            while i < back {
                // Process current clause
                let clause_index = self.two_wl[up_lit_neg as usize][i];
                match self.check_clause(clause_index as usize) {
                    ClauseStatus::Unsatisfied => {
                        // No longer satisfied, we have found conflict - stop unit propagation
                        return clause_index;
                    },
                    ClauseStatus::Satisfied => {
                        // Clause satisfied, look for next clause
                        i += 1;
                    },
                    ClauseStatus::UnknownUnit => {
                        // Unit propagate normally (make the new decision)
                        self.make_decision(self.temp_lit, clause_index);
                        i += 1;
                    },
                    ClauseStatus::Unknown => {
                        // Otherwise, use another unassigned literal in clause as new WL, if available
                        if self.temp_lit == INVALID_LIT {
                            i += 1;
                        } else {
                            // Move another clause index to current position instead
                            back -= 1;
                            self.two_wl[up_lit_neg as usize].swap_remove(i);

                            // Found new WL to use, add clause to new WL's watchlist instead
                            self.two_wl[self.temp_lit as usize].push(clause_index);
                            let clause = &mut self.clauses[clause_index as usize];
                            if clause.wl[0] == up_lit_neg {
                                clause.wl[0] = self.temp_lit;
                            }
                            if clause.wl[1] == up_lit_neg {
                                clause.wl[1] = self.temp_lit;
                            }
                        }
                    }
                }
            }
        }

        // No UNSAT clauses
        return INVALID_CLAUSE_INDEX;
    }

    // -------------------- PRE-PROCESSING --------------------

    fn preprocess_clauses(&mut self) {
        // Store potential pure literals (only positive or negation of variable exists)
        let mut positive = vec![false; self.num_vars as usize + 1];
        let mut negative = vec![false; self.num_vars as usize + 1];

        // Look for unit clauses
        for i in 0..self.clauses.len() {
            // If it is a unit clause
            if self.clauses[i].lits.len() == 1 {
                let lit = self.clauses[i].lits[0];
                let dec = &self.dec_map[lit_var!(lit)];
                
                // If different true/false values assigned for soem variable, UNSAT
                self.is_sat = dec.lit == INVALID_LIT || dec.lit == lit;
                self.make_decision(lit, INVALID_CLAUSE_INDEX);
                print!("c Identified unit clause: (");
                SatContext::display_lit(lit);
                println!(")");
            }

            // Track sign of each literal in the clause
            for lit in &self.clauses[i].lits {
                if lit_sign!(lit) {
                    positive[lit_var!(lit)] = true;
                } else {
                    negative[lit_var!(lit)] = true;
                }
            }
        }

        // Look for pure literals
        for i in 1..(self.num_vars as usize + 1) {
            if positive[i] == negative[i] {
                continue;
            }

            // Found a pure literal, attempt to assign a value not already done (e.g. by unit clause)
            println!("c Identified pure literal: {}{}", ternary!(positive[i], "", "-"), i);
            if self.dec_map[i].lit == INVALID_LIT {
                self.make_decision(lit_make!(i, positive[i]), INVALID_CLAUSE_INDEX);
            } else if lit_sign!(self.dec_map[i].lit) != positive[i] {
                // Pure literal conflicts with previous unit clause decision, UNSAT
                self.is_sat = false;
            }
        }

        // If any clause is UNSAT at this point, formula is UNSAT (pure literals and unit clauses used only)
        for i in 0..self.num_given_clauses {
            if !self.is_sat || self.check_clause(i as usize) == ClauseStatus::Unsatisfied {
                self.is_sat = false;
                break;
            }
        }
    }

    // -------------------- SAT SOLVER MAIN LOGIC --------------------

    fn solve(&mut self) {
        // Restart on clean slate before starting to solve
        self.restart();

        // Pre-process clauses
        self.preprocess_clauses();

        // Begin CDCL algorithm
        while self.is_sat {
            // Perform unit propagation
            let unsat_clause_index = self.do_unit_propagation();

            // Conflict found, process it
            if unsat_clause_index != INVALID_CLAUSE_INDEX {
                // Conflict at decision level 0 = conflict with unit clause = UNSAT
                if self.dec_level == 0 {
                    self.is_sat = false;
                }
                self.resolve_conflict(unsat_clause_index);
                if !self.is_sat {
                    break;
                }
                self.after_conflict_analysis(unsat_clause_index);

                // Restart if require (e.g. 256 * LubyRestart Multiplier)
                if self.conflicts_since_restart > self.luby_restart.0 << 6 {
                    self.restart();
                }
            } else if self.num_decisions < self.num_vars {
                // No conflict found, attempt to assign a new variable
                self.make_heuristic_decision();
            } else {
                // Done
                break;
            }
        }

        // Double check for errors against only original clauses (esp. if solution is SAT)
        for i in 0..self.num_given_clauses {
            if !self.is_sat {
                return;
            }

            if self.check_clause(i as usize) != ClauseStatus::Satisfied {
                println!("c [!] SAT Solver Error: Found solution does not satisfy all given clauses.");
                return;
            }
        }

        // No errors, write solution DIMACS output format
        self.display_model();
    }

}

fn main() { 
    let args: Vec<String> = std::env::args().collect();

    // Read from file (DIMACS CNF format)
    let mut ctx = SatContext {
        num_generated_unit_clauses: 0,
        is_sat: false,
        num_vars: 0,
        num_decisions: 0,
        lit_array_size: 0,
        num_given_clauses: 0,
        num_core_clauses: 0,
        dec_level: 0,
        conflicts_since_restart: 0,
        luby_restart: (0, 0),
        dec_map: vec![],
        dec_trail: vec![],
        clauses: vec![],
        two_wl: vec![],
        lrb: LrbStats {
            alpha: 0.0,
            learnt_counter: 0,
            var_stats: vec![],
        },
        temp_lit: INVALID_LIT,
    };

    if args.len() < 2 {
        println!("[-] Insufficient arguments.");
        process::exit(1);
    }

    if let Err(e) = ctx.read_dimacs(Path::new(&args[1])) {
        println!("Failed to load problem: {}", e);
        process::exit(1);
    }
    ctx.solve();
}