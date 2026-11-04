#pragma once

#include "cstring"
#include "math.h"
#include "solver_types.h"
#include "utils.hpp"
#include <algorithm>
#include <assert.h>
#include <iomanip>
#include <unordered_map>

namespace minicore {

// MLQP dependency bitset: bit i refers to the caller's core_assumps[i].
using MLQPSupportMask = uint64_t;
using MLQPSupportSet = std::vector<MLQPSupportMask>;

struct MLQPSupportLookup {
    // Borrowed words; valid until entry/pool growth, a support update, or a new call.
    const MLQPSupportMask *bits = nullptr;
    size_t size = 0;
};

inline std::string vec2str(const std::vector<Lit> &lits) {
    std::string res;
    for (Lit l : lits) {
        res += std::to_string(toInt(l)) + " ";
    }
    return res;
}

class Solver {
  public:
    enum class SolverState {
        Ready,
        Solved,
    };

    // Constructor/Destructor:
    //
    Solver();
    ~Solver();

    // Problem specification:
    //
    Var newVar(); // Add a new variable with parameters specifying variable mode.
    void newVarUntil(Var v);

    bool addClause(const std::vector<Lit> &ps); // Add a clause to the solver.
    bool addClause_(std::vector<Lit> &ps);      // Add a clause to the solver without making superflous internal copy. Will change the passed vector 'ps'.

    bool addTempClause(const std::vector<Lit> &ps); // Add a temp clause that effects solves until release.
    void releaseTempClause();                       // Release all active temp clauses and their derived learnts.
    bool solve_in_domain;                           // Deciside in domain.
    void setSolveInDomain(bool in_domain);          // Set decide in domain.

    // Incremental modelchecking decision domain:
    //
    bool inDomain(Var x) const;
    std::vector<char> &domainSet();
    std::vector<Var> &domainList();

    // Solving:
    //
    void simplify();                              // Simplify clauses.
    lbool solve(const std::vector<Lit> &assumps); // Search for a model that respects a given set of assumptions.
    lbool solve();                                // Search without assumptions.
    bool okay() const;                            // FALSE means solver is in a conflicting state
    void reset();                                 // Reset solver to ready state after a solve.
    SolverState state() const { return state_; }
    lbool lastResult() const { return last_result_; }
    bool failed(Lit assumption) const;

    void setRestartLimit(int limit); // Set the restart limit.

    std::vector<Lit> intVec2LitVec(const std::vector<int> &vec); // Convert a vector of integers to a vector of literals.

    // Reduce the caller's UNSAT core in its supplied order, without modifying it.
    // On success publish the result through failed(); otherwise keep the SAT core.
    // Strategy: 0 disabled, 1 Default, 2 Extended.
    // Call while the last UNSAT query and temporary clauses remain intact.
    // IC3 may first narrow the temporary domain to the validated core's COI.
    // Cores below size 3 retain the trivial-core fast return. Otherwise preserve
    // input order and reduce from scratch; no cross-query support cache.
    bool mlqp(const std::vector<Lit> &core_assumps, int strategy);
    // Bypass deletions in the last MLQP call.
    size_t mlqpBypassReducedLiterals() const { return mlqp_bypass_reduced_literals; }

    // Read state:
    //
    lbool value(Var x) const;   // The current value of a variable.
    lbool value(Lit p) const;   // The current value of a literal.
    size_t nAssigns() const;    // The current number of assigned literals.
    int nClauses() const;       // The current number of original clauses.
    int nLearnts() const;       // The current number of learnt clauses.
    int nVars() const;          // The current number of variables.
    void printStats() const;    // Print some current statistics to standard output.
    void printResult() const;   // Print sat result.
    void printModel() const;    // Print model in DIMACS style.
    void printHead() const;     // Print head.
    void printProgress() const; // Print progress.

    // Memory managment:
    //
    virtual void garbageCollect();
    void checkGarbage();

    // Mode of operation:
    //
    int verbosity;
    double random_seed;
    double clause_decay;

    int restart_first;        // The initial restart limit.                                                                (default 100)
    double restart_inc;       // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double learntsize_factor; // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double learntsize_inc;    // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

    int learntsize_adjust_start_confl;
    double learntsize_adjust_inc;

    // Statistics: (read-only member variable)
    //
    uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
    uint64_t dec_vars, num_clauses, num_learnts, clauses_literals, learnts_literals, max_literals, tot_literals;

  protected:
    static constexpr uint8_t assign_True = 0;
    static constexpr uint8_t assign_False = 1;
    static constexpr uint8_t assign_Undef = 2;

    bool is_value_true(Lit p) const noexcept;
    bool is_value_false(Lit p) const noexcept;

    std::shared_ptr<ClauseAllocator> ca;

    // Solver state:
    //
    std::vector<CRef> clauses;      // List of problem clauses.
    std::vector<CRef> learnts;      // List of learnt clauses.
    std::vector<CRef> temp_clauses; // List of clauses learnt from the temp clause.
    std::vector<Lit> trail;         // Assignment stack; stores all assigments made in the order they were made.
    std::vector<size_t> trail_lim;  // Separator indices for different decision levels in 'trail'.
    std::vector<Lit> assumptions;   // Current set of assumptions provided to solve by the user.

    std::vector<uint8_t> assigns; // The current assignments.
    std::vector<char> polarity;   // The preferred polarity of each variable.
    std::vector<VarData> vardata; // Stores reason and level for each variable.
    OccLists watches;             // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).

    bool solve_in_domain_runtime_flag; // Decide in domain in runtime.
    std::vector<char> domain_set;
    std::vector<Var> domain_list;

    int restart_limit; // The restart limit.

    DecisionBuckets order_list; // A priority queue of variables ordered with respect to the variable activity.

    // VarOrderLt var_order_lt; // Compare function for var on activity order
    reduceDB_lt reduce_db_lt;

    bool ok;                       // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    double cla_inc;                // Amount to bump next clause with.
    size_t qhead;                  // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    size_t simpDB_assigns;         // Number of top-level assignments since last execution of 'simplify()'.
    int64_t simpDB_props;          // Remaining number of propagations that must be made before next execution of 'simplify()'.
    double progress_estimate;      // Set by 'search()'.
    Var next_var;                  // Next variable to be created.
    Var alloced_var;               // Variable with structure created.
    Var temp_cls_act_var;          // Variable to activate temp clause.
    bool temp_cls_activated;       // A temp clause is added.
    bool temp_cls_release_pending; // Active temp clauses should be released on the next reset.
    size_t traillim_snapshot;      // Snapshot of trail_lim before temp clause/solve in domain is activated.
    int64_t simpDB_called;         // Number of times 'solve()' has been called.
    int64_t simpDB_clauses;        // Number of clauses at last 'simplify()' call.
    SolverState state_;
    lbool last_result_;

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    std::vector<char> seen;
    std::vector<Lit> analyze_toclear;
    std::vector<ShrinkStackElem> analyze_stack;
    std::vector<Lit> learnt_clause_tmp;
    std::vector<uint32_t> failed_stamp;
    // Unique failed user assumptions, excluding the temporary-clause activator.
    std::vector<Lit> failed_core;
    bool has_failed{false};
    uint32_t failed_epoch{1};

    int m_mlqpStrategy;    // Strategy for the current reduction.
    size_t mlqp_core_size; // Input core size.
    size_t mlqp_best_size; // Smallest support size found.
    size_t mlqp_support_chunks;

    MLQPSupportSet mlqp_zero_support;     // Reusable all-zero support bitset.
    MLQPSupportSet mlqp_best_core;        // Bitset for the best core found so far.
    MLQPSupportSet mlqp_work_support;     // Scratch support bitset for construction/DFS.
    MLQPSupportSet mlqp_merged_support;   // Scratch buffer for OR-merging supports in one clause.
    MLQPSupportSet mlqp_conflict_support; // Scratch buffer used when testing literal/opposite-literal conflicts.

    // MLQP borrows seen's polarity/presence bits and failed_stamp's literal slots as
    // a temporary index. Restore both before returning to SAT or publishing a core.
    struct MLQPEntry {
        Lit literal;
        uint32_t saved_failed_stamp;
        union {
            size_t support_offset = 0;
            MLQPSupportMask inline_support;
        };
        size_t support_size = size_t(-1);
        size_t assumption = size_t(-1);
        uint32_t pending_head = UINT32_MAX;
    };
    struct MLQPPendingEntry {
        uint32_t clause_index;
        uint32_t next;
    };
    struct MLQPPendingClause {
        CRef clause;
        Lit first;
        Lit second;
        uint32_t cursor = 0;
    };
    static_assert(sizeof(MLQPPendingEntry) == 8, "Pending links must stay compact");
    static_assert(sizeof(MLQPPendingClause) == 16, "Pending clause cache must stay compact");
    std::vector<MLQPEntry> mlqp_entries;
    std::vector<MLQPPendingEntry> mlqp_pending_entries;
    std::vector<MLQPPendingClause> mlqp_pending_clauses;
    uint32_t mlqp_pending_seen_epoch{0};
    // Current-call supports and pending lists share contiguous reusable storage.
    MLQPSupportSet mlqp_support_pool;
    std::vector<std::vector<Lit>> mlqp_buckets;
    std::vector<size_t> mlqp_bucket_heads;
    std::vector<uint32_t> mlqp_pending_seen_indices;
    std::vector<uint32_t> mlqp_pending_seen_stamps;
    std::vector<CRef> mlqp_propagate_clauses;
    std::vector<Lit> mlqp_unresolved_clause_tmp;

    // Concatenated fixed-width supports per assumption; reuse capacity across calls
    // rather than allocating a separate vector for every bypass rule.
    std::vector<MLQPSupportSet> mlqp_bypass_rules;
    std::vector<size_t> mlqp_bypass_targets;
    MLQPSupportSet mlqp_bypass_available;
    size_t mlqp_bypass_reduced_literals{0};

    double max_learnts;
    double learntsize_adjust_confl;
    int learntsize_adjust_cnt;

    // Main internal methods:
    //
    void insertVarOrder(Var x); // Insert a variable in the decision order priority queue.
    Lit pickBranchLit();        // Return the next decision variable.
    void newDecisionLevel();    // Begins a new decision level.
    void uncheckedEnqueue(Lit p,
                          CRef from = CRef_Undef); // Enqueue a literal. Assumes value of literal is undefined.
    CRef propagate();                              // Perform unit propagation. Returns possibly conflicting clause.
    CRef propagate_full();                         // Perform *full* unit propagation.
    CRef propagate_domain();                       // Perform unit propagation *in domain*.
    void cancelUntil(size_t level);                // Backtrack until a certain level.
    void analyze(CRef confl,
                 std::vector<Lit> &out_learnt,
                 size_t &out_btlevel); // (bt = backtrack)
    void clearFailed();
    void markFailed(Lit assumption);
    void analyzeFinal(Lit p);
    bool litRedundant(Lit p);                    // (helper method for 'analyze()')
    lbool search(int nof_conflicts);             // Search for a given number of conflicts.
    lbool solve_();                              // Main solve method (assumptions given in 'assumptions').
    void reduceDB();                             // Reduce the set of learnt clauses.
    void removeSatisfied(std::vector<CRef> &cs); // Shrink 'cs' to contain only non-satisfied clauses.
    void removeSubsumed(std::vector<CRef> &cs);  // Remove subsumed clauses from 'cs'.
    void removeTempLearnt();                     // Remove the clauses learnt from the temp clause.

    bool reduceMLQPCore(const std::vector<Lit> &core_assumps); // Query and strategy already checked.
    void initMLQPState(size_t core_size);
    const MLQPEntry *findMLQPEntry(Lit p) const;
    MLQPEntry &ensureMLQPEntry(Lit p);
    void restoreMLQPState();
    MLQPSupportLookup lookupMLQPSupport(Lit p) const;
    void updateMLQPSupport(Lit p, const MLQPSupportSet &cand_support, size_t cand_size);
    void reduceMLQPBypassCore();
    void updateMLQPBestCore(const MLQPSupportSet &support);
    void updateMLQPBestCore(const MLQPSupportSet &support, size_t support_size);
    void addMLQPPendingClause(Lit p, uint32_t clause_index);
    void reserveMLQPPendingSeen(size_t min_entries);
    uint32_t findMLQPPendingClause(CRef cr) const;
    bool markMLQPPendingClause(CRef cr);
    bool mlqpPendingBlocked(uint32_t index);
    void mlqpScanClause(CRef cr);
    template <bool SingleWord> void mlqpScanClauseImpl(CRef cr);
    void mlqpPropagate(Lit p);

    // Maintaining Variable/Clause activity:
    //
    void varBumpActivity(Var v, uint64_t conflict_index); // Increase a variable with ACIDS update.
    void claDecayActivity();                              // Decay all clauses with the specified factor.
    void claBumpActivity(Clause &c);                      // Increase a clause with the current 'bump' value.

    // Operations on clauses:
    //
    void attachClause(CRef cr);                            // Attach a clause to watcher lists.
    void detachClause(CRef cr);                            // Detach a clause to watcher lists.
    void removeClause(CRef cr);                            // Detach and free a clause.
    bool isRemoved(CRef cr) const;                         // Test if a clause has been removed.
    bool locked(const Clause &c) const;                    // Returns TRUE if a clause is a reason for some implication in the current state.
    bool satisfied(const Clause &c) const;                 // Returns TRUE if a clause is satisfied in the current state.
    bool deducedByTemp(const std::vector<Lit> &cls) const; // If a clause is deduced by the temp clause.

    // Misc:
    //
    size_t decisionLevel() const; // Gives the current decisionlevel.
    CRef reason(Var x) const;
    size_t level(Var x) const;
    double progressEstimate() const;
    void relocAll(std::shared_ptr<ClauseAllocator> new_ca);

    // Restart Limit:
    bool restartInLimit(int current_restarts) const;

    // Static helpers:
    //

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double &seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647;
    }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double &seed, int size) {
        return (int)(drand(seed) * size);
    }
};


//=================================================================================================
// Implementation of inline methods:

inline CRef Solver::reason(Var x) const { return vardata[x].reason; }
inline size_t Solver::level(Var x) const { return vardata[x].level; }

inline void Solver::insertVarOrder(Var v) {
    order_list.insert(v);
}

inline void Solver::varBumpActivity(Var v, uint64_t conflict_index) {
    order_list.update(v, conflict_index);
}

inline void Solver::claDecayActivity() {
    cla_inc *= (1.0 / clause_decay);
}

inline void Solver::claBumpActivity(Clause &c) {
    if ((c.activity() += cla_inc) > 1e20) {
        // Rescale:
        for (size_t i = 0; i < learnts.size(); i++)
            ca->get_clause(learnts[i]).activity() *= 1e-20;
        cla_inc *= 1e-20;
    }
}

inline void Solver::checkGarbage(void) {
    if (3 * ca->wasted_memory() > ca->allocated_memory())
        garbageCollect();
}

inline bool Solver::addClause(const std::vector<Lit> &cls) {
    std::vector<Lit> add_tmp = cls;
    return addClause_(add_tmp);
}

inline bool Solver::isRemoved(CRef cr) const { return ca->get_clause(cr).get_mark() == 1; }
inline bool Solver::locked(const Clause &c) const { return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && reason(var(c[0])) == ca->get_ref(c); }
inline void Solver::newDecisionLevel() { trail_lim.emplace_back(trail.size()); }

inline size_t Solver::decisionLevel() const { return trail_lim.size(); }

inline void Solver::uncheckedEnqueue(Lit p, CRef from) {
    assert((assigns[p.x >> 1] ^ (p.x & 1)) & assign_Undef);
    assigns[var(p)] = sign(p) ? assign_False : assign_True;
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.emplace_back(p);
}


inline lbool Solver::value(Var x) const { return toLbool(assigns[x]); }
inline lbool Solver::value(Lit p) const {
    return toLbool(static_cast<uint8_t>(assigns[p.x >> 1] ^ (p.x & 1)));
}
inline bool Solver::is_value_true(Lit p) const noexcept {
    return (assigns[p.x >> 1] ^ (p.x & 1)) == assign_True;
}
inline bool Solver::is_value_false(Lit p) const noexcept {
    return (assigns[p.x >> 1] ^ (p.x & 1)) == assign_False;
}

inline size_t Solver::nAssigns() const { return trail.size(); }
inline int Solver::nClauses() const { return num_clauses; }
inline int Solver::nLearnts() const { return num_learnts; }
inline int Solver::nVars() const { return next_var; }

inline bool Solver::failed(Lit assumption) const {
    const size_t index = static_cast<size_t>(toInt(assumption));
    assert(index < failed_stamp.size());
    return failed_stamp[index] == failed_epoch;
}

inline CRef Solver::propagate() {
    if (decisionLevel() == 0)
        return propagate_full();
    else
        return propagate_domain();
}

inline lbool Solver::solve() {
    if (state_ != SolverState::Ready) reset();
    assumptions.clear();
    if (temp_cls_activated) {
        assumptions.emplace_back(mkLit(temp_cls_act_var));
    }
    return solve_();
}

inline lbool Solver::solve(const std::vector<Lit> &assumps) {
    if (state_ != SolverState::Ready) reset();
    if (temp_cls_activated) {
        assumptions.clear();
        assumptions.emplace_back(mkLit(temp_cls_act_var));
        assumptions.resize(assumps.size() + 1);
        std::copy(assumps.begin(), assumps.end(), assumptions.begin() + 1);
    } else
        assumptions = assumps;
    return solve_();
}

inline void Solver::setRestartLimit(int limit) { restart_limit = limit; }

inline bool Solver::okay() const { return ok; }

inline void Solver::setSolveInDomain(bool in_domain) { solve_in_domain = in_domain; }

inline bool Solver::inDomain(Var x) const { return !solve_in_domain_runtime_flag || domain_set[x]; }

inline std::vector<char> &Solver::domainSet() { return domain_set; }

inline std::vector<Var> &Solver::domainList() { return domain_list; }

inline bool Solver::restartInLimit(int current_restarts) const { return restart_limit == -1 || current_restarts < restart_limit; }

inline std::vector<Lit> Solver::intVec2LitVec(const std::vector<int> &vec) {
    std::vector<Lit> res;
    res.reserve(vec.size());
    for (int l : vec) {
        Var v = abs(l);
        newVarUntil(v);
        res.push_back(mkLit(v, l < 0));
    }
    return res;
}

} // namespace minicore
