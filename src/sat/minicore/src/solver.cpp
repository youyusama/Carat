#include "solver.h"

namespace minicore {

Solver::Solver() : // Parameters (user settable):
                   //
                   verbosity(0),
                   random_seed(42), clause_decay(0.99), restart_first(100), restart_inc(2)

                   // Parameters (the rest):
                   //
                   ,
                   learntsize_factor((double)1 / (double)6), learntsize_inc(1.1)

                   // Parameters (experimental):
                   //
                   ,
                   learntsize_adjust_start_confl(100), learntsize_adjust_inc(1.5)


                   // Statistics: (formerly in 'SolverStats')
                   //
                   ,
                   solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), dec_vars(0), num_clauses(0), num_learnts(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

                   ,
                   ca(std::make_shared<ClauseAllocator>()),
                   watches(ca), order_list(), reduce_db_lt(ca),

                   solve_in_domain(false), solve_in_domain_runtime_flag(false), ok(true), cla_inc(1.0), qhead(0), simpDB_assigns(0), simpDB_props(0), simpDB_called(0), simpDB_clauses(0), progress_estimate(0), next_var(0), alloced_var(0), temp_cls_activated(false), temp_cls_release_pending(false), restart_limit(-1), state_(SolverState::Ready), last_result_(l_Undef), m_mlqpStrategy(0), mlqp_core_size(0), mlqp_best_size(0), mlqp_support_chunks(0) {

    temp_cls_act_var = newVar(); // let 0 be the temp clause activator
    domain_set[temp_cls_act_var] = 1;
    domain_list.push_back(temp_cls_act_var);
    analyze_stack.reserve(64);
    learnt_clause_tmp.reserve(32);
    analyze_toclear.reserve(64);
}

void Solver::reset() {
    assert(state_ == SolverState::Solved);

    // clean decisions
    if (decisionLevel() > 0) {
        while (trail.size() > trail_lim[0]) {
            Var x = var(trail.back());
            assigns[x] = assign_Undef;
            polarity[x] = sign(trail.back());
            trail.pop_back();
        }
        qhead = trail.size();
        trail_lim.resize(0);
    }

    // Keep temporary clauses across solves until releaseTempClause().
    if (temp_cls_activated) {
        // temp cls act var
        while (assigns[temp_cls_act_var] != assign_Undef) {
            Var x = var(trail.back());
            assigns[x] = assign_Undef;
            polarity[x] = sign(trail.back());
            trail.pop_back();
        }
        qhead = trail.size();
        trail_lim.resize(0);
    }
    assert(assigns[temp_cls_act_var] == assign_Undef);

    if (temp_cls_release_pending) {
        removeTempLearnt();
        temp_cls_activated = false;
        temp_cls_release_pending = false;
    }

    // solve in domain
    if (solve_in_domain) solve_in_domain_runtime_flag = false;

    assumptions.clear();
    clearFailed();
    last_result_ = l_Undef;
    state_ = SolverState::Ready;
}


bool Solver::mlqp(const std::vector<Lit> &core_assumps, int strategy) {
    mlqp_bypass_reduced_literals = 0;
    if (state_ != SolverState::Solved || last_result_ != l_False)
        return false;
    if (strategy <= 0 || strategy > 2)
        return false;
    if (core_assumps.size() < 3 || nVars() == 0)
        return false;

    m_mlqpStrategy = strategy;
    return reduceMLQPCore(core_assumps);
}


Solver::~Solver() {
}


Var Solver::newVar() {
    Var v = next_var;
    newVarUntil(v);
    return v;
}


void Solver::newVarUntil(Var v) {
    assert(v >= 0);
    if (v < next_var) return;

    Var old_next_var = next_var;
    next_var = v + 1;
    if (alloced_var < next_var) {
        while (alloced_var < next_var) alloced_var += 128;
        watches.ensure(alloced_var + alloced_var + 1);
        assigns.resize(alloced_var, assign_Undef);
        vardata.resize(alloced_var, mkVarData(CRef_Undef, 0));
        seen.resize(alloced_var, 0);
        failed_stamp.resize(static_cast<size_t>(2 * alloced_var), 0);
        polarity.resize(alloced_var, true);
        order_list.resize(alloced_var);
        trail.reserve(alloced_var);
        domain_set.resize(alloced_var, 0);
    }
    dec_vars += static_cast<uint64_t>(next_var - old_next_var);
    order_list.init_vars(old_next_var, next_var);
}

bool Solver::addClause_(std::vector<Lit> &ps) {
    if (state_ != SolverState::Ready) reset();
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps.begin(), ps.end());
    Lit p;
    size_t i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.resize(j);

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1) {
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    } else {
        CRef cr = ca->alloc(ps, false);
        clauses.emplace_back(cr);
        attachClause(cr);
    }

    return true;
}


bool Solver::addTempClause(const std::vector<Lit> &cls) {
    if (state_ != SolverState::Ready) reset();
    assert(decisionLevel() == 0);
    if (!ok) return false;
    temp_cls_activated = true;

    std::vector<Lit> temp_cls;
    temp_cls.emplace_back(mkLit(temp_cls_act_var, true));
    temp_cls.resize(cls.size() + 1);
    std::copy(cls.begin(), cls.end(), temp_cls.begin() + 1);
    // add temp
    CRef cr = ca->alloc(temp_cls, false);
    attachClause(cr);
    temp_clauses.emplace_back(cr);

    return true;
}


void Solver::releaseTempClause() {
    if (!temp_cls_activated) return;

    if (state_ == SolverState::Solved) {
        temp_cls_release_pending = true;
        return;
    }

    assert(state_ == SolverState::Ready);
    removeTempLearnt();
    temp_cls_activated = false;
    temp_cls_release_pending = false;
}


void Solver::attachClause(CRef cr) {
    const Clause &c = ca->get_clause(cr);
    assert(c.size() > 1);
    watches[~c[0]].emplace_back(Watcher(cr, c[1]));
    watches[~c[1]].emplace_back(Watcher(cr, c[0]));
    if (c.learnt())
        num_learnts++, learnts_literals += c.size();
    else
        num_clauses++, clauses_literals += c.size();
}


void Solver::detachClause(CRef cr) {
    const Clause &c = ca->get_clause(cr);
    assert(c.size() > 1);

    for (int w = 0; w < 2; w++) {
        Lit watch_lit = c[w];
        std::vector<Watcher> &ws = watches[~watch_lit];
        for (size_t i = 0; i < ws.size();) {
            if (ws[i].cref == cr) {
                ws[i] = ws.back();
                ws.pop_back();
                break;
            } else {
                i++;
            }
        }
    }

    if (c.learnt())
        num_learnts--, learnts_literals -= c.size();
    else
        num_clauses--, clauses_literals -= c.size();
}


void Solver::removeClause(CRef cr) {
    Clause &c = ca->get_clause(cr);
    detachClause(cr);
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.set_mark(1);
    ca->free(cr);
}


bool Solver::satisfied(const Clause &c) const {
    for (size_t i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false;
}


bool Solver::deducedByTemp(const std::vector<Lit> &cls) const {
    Lit neg_a = mkLit(temp_cls_act_var, true);
    for (Lit l : cls)
        if (l == neg_a)
            return true;
    return false;
}


void Solver::cancelUntil(size_t level) {
    if (decisionLevel() > level) {
        for (size_t c = trail.size(); c-- > trail_lim[level];) {
            Var x = var(trail[c]);
            assigns[x] = assign_Undef;
            polarity[x] = sign(trail[c]);
            if (inDomain(x) && !order_list.inBucket(x)) {
                insertVarOrder(x);
            }
        }
        qhead = trail_lim[level];
        trail.resize(trail_lim[level]);
        trail_lim.resize(level);
    }
}


Lit Solver::pickBranchLit() {
    Var next = var_Undef;

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !inDomain(next)) {
        if (order_list.empty()) {
            next = var_Undef;
            break;
        } else {
            next = order_list.get_deci_var();
        }
    }

    // Choose polarity based on different polarity modes (global or per-variable):
    if (next == var_Undef)
        return lit_Undef;
    return mkLit(next, polarity[next]);
}


void Solver::analyze(CRef confl, std::vector<Lit> &out_learnt, size_t &out_btlevel) {
    int pathC = 0;
    Lit p = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.resize(1);
    size_t index = trail.size();

    do {
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause &c = ca->get_clause(confl);

        if (c.learnt())
            claBumpActivity(c);

        for (size_t j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++) {
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0) {
                varBumpActivity(var(q), conflicts);
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel())
                    pathC++;
                else
                    out_learnt.emplace_back(q);
            }
        }

        // Select next clause to look at:
        while (!seen[var(trail[--index])]);
        p = trail[index];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    } while (pathC > 0);
    out_learnt[0] = ~p;
    analyze_toclear = out_learnt;

    // Simplify conflict clause:
    //
    size_t i, j;
    for (i = j = 1; i < out_learnt.size(); i++)
        if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i]))
            out_learnt[j++] = out_learnt[i];

    max_literals += out_learnt.size();
    out_learnt.resize(j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else {
        size_t max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (size_t i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1] = p;
        out_btlevel = level(var(p));
    }

    for (size_t j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0; // ('seen[]' is now cleared)
}


bool Solver::litRedundant(Lit p) {
    enum { seen_undef = 0,
           seen_source = 1,
           seen_removable = 2,
           seen_failed = 3 };
    assert(seen[var(p)] == seen_undef || seen[var(p)] == seen_source);
    assert(reason(var(p)) != CRef_Undef);

    Clause *c = &ca->get_clause(reason(var(p)));
    std::vector<ShrinkStackElem> &stack = analyze_stack;
    stack.clear();

    for (uint32_t i = 1;; i++) {
        if (i < (uint32_t)c->size()) {
            // Checking 'p'-parents 'l':
            Lit l = (*c)[i];

            // Variable at level 0 or previously removable:
            if (level(var(l)) == 0 ||
                seen[var(l)] == seen_source ||
                seen[var(l)] == seen_removable) {
                continue;
            }

            // Check variable can not be removed for some local reason:
            if (reason(var(l)) == CRef_Undef || seen[var(l)] == seen_failed) {
                stack.emplace_back(ShrinkStackElem(0, p));
                for (size_t i = 0; i < stack.size(); i++)
                    if (seen[var(stack[i].l)] == seen_undef) {
                        seen[var(stack[i].l)] = seen_failed;
                        analyze_toclear.emplace_back(stack[i].l);
                    }

                return false;
            }

            // Recursively check 'l':
            stack.emplace_back(ShrinkStackElem(i, p));
            i = 0;
            p = l;
            c = &ca->get_clause(reason(var(p)));
        } else {
            // Finished with current element 'p' and reason 'c':
            if (seen[var(p)] == seen_undef) {
                seen[var(p)] = seen_removable;
                analyze_toclear.emplace_back(p);
            }

            // Terminate with success if stack is empty:
            if (stack.size() == 0) break;

            // Continue with top element on stack:
            i = stack.back().i;
            p = stack.back().l;
            c = &ca->get_clause(reason(var(p)));

            stack.pop_back();
        }
    }

    return true;
}


void Solver::clearFailed() {
    failed_core.clear();
    has_failed = false;
    if (++failed_epoch == 0) {
        std::fill(failed_stamp.begin(), failed_stamp.end(), 0);
        failed_epoch = 1;
    }
}


void Solver::markFailed(Lit assumption) {
    const size_t index = static_cast<size_t>(toInt(assumption));
    assert(index < failed_stamp.size());
    has_failed = true;
    if (failed_stamp[index] == failed_epoch) return;
    failed_stamp[index] = failed_epoch;
    if (var(assumption) != temp_cls_act_var)
        failed_core.push_back(assumption);
}


void Solver::analyzeFinal(Lit p) {
    markFailed(~p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;
    // std::cout << "final conflict var: " << (!sign(p) ? var(p) : -var(p)) << std::endl;

    for (size_t i = trail.size(); i-- > trail_lim[0];) {
        Var x = var(trail[i]);
        if (seen[x]) {
            if (reason(x) == CRef_Undef) {
                assert(level(x) > 0);
                markFailed(trail[i]);
                // std::cout << "decision var: " << (!sign(trail[i]) ? var(trail[i]) : -var(trail[i])) << std::endl;
            } else {
                Clause &c = ca->get_clause(reason(x));
                // std::cout << "from clause: " << c.tostring() << std::endl;
                for (size_t j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


CRef Solver::propagate_full() {
    CRef confl = CRef_Undef;
    int num_props = 0;

    while (qhead < trail.size()) {
        Lit p = trail[qhead++]; // 'p' is enqueued fact to propagate.
        std::vector<Watcher> &ws = watches[p];
        Watcher *ws_data = ws.data();
        size_t ws_len = ws.size();
        size_t i = 0;
        num_props++;

        while (i < ws_len) {
            // Try to avoid inspecting the clause:
            Watcher w_cur = ws_data[i];
            Lit blocker = w_cur.blocker;
            if (is_value_true(blocker)) {
                i++;
                continue;
            }

            // Make sure the false literal is data[1]:
            CRef cr = w_cur.cref;
            Clause &c = ca->get_clause(cr);
            Lit false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
            if (first != blocker && is_value_true(first)) {
                ws_data[i].blocker = first;
                i++;
                continue;
            }

            // Look for new watch:
            for (size_t k = 2; k < c.size(); k++) {
                if (!is_value_false(c[k])) {
                    c[1] = c[k];
                    c[k] = false_lit;
                    watches[~c[1]].emplace_back(Watcher(cr, first));
                    ws_data[i] = ws_data[ws_len - 1];
                    ws_len--;
                    goto NextClause;
                }
            }

            // Did not find watch -- clause is unit under assignment:
            ws_data[i].blocker = first;
            if (is_value_false(first)) {
                confl = cr;
                qhead = trail.size();
                break;
            } else {
                uncheckedEnqueue(first, cr);
                i++;
            }

        NextClause:;
        }
        ws.resize(ws_len);
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


CRef Solver::propagate_domain() {
    CRef confl = CRef_Undef;
    int num_props = 0;

    while (qhead < trail.size()) {
        Lit p = trail[qhead++]; // 'p' is enqueued fact to propagate.
        std::vector<Watcher> &ws = watches[p];
        Watcher *ws_data = ws.data();
        size_t ws_len = ws.size();
        size_t i = 0;
        num_props++;

        while (i < ws_len) {
            // Try to avoid inspecting the clause:
            Watcher w_cur = ws_data[i];
            Lit blocker = w_cur.blocker;
            if (is_value_true(blocker) || !inDomain(var(blocker))) {
                i++;
                continue;
            }

            // Make sure the false literal is data[1]:
            CRef cr = w_cur.cref;
            Clause &c = ca->get_clause(cr);
            Lit false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
            if (first != blocker &&
                (is_value_true(first) || !inDomain(var(first)))) {
                ws_data[i].blocker = first;
                i++;
                continue;
            }

            // Look for new watch:
            for (size_t k = 2; k < c.size(); k++) {
                if (!is_value_false(c[k])) {
                    c[1] = c[k];
                    c[k] = false_lit;
                    watches[~c[1]].emplace_back(Watcher(cr, first));
                    ws_data[i] = ws_data[ws_len - 1];
                    ws_len--;
                    goto NextClause;
                }
            }

            // Did not find watch -- clause is unit under assignment:
            ws_data[i].blocker = first;
            if (is_value_false(first)) {
                confl = cr;
                qhead = trail.size();
                break;
            } else {
                uncheckedEnqueue(first, cr);
                i++;
            }

        NextClause:;
        }
        ws.resize(ws_len);
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


void Solver::reduceDB() {
    size_t i, j;

    std::sort(learnts.begin(), learnts.end(), [this](CRef x, CRef y) {
        return ca->get_clause(x).activity() > ca->get_clause(y).activity();
    });
    const size_t keep_limit = learnts.size() / 3;

    // Keep the highest-activity fraction. From the rest, delete non-locked long clauses.
    for (i = j = 0; i < learnts.size(); i++) {
        if (i > keep_limit) {
            Clause &c = ca->get_clause(learnts[i]);
            if (c.size() > 2 && !locked(c))
                removeClause(learnts[i]);
            else
                learnts[j++] = learnts[i];
        } else
            learnts[j++] = learnts[i];
    }
    learnts.resize(j);
    checkGarbage();
}


void Solver::removeSatisfied(std::vector<CRef> &cs) {
    size_t i, j;
    for (i = j = 0; i < cs.size(); i++) {
        Clause &c = ca->get_clause(cs[i]);
        if (satisfied(c))
            removeClause(cs[i]);
        else {
            // Trim clause:
            assert(value(c[0]) == l_Undef && value(c[1]) == l_Undef);
            for (size_t k = 2; k < c.size(); k++)
                if (value(c[k]) == l_False) {
                    c[k--] = c[c.size() - 1];
                    c.pop();
                }
            cs[j++] = cs[i];
        }
    }
    cs.resize(j);
}


void Solver::removeSubsumed(std::vector<CRef> &cs) {
    struct ClauseInfo {
        CRef cref;
        std::vector<Lit> lits;
    };

    std::vector<ClauseInfo> infos;
    infos.reserve(cs.size());
    for (CRef cr : cs) {
        if (isRemoved(cr)) {
            continue;
        }
        Clause &c = ca->get_clause(cr);
        if (c.size() > 128) {
            continue;
        }
        std::vector<Lit> lits;
        lits.reserve(c.size());
        for (uint32_t i = 0; i < c.size(); i++) {
            lits.emplace_back(c[i]);
        }
        std::sort(lits.begin(), lits.end(),
                  [](Lit a, Lit b) { return toInt(a) < toInt(b); });
        infos.push_back(ClauseInfo{cr, std::move(lits)});
    }

    if (infos.empty()) return;

    std::sort(infos.begin(), infos.end(),
              [](const ClauseInfo &a, const ClauseInfo &b) {
                  return a.lits.size() < b.lits.size();
              });

    std::vector<std::vector<size_t>> occurs;
    occurs.resize(nVars());
    for (size_t i = 0; i < infos.size(); i++) {
        for (Lit l : infos[i].lits) {
            occurs[var(l)].push_back(i);
        }
    }

    auto subsume_except_one = [](const std::vector<Lit> &a,
                                 const std::vector<Lit> &b,
                                 Lit &diff) -> bool {
        diff = lit_Undef;
        if (a.size() > b.size()) {
            return false;
        }
        size_t j = 0;
        for (size_t i = 0; i < a.size(); i++) {
            Var va = var(a[i]);
            while (j < b.size() && var(b[j]) < va) {
                j++;
            }
            if (j == b.size() || var(b[j]) != va) {
                diff = lit_Undef;
                return false;
            }
            if (a[i] != b[j]) {
                if (diff != lit_Undef) {
                    diff = lit_Undef;
                    return false;
                }
                diff = a[i];
            }
            j++;
        }
        return diff == lit_Undef;
    };

    auto strengthen_clause = [&](CRef cr, Lit remove_lit) -> bool {
        Clause &c = ca->get_clause(cr);
        if (c.size() <= 2) {
            return false;
        }
        detachClause(cr);
        for (uint32_t i = 0; i < c.size(); i++) {
            if (c[i] == remove_lit) {
                c[i] = c[c.size() - 1];
                c.pop();
                break;
            }
        }
        attachClause(cr);
        return true;
    };

    for (size_t i = 0; i < infos.size(); i++) {
        if (isRemoved(infos[i].cref)) continue;

        Var best_var = var(infos[i].lits[0]);
        size_t best_occurs = occurs[best_var].size();
        for (Lit l : infos[i].lits) {
            size_t occ_size = occurs[var(l)].size();
            if (occ_size < best_occurs) {
                best_occurs = occ_size;
                best_var = var(l);
            }
        }
        for (size_t idx : occurs[best_var]) {
            if (idx == i || isRemoved(infos[idx].cref)) {
                continue;
            }
            Lit diff = lit_Undef;
            bool subsumes = subsume_except_one(infos[i].lits, infos[idx].lits, diff);
            if (subsumes) {
                removeClause(infos[idx].cref);
                continue;
            }
            if (diff == lit_Undef) {
                continue;
            }
            if (infos[i].lits.size() == infos[idx].lits.size()) {
                if (infos[i].lits.size() > 2) {
                    removeClause(infos[idx].cref);
                    strengthen_clause(infos[i].cref, diff);
                    auto &lits = infos[i].lits;
                    auto it = std::find(lits.begin(), lits.end(), diff);
                    if (it != lits.end()) {
                        lits.erase(it);
                    }
                }
            } else {
                if (infos[idx].lits.size() > 2) {
                    Lit remove_lit = ~diff;
                    strengthen_clause(infos[idx].cref, remove_lit);
                    auto &lits = infos[idx].lits;
                    auto it = std::find(lits.begin(), lits.end(), remove_lit);
                    if (it != lits.end()) {
                        lits.erase(it);
                    }
                }
            }
        }
    }

    size_t j = 0;
    for (size_t i = 0; i < cs.size(); i++) {
        if (!isRemoved(cs[i])) {
            cs[j++] = cs[i];
        }
    }
    cs.resize(j);
}


void Solver::removeTempLearnt() {
    for (CRef cls : temp_clauses) {
        removeClause(cls);
    }
    temp_clauses.clear();
}


void Solver::simplify() {
    assert(decisionLevel() == 0);

    if (simpDB_called <= 128) return;
    simpDB_called = 0;

    // Remove satisfied clauses:
    if (nAssigns() > simpDB_assigns) {
        removeSatisfied(learnts);
        removeSatisfied(clauses);
        simpDB_assigns = nAssigns();
    }

    // Remove subsumed clauses:
    if (nClauses() > simpDB_clauses + 512) {
        removeSubsumed(clauses);
        simpDB_clauses = nClauses();
    }

    // check whether we need to rebuild the clauses db
    if (simpDB_props <= 0) {
        checkGarbage();
        simpDB_props = clauses_literals + learnts_literals;
    }
}


lbool Solver::search(int nof_conflicts) {
    assert(ok);
    assert(nof_conflicts >= 0);
    size_t backtrack_level;
    int conflictC = 0;
    std::vector<Lit> &learnt_clause = learnt_clause_tmp;
    starts++;

    for (;;) {
        CRef confl = propagate();
        if (confl != CRef_Undef) {
            // CONFLICT
            conflicts++;
            conflictC++;
            if (decisionLevel() == 0) {
                return l_False;
            }

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);

            if (learnt_clause.size() == 1) {
                uncheckedEnqueue(learnt_clause[0]);
            } else {
                CRef cr = ca->alloc(learnt_clause, true);
                if (deducedByTemp(learnt_clause))
                    temp_clauses.emplace_back(cr);
                else
                    learnts.emplace_back(cr);
                attachClause(cr);
                claBumpActivity(ca->get_clause(cr));
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            claDecayActivity();

            if (--learntsize_adjust_cnt == 0) {
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt = (int)learntsize_adjust_confl;
                max_learnts *= learntsize_inc;

                if (verbosity >= 1) printProgress();
            }

        } else {
            // NO CONFLICT
            if (conflictC >= nof_conflicts &&
                decisionLevel() >= assumptions.size()) {
                // Reached bound on number of conflicts:
                cancelUntil(assumptions.size());
                return l_Undef;
            }

            if (learnts.size() > max_learnts) {
                // Reduce the set of learnt clauses:
                reduceDB();
            }

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()) {
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True || !inDomain(var(p))) {
                    // Dummy decision level:
                    newDecisionLevel();
                } else if (value(p) == l_False) {
                    analyzeFinal(~p);
                    return l_False;
                } else {
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef) {
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef) {
                    // Model found:
                    return l_True;
                }
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const {
    double progress = 0;
    double F = 1.0 / nVars();

    for (size_t i = 0; i <= decisionLevel(); i++) {
        size_t beg = i == 0 ? 0 : trail_lim[i - 1];
        size_t end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}


static double luby(double y, int x) {
    int size, seq;
    for (size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1);

    while (size - 1 != x) {
        size = (size - 1) >> 1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}


lbool Solver::solve_() {
    assert(state_ == SolverState::Ready);
    if (!ok) {
        last_result_ = l_False;
        state_ = SolverState::Solved;
        return l_False;
    }

    solves++;
    simpDB_called++;

    max_learnts = nClauses() * learntsize_factor;

    learntsize_adjust_confl = learntsize_adjust_start_confl;
    learntsize_adjust_cnt = (int)learntsize_adjust_confl;
    lbool status = l_Undef;

    if (verbosity >= 1) printHead();

    // Simplify the set of problem clauses before enabling domain-restricted solving.
    simplify();

    // set runtime flag
    if (solve_in_domain)
        solve_in_domain_runtime_flag = true;

    if (solve_in_domain) {
        for (Var v : domain_list) {
            insertVarOrder(v);
        }
    } else {
        for (int i = 0; i < nVars(); i++) {
            insertVarOrder(i);
        }
    }
    if (temp_cls_activated || solve_in_domain) {
        traillim_snapshot = trail.size();
    }

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef && restartInLimit(curr_restarts)) {
        double rest_base = luby(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        curr_restarts++;
    }

    if (status == l_False && !has_failed)
        ok = false;
    last_result_ = status;
    state_ = SolverState::Solved;

    if (verbosity >= 1) {
        printStats();
        printResult();
        // if (status == l_True) printModel();
    }

    return status;
}


void Solver::relocAll(std::shared_ptr<ClauseAllocator> new_ca) {
    // All watchers:
    //
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++) {
            Lit p = mkLit(v, s);
            std::vector<Watcher> &ws = watches[p];
            for (size_t j = 0; j < ws.size(); j++)
                ca->reloc(ws[j].cref, new_ca);
        }

    // All reasons:
    //
    for (size_t i = 0; i < trail.size(); i++) {
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef &&
            (ca->get_clause(reason(v)).reloced() || locked(ca->get_clause(reason(v))))) {
            assert(!isRemoved(reason(v)));
            ca->reloc(vardata[v].reason, new_ca);
        }
    }

    // All learnt:
    //
    size_t i, j;
    for (i = j = 0; i < learnts.size(); i++)
        if (!isRemoved(learnts[i])) {
            ca->reloc(learnts[i], new_ca);
            learnts[j++] = learnts[i];
        }
    learnts.resize(j);

    // All temporary:
    //
    for (i = j = 0; i < temp_clauses.size(); i++)
        if (!isRemoved(temp_clauses[i])) {
            ca->reloc(temp_clauses[i], new_ca);
            temp_clauses[j++] = temp_clauses[i];
        }
    temp_clauses.resize(j);

    // All original:
    //
    for (i = j = 0; i < clauses.size(); i++)
        if (!isRemoved(clauses[i])) {
            ca->reloc(clauses[i], new_ca);
            clauses[j++] = clauses[i];
        }
    clauses.resize(j);
}


void Solver::garbageCollect() {
    std::shared_ptr<ClauseAllocator> new_ca =
        std::make_shared<ClauseAllocator>(ca->total_capacity());
    relocAll(new_ca);
    ca = new_ca;
    reduce_db_lt.update(ca);
    watches.update(ca);
}


void Solver::printStats() const {
    std::cout << "===============================================================================\n";
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    std::cout << "starts                : " << starts << "\n";

    std::cout << "conflicts             : "
              << std::left << std::setw(12) << conflicts
              << "   (" << std::fixed << std::setprecision(0)
              << (conflicts / cpu_time) << " /sec)\n";

    std::cout << "decisions             : "
              << std::left << std::setw(12) << decisions
              << "   (" << std::setprecision(0)
              << (decisions / cpu_time) << " /sec)\n";

    std::cout << "propagations          : "
              << std::left << std::setw(12) << propagations
              << "   (" << std::setprecision(0)
              << (propagations / cpu_time) << " /sec)\n";

    std::cout << "conflict literals     : "
              << std::left << std::setw(12) << tot_literals
              << "   (" << std::fixed << std::setprecision(2)
              << ((max_literals - tot_literals) * 100 / static_cast<double>(max_literals))
              << " %% deleted)\n";

    if (mem_used != 0) {
        std::cout << "Memory used           : "
                  << std::fixed << std::setprecision(2) << mem_used << " MB\n";
    }

    std::cout << "CPU time              : ";
    std::cout << std::setprecision(3) << cpu_time << " s\n";
}


void Solver::printResult() const {
    if (last_result_ == l_True)
        std::cout << "sat";
    else if (last_result_ == l_False)
        std::cout << "unsat";
    else
        std::cout << "unknow";
    std::cout << std::endl;
}

void Solver::printModel() const {
    if (last_result_ != l_True) return;

    std::cout << "v";
    for (Var v = 1; v < nVars(); ++v) {
        if (assigns[v] == assign_True) {
            std::cout << " " << v;
        } else if (assigns[v] == assign_False) {
            std::cout << " -" << v;
        }
    }
    std::cout << " 0\n";
}

void Solver::printHead() const {
    std::cout << "============================[ Search Statistics ]==============================\n";
    std::cout << "| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n";
    std::cout << "|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n";
    std::cout << "===============================================================================\n";
}

void Solver::printProgress() const {
    size_t diff = static_cast<size_t>(dec_vars) -
                  (trail_lim.size() == 0 ? trail.size() : trail_lim[0]);
    double avg_literals = (nLearnts() > 0) ? static_cast<double>(learnts_literals) / nLearnts() : 0.0;
    double progress = progressEstimate() * 100;
    std::cout << "| "
              << std::setw(9) << static_cast<int>(conflicts) << " | "
              << std::setw(7) << diff << " "
              << std::setw(8) << nClauses() << " "
              << std::setw(8) << static_cast<int>(clauses_literals) << " | "
              << std::setw(8) << static_cast<int>(max_learnts) << " "
              << std::setw(8) << nLearnts() << " "
              << std::setw(6) << std::fixed << std::setprecision(0) << avg_literals << " | "
              << std::setw(6) << std::fixed << std::setprecision(3) << progress << " % |"
              << std::endl;
}

} // namespace minicore
