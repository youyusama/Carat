#include "solver.h"
#include <stdexcept>

namespace minicore {

namespace {

// Support sets are packed bitsets over the current unsat core.
constexpr size_t MLQPSupportMaskBits = 64;
constexpr unsigned MLQPEntryFlag = 1u;
constexpr unsigned MLQPSupportFlag = 4u;

inline size_t MLQPSupportChunks(size_t bits) {
    return (bits + MLQPSupportMaskBits - 1) / MLQPSupportMaskBits;
}

inline size_t MLQPSupportSize(const MLQPSupportSet &support) {
    size_t size = 0;
    for (MLQPSupportMask chunk : support) {
        size += static_cast<size_t>(__builtin_popcountll(static_cast<unsigned long long>(chunk)));
    }
    return size;
}

inline void SetMLQPUnitSupport(MLQPSupportSet &support, size_t chunks, size_t idx) {
    support.assign(chunks, 0);
    support[idx / MLQPSupportMaskBits] = MLQPSupportMask(1) << (idx % MLQPSupportMaskBits);
}

inline void SetMLQPFullSupport(MLQPSupportSet &support, size_t bits) {
    const size_t chunks = MLQPSupportChunks(bits);
    support.assign(chunks, ~MLQPSupportMask(0));
    const size_t tail_bits = bits % MLQPSupportMaskBits;
    if (tail_bits != 0) {
        support.back() = (MLQPSupportMask(1) << tail_bits) - MLQPSupportMask(1);
    }
}

inline void ClearMLQPSupport(MLQPSupportSet &support, size_t chunks) {
    support.assign(chunks, 0);
}

inline size_t MergeMLQPSupportCountNew(MLQPSupportSet &target, const MLQPSupportMask *source, size_t chunks) {
    size_t new_bits = 0;
    for (size_t i = 0; i < chunks; i++) {
        const MLQPSupportMask old_mask = target[i];
        const MLQPSupportMask new_mask = old_mask | source[i];
        target[i] = new_mask;
        new_bits += static_cast<size_t>(__builtin_popcountll(static_cast<unsigned long long>(new_mask ^ old_mask)));
    }
    return new_bits;
}

inline bool MLQPSupportHasBit(const MLQPSupportSet &support, size_t idx) {
    return support[idx / MLQPSupportMaskBits] & (MLQPSupportMask(1) << (idx % MLQPSupportMaskBits));
}

inline size_t MLQPPendingHash(CRef cr) {
    uint32_t x = cr >> 2;
    x ^= x >> 16;
    x *= 0x7feb352dU;
    x ^= x >> 15;
    x *= 0x846ca68bU;
    x ^= x >> 16;
    return static_cast<size_t>(x);
}

} // namespace

void Solver::initMLQPState(size_t core_size) {
    mlqp_core_size = core_size;
    mlqp_best_size = core_size;
    mlqp_support_chunks = MLQPSupportChunks(core_size);

    if (++mlqp_pending_seen_epoch == 0) {
        std::fill(mlqp_pending_seen_stamps.begin(), mlqp_pending_seen_stamps.end(), 0);
        ++mlqp_pending_seen_epoch;
    }
    assert(mlqp_entries.empty());
    mlqp_pending_entries.clear();
    mlqp_pending_clauses.clear();
    for (size_t target : mlqp_bypass_targets)
        mlqp_bypass_rules[target].clear();
    mlqp_bypass_targets.clear();
    if (m_mlqpStrategy == 2 && mlqp_bypass_rules.size() < core_size)
        mlqp_bypass_rules.resize(core_size);
    mlqp_support_pool.clear();
    if (m_mlqpStrategy > 0) {
        // markMLQPPendingClause grows this table as needed. Most queries touch
        // only a small part of the formula; avoid zeroing a formula-sized table.
        reserveMLQPPendingSeen(16);
    }

    ClearMLQPSupport(mlqp_zero_support, mlqp_support_chunks);
    SetMLQPFullSupport(mlqp_best_core, core_size);

    const size_t bucket_count = core_size + 1;
    if (mlqp_buckets.size() < bucket_count)
        mlqp_buckets.resize(bucket_count);
    for (size_t i = 0; i < bucket_count; i++) {
        mlqp_buckets[i].clear();
    }
    mlqp_bucket_heads.assign(bucket_count, 0);
}

const Solver::MLQPEntry *Solver::findMLQPEntry(Lit p) const {
    const unsigned bit = MLQPEntryFlag << sign(p);
    if (!(seen[var(p)] & bit)) return nullptr;
    const size_t index = failed_stamp[toInt(p)];
    assert(index < mlqp_entries.size() && mlqp_entries[index].literal == p);
    return &mlqp_entries[index];
}

Solver::MLQPEntry &Solver::ensureMLQPEntry(Lit p) {
    if (findMLQPEntry(p)) return mlqp_entries[failed_stamp[toInt(p)]];
    const size_t index = mlqp_entries.size();
    assert(index < UINT32_MAX);
    mlqp_entries.push_back({p, failed_stamp[toInt(p)]});
    // Mutate borrowed SAT storage only after allocation succeeds.
    failed_stamp[toInt(p)] = static_cast<uint32_t>(index);
    seen[var(p)] |= MLQPEntryFlag << sign(p);
    return mlqp_entries.back();
}

void Solver::restoreMLQPState() {
    for (const auto &entry : mlqp_entries) {
        failed_stamp[toInt(entry.literal)] = entry.saved_failed_stamp;
        seen[var(entry.literal)] &= ~((MLQPEntryFlag | MLQPSupportFlag) << sign(entry.literal));
    }
    mlqp_entries.clear();
}

MLQPSupportLookup Solver::lookupMLQPSupport(Lit p) const {
    if (seen[var(p)] & (MLQPSupportFlag << sign(p))) {
        const auto *entry = &mlqp_entries[failed_stamp[toInt(p)]];
        if (mlqp_support_chunks == 1)
            return {&entry->inline_support, entry->support_size};
        return {mlqp_support_pool.data() + entry->support_offset, entry->support_size};
    }

    if (value(p) == l_True && level(var(p)) == 0) {
        return {mlqp_zero_support.data(), 0};
    }

    return {};
}

void Solver::updateMLQPBestCore(const MLQPSupportSet &support) {
    updateMLQPBestCore(support, MLQPSupportSize(support));
}

void Solver::updateMLQPBestCore(const MLQPSupportSet &support, size_t support_size) {
    if (support_size < mlqp_best_size) {
        mlqp_best_size = support_size;
        mlqp_best_core = support;
    }
}

void Solver::updateMLQPSupport(Lit p, const MLQPSupportSet &cand_support, size_t cand_size) {

    // An alternative support need not improve the singleton {p}. Save it before
    // either size cutoff, but never record a rule that depends on its own head.
    const auto *existing = findMLQPEntry(p);
    const size_t assumption = existing ? existing->assumption : size_t(-1);
    if (m_mlqpStrategy == 2 && assumption != size_t(-1) &&
        !MLQPSupportHasBit(cand_support, assumption)) {
        auto &rules = mlqp_bypass_rules[assumption];
        // Repeated clause scans often rediscover the last rule. Avoid a full
        // dominance/deduplication search on this propagation hot path.
        if (rules.empty() || !std::equal(cand_support.begin(), cand_support.end(),
                                         rules.end() - mlqp_support_chunks)) {
            if (rules.empty()) mlqp_bypass_targets.push_back(assumption);
            rules.insert(rules.end(), cand_support.begin(), cand_support.end());
        }
    }
    if (cand_size >= mlqp_best_size)
        return;

    MLQPSupportLookup old_support = lookupMLQPSupport(p);
    if (old_support.bits != nullptr && cand_size >= old_support.size) {
        return;
    }
    auto &entry = ensureMLQPEntry(p);
    if (mlqp_support_chunks == 1) {
        entry.inline_support = cand_support[0];
    } else if (entry.support_size == size_t(-1)) {
        entry.support_offset = mlqp_support_pool.size();
        mlqp_support_pool.insert(mlqp_support_pool.end(), cand_support.begin(), cand_support.end());
    } else {
        std::copy(cand_support.begin(), cand_support.end(),
                  mlqp_support_pool.begin() + entry.support_offset);
    }
    entry.support_size = cand_size;
    seen[var(p)] |= MLQPSupportFlag << sign(p);
    mlqp_buckets[cand_size].push_back(p);

    MLQPSupportLookup opp_support = lookupMLQPSupport(~p);
    if (opp_support.bits != nullptr) {
        mlqp_conflict_support = cand_support;
        const size_t conflict_size = cand_size + MergeMLQPSupportCountNew(mlqp_conflict_support, opp_support.bits, mlqp_support_chunks);
        updateMLQPBestCore(mlqp_conflict_support, conflict_size);
    }
}

void Solver::reduceMLQPBypassCore() {
    const size_t before_size = mlqp_best_size;
    // Rules are fixed now. If closure cannot derive u from C\{u}, shrinking C
    // cannot make it derivable later. Thus one sequential pass suffices; each
    // successful deletion still takes effect before testing the next candidate.
    for (size_t candidate : mlqp_bypass_targets) {
        if (!MLQPSupportHasBit(mlqp_best_core, candidate)) continue;

        mlqp_bypass_available = mlqp_best_core;
        const size_t chunk = candidate / MLQPSupportMaskBits;
        const MLQPSupportMask bit = MLQPSupportMask(1) << (candidate % MLQPSupportMaskBits);
        mlqp_bypass_available[chunk] &= ~bit;

        bool changed;
        do {
            changed = false;
            for (size_t target : mlqp_bypass_targets) {
                if (MLQPSupportHasBit(mlqp_bypass_available, target)) continue;
                const auto &rules = mlqp_bypass_rules[target];
                for (size_t offset = 0; offset < rules.size(); offset += mlqp_support_chunks) {
                    size_t i = 0;
                    while (i < mlqp_support_chunks &&
                           (rules[offset + i] & ~mlqp_bypass_available[i]) == 0)
                        ++i;
                    if (i != mlqp_support_chunks) continue;

                    mlqp_bypass_available[target / MLQPSupportMaskBits] |=
                        MLQPSupportMask(1) << (target % MLQPSupportMaskBits);
                    changed = true;
                    break;
                }
                if (mlqp_bypass_available[chunk] & bit) break;
            }
        } while (changed && !(mlqp_bypass_available[chunk] & bit));

        if (mlqp_bypass_available[chunk] & bit) {
            mlqp_best_core[chunk] &= ~bit;
            --mlqp_best_size;
        }
    }
    mlqp_bypass_reduced_literals = before_size - mlqp_best_size;
}

void Solver::addMLQPPendingClause(Lit p, uint32_t clause_index) {
    if (mlqp_pending_entries.size() >= UINT32_MAX)
        throw std::length_error("MLQP pending link index overflow");
    auto &entry = ensureMLQPEntry(p);
    mlqp_pending_entries.push_back({clause_index, entry.pending_head});
    entry.pending_head = static_cast<uint32_t>(mlqp_pending_entries.size() - 1);
}

void Solver::reserveMLQPPendingSeen(size_t min_entries) {
    size_t capacity = mlqp_pending_seen_indices.size();
    if (capacity != 0 && capacity * 3 >= min_entries * 4)
        return;

    size_t new_capacity = 16;
    while (new_capacity * 3 < min_entries * 4)
        new_capacity <<= 1;

    // Keep the old table valid if either allocation fails.
    std::vector<uint32_t> new_indices(new_capacity, UINT32_MAX);
    std::vector<uint32_t> new_stamps(new_capacity, 0);

    const uint32_t stamp = mlqp_pending_seen_epoch;
    const size_t mask = new_capacity - 1;
    for (size_t i = 0; i < mlqp_pending_seen_indices.size(); i++) {
        if (mlqp_pending_seen_stamps[i] != stamp)
            continue;

        const uint32_t index = mlqp_pending_seen_indices[i];
        CRef cr = mlqp_pending_clauses[index].clause;
        size_t pos = MLQPPendingHash(cr) & mask;
        while (new_stamps[pos] == stamp)
            pos = (pos + 1) & mask;
        new_indices[pos] = index;
        new_stamps[pos] = stamp;
    }
    mlqp_pending_seen_indices.swap(new_indices);
    mlqp_pending_seen_stamps.swap(new_stamps);
}

uint32_t Solver::findMLQPPendingClause(CRef cr) const {
    if (mlqp_pending_clauses.empty()) return UINT32_MAX;
    const uint32_t stamp = mlqp_pending_seen_epoch;
    const size_t mask = mlqp_pending_seen_indices.size() - 1;
    size_t pos = MLQPPendingHash(cr) & mask;
    while (mlqp_pending_seen_stamps[pos] == stamp) {
        const uint32_t index = mlqp_pending_seen_indices[pos];
        if (mlqp_pending_clauses[index].clause == cr) return index;
        pos = (pos + 1) & mask;
    }
    return UINT32_MAX;
}

bool Solver::markMLQPPendingClause(CRef cr) {
    if (findMLQPPendingClause(cr) != UINT32_MAX) return false;
    if (mlqp_pending_clauses.size() >= UINT32_MAX)
        throw std::length_error("MLQP pending clause index overflow");
    reserveMLQPPendingSeen(mlqp_pending_clauses.size() + 1);
    const uint32_t index = static_cast<uint32_t>(mlqp_pending_clauses.size());
    assert(mlqp_unresolved_clause_tmp.size() >= 2);
    mlqp_pending_clauses.push_back({cr, mlqp_unresolved_clause_tmp[0],
                                  mlqp_unresolved_clause_tmp[1]});

    const uint32_t stamp = mlqp_pending_seen_epoch;
    const size_t mask = mlqp_pending_seen_indices.size() - 1;
    size_t pos = MLQPPendingHash(cr) & mask;
    while (mlqp_pending_seen_stamps[pos] == stamp) pos = (pos + 1) & mask;
    mlqp_pending_seen_indices[pos] = index;
    mlqp_pending_seen_stamps[pos] = stamp;
    return true;
}

bool Solver::mlqpPendingBlocked(uint32_t index) {
    auto &pending = mlqp_pending_clauses[index];
    if (pending.cursor == UINT32_MAX) return false;

    // Negative support takes precedence even if both polarities are known.
    // Presence only grows during one MLQP call; improving a support cannot
    // make a previously false literal a replacement candidate again.
    auto is_false = [this](Lit p) {
        return (seen[var(p)] & (MLQPSupportFlag << !sign(p))) ||
               (value(p) == l_False && level(var(p)) == 0);
    };
    if (is_false(pending.first)) pending.first = lit_Undef;
    if (is_false(pending.second)) pending.second = lit_Undef;
    if (pending.first != lit_Undef && pending.second != lit_Undef) return true;

    const Clause &clause = ca->get_clause(pending.clause);
    while (pending.cursor < clause.size()) {
        Lit q = clause[pending.cursor++];
        if (q == pending.first || q == pending.second || is_false(q)) continue;
        if (pending.first == lit_Undef) pending.first = q;
        else pending.second = q;
        if (pending.first != lit_Undef && pending.second != lit_Undef) return true;
    }
    // Fewer than two non-false literals remain. Keep all subscriptions: later
    // support improvements can still change the unit/conflict/bypass result.
    pending.cursor = UINT32_MAX;
    return false;
}

void Solver::mlqpScanClause(CRef cr) {
    if (mlqp_support_chunks == 1) mlqpScanClauseImpl<true>(cr);
    else mlqpScanClauseImpl<false>(cr);
}

template <bool SingleWord>
void Solver::mlqpScanClauseImpl(CRef cr) {
    if (isRemoved(cr))
        return;

    Clause &clause = ca->get_clause(cr);
    // Only registered pending clauses can be skipped: their first full scan
    // has already installed every notification the original algorithm needs.
    // Run this after CRef ordering, since earlier clauses may update supports.
    if (clause.size() > 2) {
        const uint32_t pending = findMLQPPendingClause(cr);
        if (pending != UINT32_MAX && mlqpPendingBlocked(pending)) return;
    }
    bool merged_initialized = false;
    size_t merged_size = 0;
    MLQPSupportMask merged_word = 0;
    int unresolved = 0;
    Lit local = lit_Undef;
    Lit implied = lit_Undef;
    bool satisfied = false;

    mlqp_unresolved_clause_tmp.clear();

    for (size_t i = 0; i < clause.size(); i++) {
        Lit q = clause[i];
        if (!inDomain(var(q))) {
            satisfied = true;
            break;
        }
        MLQPSupportLookup neg_support;
        bool positive_known = false;
        if constexpr (SingleWord) {
            // Read SAT's scratch flags once for both polarities. A valid support
            // bit avoids chasing entries that only hold a pending-clause list.
            const unsigned flags = seen[var(q)];
            if (flags & (MLQPSupportFlag << !sign(q))) {
                const auto &entry = mlqp_entries[failed_stamp[toInt(~q)]];
                neg_support.bits = &entry.inline_support;
            } else {
                const auto current = assigns[var(q)] ^ sign(q);
                if (current == assign_False && level(var(q)) == 0)
                    neg_support.bits = mlqp_zero_support.data();
                else {
                    positive_known = (flags & (MLQPSupportFlag << sign(q))) ||
                        (current == assign_True && level(var(q)) == 0);
                }
            }
        } else {
            neg_support = lookupMLQPSupport(~q);
        }
        // literal is false
        if (neg_support.bits != nullptr) {
            if constexpr (SingleWord) {
                const auto previous = merged_word;
                merged_word |= *neg_support.bits;
                if (merged_word != previous)
                    merged_size = __builtin_popcountll(merged_word);
            } else {
                if (!merged_initialized) {
                    ClearMLQPSupport(mlqp_merged_support, mlqp_support_chunks);
                    merged_initialized = true;
                }
                if (neg_support.size != 0)
                    merged_size += MergeMLQPSupportCountNew(mlqp_merged_support, neg_support.bits, mlqp_support_chunks);
            }
            if (merged_size >= mlqp_best_size && mlqp_best_size < mlqp_core_size) {
                // The old path discarded this scan after reaching the end of
                // the clause. No later literal can undo this size cutoff.
                return;
            }
            continue;
        }

        if constexpr (!SingleWord)
            positive_known = lookupMLQPSupport(q).bits != nullptr;
        if (positive_known) {
            if (m_mlqpStrategy == 2 && local == lit_Undef) {
                local = q;
                continue;
            } else {
                satisfied = true;
                break;
            }
        } // literal is true

        // literal is lit_Undef
        unresolved++;
        mlqp_unresolved_clause_tmp.push_back(q);
        implied = q;
    }

    if (!satisfied && unresolved > 1 && markMLQPPendingClause(cr)) {
        const uint32_t index = static_cast<uint32_t>(mlqp_pending_clauses.size() - 1);
        for (Lit q : mlqp_unresolved_clause_tmp) {
            addMLQPPendingClause(~q, index);
        }
    }

    if (satisfied || unresolved > 1)
        return;
    if constexpr (SingleWord) {
        mlqp_merged_support.assign(1, merged_word);
    } else {
        if (!merged_initialized)
            ClearMLQPSupport(mlqp_merged_support, mlqp_support_chunks);
    }
    if (local != lit_Undef) {
        if (unresolved == 0) updateMLQPSupport(local, mlqp_merged_support, merged_size);
    } else {
        if (unresolved == 0)
            updateMLQPBestCore(mlqp_merged_support, merged_size);
        else
            updateMLQPSupport(implied, mlqp_merged_support, merged_size);
    }
}

void Solver::mlqpPropagate(Lit p) {
    // In this solver, watches[p] is the frontier for clauses watching ~p.
    const std::vector<Watcher> &watched_on_neg_p = watches[p];
    mlqp_propagate_clauses.clear();
    for (const Watcher &watch : watched_on_neg_p) {
        Lit blocker = watch.blocker;
        if (!inDomain(var(blocker)))
            continue;
        if (m_mlqpStrategy == 1 && lookupMLQPSupport(blocker).bits != nullptr) // literal is true
            continue;
        mlqp_propagate_clauses.push_back(watch.cref);
    }

    const auto *entry = findMLQPEntry(p);
    for (uint32_t index = entry ? entry->pending_head : UINT32_MAX;
         index != UINT32_MAX; index = mlqp_pending_entries[index].next)
        mlqp_propagate_clauses.push_back(mlqp_pending_clauses[mlqp_pending_entries[index].clause_index].clause);

    std::sort(mlqp_propagate_clauses.begin(), mlqp_propagate_clauses.end());
    CRef last = CRef_Undef;
    bool has_last = false;
    for (CRef cr : mlqp_propagate_clauses) {
        if (has_last && cr == last)
            continue;
        last = cr;
        has_last = true;
        mlqpScanClause(cr);
    }
}

bool Solver::reduceMLQPCore(const std::vector<Lit> &core_assumps) {
    // SAT analysis leaves seen cleared. Neither SAT nor failed() may run while
    // its scratch/index slots are borrowed. Also restore on allocation failure.
    struct RestoreState {
        Solver &solver;
        bool active = true;
        ~RestoreState() {
            if (active) {
                solver.restoreMLQPState();
            }
        }
        void finish() { solver.restoreMLQPState(); active = false; }
    } restore{*this};
    // Preserve the input order when assigning support bits and queuing assumptions.
    initMLQPState(core_assumps.size());
    if (m_mlqpStrategy == 2) {
        for (size_t i = 0; i < core_assumps.size(); ++i) {
            auto &entry = ensureMLQPEntry(core_assumps[i]);
            // Repeated primed literals use their first singleton support.
            if (entry.assumption == size_t(-1)) entry.assumption = i;
        }
    }

    if (temp_cls_activated) {
        ClearMLQPSupport(mlqp_work_support, mlqp_support_chunks);
        updateMLQPSupport(mkLit(temp_cls_act_var), mlqp_work_support, 0);
    }

    for (size_t i = 0; i < core_assumps.size(); i++) {
        SetMLQPUnitSupport(mlqp_work_support, mlqp_support_chunks, i);
        updateMLQPSupport(core_assumps[i], mlqp_work_support, 1);
    }

    for (size_t bucket_size = 0; bucket_size <= mlqp_core_size && bucket_size < mlqp_best_size; bucket_size++) {
        auto &bucket = mlqp_buckets[bucket_size];
        size_t &head = mlqp_bucket_heads[bucket_size];
        while (head < bucket.size()) {
            Lit p = bucket[head++];

            const auto *entry = findMLQPEntry(p);
            if (!entry || entry->support_size != bucket_size)
                continue;
            if (bucket_size >= mlqp_best_size)
                break;

            mlqpPropagate(p);
        }
    }
    // Bypass can reduce the core even when propagation cannot.
    if (m_mlqpStrategy == 2) reduceMLQPBypassCore();
    restore.finish();

    if (mlqp_best_size >= core_assumps.size())
        return false;

    // Publish only after all allocations succeed. The supplied UC may differ
    // from SAT's old core; rebuild every failed mark instead of just removing.
    failed_core.reserve(mlqp_best_size);
    clearFailed();
    for (size_t i = 0; i < core_assumps.size(); i++)
        if (MLQPSupportHasBit(mlqp_best_core, i)) markFailed(core_assumps[i]);
    // Preserve temporary-clause dependency, even when the user core is empty.
    if (temp_cls_activated) markFailed(mkLit(temp_cls_act_var));
    return true;
}

} // namespace minicore
