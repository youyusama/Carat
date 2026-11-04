#include "IC3.h"
#include "WitnessBuilder.h"
#include <algorithm>
#include <iostream>
#include <iterator>
#include <set>
#include <sstream>

namespace car {

IC3::IC3(Settings settings,
         Model &model,
         Log &log) : m_settings(settings),
                     m_log(log),
                     m_model(model) {
    State::num_inputs = model.GetNumInputs();
    State::num_latches = model.GetNumLatches();
    m_cexStart = nullptr;
    m_checkResult = CheckResult::Unknown;

    m_settings.satSolveInDomain = m_settings.satSolveInDomain && m_settings.solver == MCSATSolver::minicore;
}

IC3::~IC3() {
}

CheckResult IC3::Run() {
    signal(SIGINT, SignalHandler);

    if (Check())
        m_checkResult = CheckResult::Safe;
    else
        m_checkResult = CheckResult::Unsafe;

    PrintALLStats();
    m_log.PrintCustomStatistics();

    return m_checkResult;
}

std::vector<std::pair<Cube, Cube>> IC3::GetCexTrace() {
    if (m_cexTrace.empty()) BuildCEXTrace();
    return m_cexTrace;
}

void IC3::BuildCEXTrace() {
    m_cexTrace.clear();
    if (!m_cexStart) return;

    for (auto cur = m_cexStart; cur != nullptr; cur = cur->preState) {
        m_cexTrace.emplace_back(cur->inputs, cur->latches);
    }
    if (m_cexTrace.empty()) return;

    // Preserve choices for uninitialized latches and add fixed reset values.
    if (m_initialState) {
        LitSet firstState;
        firstState.NewSet(m_cexTrace.front().second);
        for (Lit literal : m_initialState->latches) {
            assert(!firstState.Has(~literal));
            if (!firstState.Has(literal)) {
                m_cexTrace.front().second.push_back(literal);
                firstState.Insert(literal);
            }
        }
    }

    auto slv = std::make_shared<SATSolver>(m_model, MCSATSolver::minicore);
    slv->AddTrans();
    slv->AddConstraints();
    for (size_t i = 0; i + 1 < m_cexTrace.size(); ++i) {
        Cube assumptions = m_cexTrace[i].first;
        assumptions.insert(assumptions.end(),
                           m_cexTrace[i].second.begin(),
                           m_cexTrace[i].second.end());
        bool sat = slv->Solve(assumptions);
        assert(sat);

        auto assignment = slv->GetAssignment(true);
        m_cexTrace[i].first = assignment.first;
        LitSet next_state;
        next_state.NewSet(assignment.second);
        assert(SubsumeSet(m_cexTrace[i + 1].second, next_state));
        m_cexTrace[i + 1].second = std::move(assignment.second);
    }
}

FrameList IC3::GetInv() {
    FrameList inv;
    if (m_invariantLevel <= 0) return inv;
    Frame f;
    for (int i = m_invariantLevel; i <= m_k + 1; ++i) {
        for (const Cube &cb : m_lfm.BorderCubes(i)) {
            f.emplace_back(cb);
        }
    }
    if (m_settings.shrinkInvariant) f = ShrinkInv(std::move(f));
    inv.emplace_back(std::move(f));
    return inv;
}

Frame IC3::ShrinkInv(Frame inv) const {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_ShrinkInv");
    const size_t original_size = inv.size();

    // 1. A blocking cube denotes its negated clause. Short cubes subsume
    // supersets; one pass after sorting is enough for this cheap prefilter.
    std::sort(inv.begin(), inv.end(), CubeComp);
    Frame candidates;
    LitSet literals;
    for (const Cube &cube : inv) {
        literals.NewSet(cube);
        bool subsumed = std::any_of(candidates.begin(), candidates.end(),
                                    [&](const Cube &kept) { return SubsumeSet(kept, literals); });
        if (!subsumed) candidates.push_back(cube);
    }
    inv = std::move(candidates);
    if (inv.empty()) return inv;

    Frame primed = inv;
    for (Cube &cube : primed)
        for (Lit &lit : cube) lit = m_model.EnsurePrimeK(lit, 1);

    // Match InitializeStartSolver for safety and AddNewFrame for induction.
    // In FAIR, the forbidden state is the custom initial cube. In RLIVE,
    // shoals/dead restrict the safety query, but not the frame transition.
    auto make_solver = [&](bool safety) {
        auto solver = std::make_unique<SATSolver>(m_model, MCSATSolver::minicore);
        solver->AddTrans();
        solver->AddConstraints();
        if (safety) {
            if (m_settings.searchFromBadPred) {
                solver->AddTransK(1);
                solver->AddBadk(1);
                solver->AddProperty();
                solver->AddConstraintsK(1);
            } else {
                if (m_loopRefuting) {
                    for (Lit lit : m_initialState->latches) solver->AddClause({lit});
                } else {
                    solver->AddBad();
                }
                solver->AddShoalConstraints(m_shoals, m_dead);
                solver->AddWallConstraints(m_walls);
            }
        } else if (m_loopRefuting) {
            solver->AddWallConstraints(m_walls);
        }
        return solver;
    };
    auto add_activations = [&](SATSolver &solver) {
        Cube labels;
        for (const Cube &cube : inv) {
            Lit label = MkLit(solver.GetNewVar());
            Clause clause{~label};
            for (Lit lit : cube) clause.push_back(~lit);
            solver.AddClause(clause);
            labels.push_back(label);
        }
        return labels;
    };

    // 2. Extract a sufficient safety seed, not globally necessary clauses.
    auto safety = make_solver(true);
    Cube labels = add_activations(*safety);
    if (safety->Solve(labels)) {
        LOG_L(m_log, 1, "Invariant shrinking skipped: safety check failed.");
        return inv;
    }
    std::vector<bool> selected(inv.size(), false);
    std::vector<size_t> work;
    for (size_t i = 0; i < inv.size(); ++i) {
        if (safety->Failed(labels[i])) {
            selected[i] = true;
            work.push_back(i);
        }
    }
    const size_t seed_size = work.size();
    safety.reset();

    // 3. NEC: find clauses required by the fixed seed. Reify each clause,
    // and use a sequential at-most-one encoding for false clause labels.
    auto nec = make_solver(false);
    labels = add_activations(*nec);
    Lit previous{};
    for (size_t i = 0; i < inv.size(); ++i) {
        for (Lit lit : inv[i]) nec->AddClause({labels[i], lit});
        if (selected[i]) {
            nec->AddClause({labels[i]});
        } else {
            Lit seen = MkLit(nec->GetNewVar());
            nec->AddClause({labels[i], seen});
            if (previous != Lit{}) {
                nec->AddClause({~previous, seen});
                nec->AddClause({labels[i], ~previous});
            }
            previous = seen;
        }
    }
    for (size_t pos = 0; pos < work.size(); ++pos) {
        while (nec->Solve(primed[work[pos]])) {
            size_t required = inv.size();
            for (size_t i = 0; i < inv.size(); ++i) {
                if (!selected[i] && nec->GetModel(VarOf(labels[i])) == T_FALSE) {
                    required = i;
                    break;
                }
            }
            // No missing clause means the original invariant is unsupported.
            if (required == inv.size()) return inv;
            selected[required] = true;
            work.push_back(required);
            nec->AddClause({labels[required]});
        }
    }
    const size_t necessary_size = work.size();
    nec.reset();

    // 4. FEAS: support the work set, then support the newly added clauses.
    // Targets are an OR of primed blocking cubes, not their conjunction.
    auto support = make_solver(false);
    labels = add_activations(*support);
    Cube violations;
    for (const Cube &cube : primed)
        violations.push_back(support->AddCubeAsLabelK(cube, 0));
    for (size_t i : work) support->AddClause({labels[i]});
    while (!work.empty()) {
        Clause target;
        for (size_t i : work) target.push_back(violations[i]);
        support->AddTempClause(target);
        Cube assumptions;
        for (size_t i = 0; i < inv.size(); ++i)
            if (!selected[i]) assumptions.push_back(labels[i]);
        if (support->Solve(assumptions)) return inv;
        work.clear();
        for (size_t i = 0; i < inv.size(); ++i) {
            if (!selected[i] && support->Failed(labels[i])) {
                selected[i] = true;
                work.push_back(i);
            }
        }
        support->ReleaseTempClause();
        for (size_t i : work) support->AddClause({labels[i]});
    }

    // Recheck the result with no optional activations. Initiation is inherited
    // by taking a subset, including when F_0 is a custom successor image.
    Frame reduced;
    Clause target;
    safety = make_solver(true);
    for (size_t i = 0; i < inv.size(); ++i) {
        if (!selected[i]) continue;
        reduced.push_back(inv[i]);
        target.push_back(violations[i]);
        safety->AddUC(inv[i]);
    }
    if (safety->Solve()) return inv;
    if (!target.empty()) {
        support->AddTempClause(target);
        if (support->Solve()) return inv;
    }
    LOG_L(m_log, 1, "Invariant shrinking: ", original_size, " -> ", inv.size(),
          " after subsumption, seed=", seed_size, ", NEC=", necessary_size,
          ", final=", reduced.size());
    return reduced;
}

void IC3::KLiveIncr() {
    int k_step = m_model.KLivenessIncrement();
    std::vector<Clause> k_clauses = m_model.GetKLiveClauses(k_step);
    Lit k_signal = m_model.GetKLiveSignal(k_step);

    // Extend persistent solvers for k-liveness.
    for (const auto &slv : m_transSolvers) {
        for (const auto &cls : k_clauses) slv->AddClause(cls);
    }
    if (m_initSolver) {
        for (const auto &cls : k_clauses) m_initSolver->AddClause(cls);
    }
    if (m_liftSolver) {
        for (const auto &cls : k_clauses) m_liftSolver->AddClause(cls);
    }

    // Initialize the new k-liveness latch.
    if (m_initialState) m_initialState->latches.emplace_back(~k_signal);
    m_initialStateSet.emplace(~k_signal);
    if (m_initSolver) m_initSolver->AddUC(Cube{k_signal});
    if (!m_searchFromInitSucc && !m_transSolvers.empty()) {
        m_transSolvers[0]->AddUC(Cube{k_signal});
    }

    // Rebuild transient solvers before reuse.
}


bool IC3::ImmediateSatisfiable() {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_ImmSAT");
    // Exclude zero-step successor.
    if (m_searchFromInitSucc) return false;

    auto slv = std::make_unique<SATSolver>(m_model, MCSATSolver::cadical);
    slv->AddTrans();
    slv->AddConstraints();
    slv->AddShoalConstraints(m_shoals, m_dead);
    slv->AddWallConstraints(m_walls);
    assert(m_initialState);
    for (auto i : m_initialState->latches) {
        slv->AddClause(Cube{i});
    }
    Cube assumptions = Cube{m_model.GetBad()};
    bool sat = slv->Solve(assumptions);
    if (sat) {
        auto p = slv->GetAssignment(false);
        m_cexStart = std::make_shared<State>(nullptr, p.first, p.second, 0);
        return true;
    } else if (m_settings.searchFromBadPred) {
        slv->AddTransK(1);
        slv->AddConstraintsK(1);
        slv->AddBadk(1);
        sat = slv->Solve(Cube{});
        if (sat) {
            Cube inputs_bad;
            for (Var i : m_model.GetPropertyCOIInputs()) {
                Lit i_p = m_model.EnsurePrimeK(MkLit(i), 1);
                if (slv->GetModel(VarOf(i_p)) == T_TRUE)
                    inputs_bad.push_back(MkLit(i));
                else if (slv->GetModel(VarOf(i_p)) == T_FALSE)
                    inputs_bad.push_back(~MkLit(i));
            }
            std::shared_ptr<State> bad_state(new State(nullptr, inputs_bad, Cube(), 0));
            auto p = slv->GetAssignment(false);
            m_cexStart = std::make_shared<State>(bad_state, p.first, p.second, 0);
            return true;
        }
    }
    return false;
}


bool IC3::IsInitStateImplyBad() {
    if (m_customInit.empty()) return false;
    auto slv = std::make_shared<SATSolver>(m_model, m_settings.solver);
    slv->AddTrans();
    slv->AddConstraints();
    Cube assumptions = m_customInit;
    assumptions.push_back(~m_model.GetBad());
    bool sat = slv->Solve(assumptions);
    return !sat;
}


void IC3::Extend() {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_Extend");
    // reserve k+1 frames
    while (m_transSolvers.size() <= m_k + 1) AddNewFrame();

    InitializeStartSolver();
    for (const Cube &cb : m_lfm.BorderCubes(m_k)) {
        m_startSolver->AddUC(cb);
    }
    // Restore pushed lemmas for liveness reuse.
    for (const Cube &cb : m_lfm.BorderCubes(m_k + 1)) {
        m_startSolver->AddUC(cb);
    }
}

bool IC3::Check() {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_Check");

    if (!m_initialized) {
        Init();
        LOG_L(m_log, 2, "Initialized");
    } else {
        Reset();
        LOG_L(m_log, 2, "Reset");
    }

    // check if initial state is bad
    if (ImmediateSatisfiable()) return false;

    // The main IC3 loop.
    while (true) {
        Extend();
        LOG_L(m_log, 2, "==================== k = ", m_k, " ====================");

        if (!Strengthen()) {
            LOG_L(m_log, 2, "UNSAFE: CEX found during strengthening of F_", m_k);
            return false;
        }

        if (PropagateFrame()) {
            LOG_L(m_log, 1, "SAFE: Proof found at F_", m_invariantLevel);
            LOG_L(m_log, 1, FramesInfo());
            return true;
        }

        LOG_L(m_log, 1, FramesInfo());
        m_k++;
    }

    return true; // Should be unreachable
}


void IC3::Init() {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_Init");

    // start solver search state in frame k
    // Use the successor image as explicit F_0.
    m_k = m_searchFromInitSucc ? 0 : 1;
    m_lfm.Reset();
    m_transSolvers.clear();
    m_obligations.clear();

    if (m_searchFromInitSucc) {
        m_initStateImplyBad = IsInitStateImplyBad();
        if (!m_initStateImplyBad)
            LOG_L(m_log, 1, "Initial state does not imply bad");
    }

    // initial states
    Cube init_latches;
    if (m_customInit.empty())
        init_latches = m_model.GetInitialState();
    else
        init_latches = m_customInit;
    m_initialState = std::make_shared<State>(nullptr, Cube{}, init_latches, 0);
    m_initialStateSet.clear();
    m_initialStateSet.insert(init_latches.begin(), init_latches.end());

    m_invariantLevel = 0;
    m_branching = std::make_shared<Branching>(m_settings.branching);
    m_litOrder.branching = m_branching;

    // create frame 0
    AddNewFrame();

    // lift
    m_liftSolver = std::make_shared<SATSolver>(m_model, m_settings.solver);
    if (m_settings.satSolveInDomain) m_liftSolver->SetSolveInDomain();
    m_liftSolver->AddTrans();
    m_liftSolver->SetDomainCOI(m_model.GetConstraints());

    InitializeInitSolver();
    InitializeBadLiftSolver();

    if (!m_searchFromInitSucc) {
        // Keep successor-image F_0 refinable.
        auto &frame_zero = m_transSolvers[0];
        for (const auto &lit : m_initialStateSet) {
            frame_zero->AddUC(Cube{~lit});
        }
    }

    m_initialized = true;
}


void IC3::InitializeStartSolver() {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_InitStart");
    if (m_settings.searchFromBadPred) {
        // s & T & c & P & T' & c' & bad'
        m_startSolver = std::make_shared<SATSolver>(m_model, MCSATSolver::cadical);
        m_startSolver->AddTrans();
        m_startSolver->AddConstraints();
        m_startSolver->AddTransK(1);
        m_startSolver->AddBadk(1);
        m_startSolver->AddProperty();
        m_startSolver->AddConstraintsK(1);
    } else {
        // s & c & bad
        m_startSolver = std::make_shared<SATSolver>(m_model, m_settings.solver);
        if (m_settings.satSolveInDomain &&
            m_shoals.empty() && m_dead.empty() && m_walls.empty()) {
            m_startSolver->SetSolveInDomain();
        }
        m_startSolver->AddTrans();
        m_startSolver->AddConstraints();
        if (m_loopRefuting) {
            for (auto lit : m_initialState->latches) m_startSolver->AddClause({lit});
        } else {
            m_startSolver->AddBad();
        }
        m_startSolver->SetDomainCOI(m_model.GetConstraints());
        m_startSolver->SetDomainCOI({m_model.GetBad()});
        // liveness: T = T & !C'
        //           T = T & ( W <-> W' )
        m_startSolver->AddShoalConstraints(m_shoals, m_dead);
        m_startSolver->AddWallConstraints(m_walls);
    }
}


void IC3::InitializeInitSolver() {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_InitImage");
    m_initSolver = std::make_shared<SATSolver>(m_model, m_settings.solver);
    if (m_settings.satSolveInDomain &&
        m_shoals.empty() && m_dead.empty() && m_walls.empty()) {
        m_initSolver->SetSolveInDomain();
    }
    m_initSolver->AddTrans();
    m_initSolver->AddConstraints();
    if (m_loopRefuting) m_initSolver->AddWallConstraints(m_walls);
    m_initSolver->AddShoalConstraints(m_shoals, m_dead);

    for (Lit lit : m_initialState->latches) {
        m_initSolver->AddUC(Cube{~lit});
    }
    if (m_searchFromInitSucc && !m_initStateImplyBad) {
        m_initSolver->AddBad();
        m_initSolver->SetDomainCOI(Cube{m_model.GetBad()});
    }
}


void IC3::InitializeBadLiftSolver() {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_InitBadLift");
    if (m_settings.searchFromBadPred) {
        m_badLiftSolver = std::make_shared<SATSolver>(m_model, MCSATSolver::cadical);
        m_badLiftSolver->AddTrans();
        m_badLiftSolver->AddTransK(1);
        m_shoalsLabels.clear();
        m_wallsLabels.clear();
        return;
    }

    m_badLiftSolver = std::make_shared<SATSolver>(m_model, m_settings.solver);
    if (m_settings.satSolveInDomain &&
        m_shoals.empty() && m_dead.empty() && m_walls.empty()) {
        m_badLiftSolver->SetSolveInDomain();
    }
    m_badLiftSolver->AddTrans();
    m_badLiftSolver->SetDomainCOI(m_model.GetConstraints());
    m_badLiftSolver->SetDomainCOI({m_model.GetBad()});
    m_shoalsLabels = m_badLiftSolver->AddShoalConstraintsAsLabels(m_shoals, m_dead);
    m_wallsLabels = m_badLiftSolver->AddWallConstraintsAsLabels(m_walls);
}


void IC3::Reset() {
    m_obligations.clear();
    m_cexStart = nullptr;
    m_cexTrace.clear();
    InitializeInitSolver();
    InitializeBadLiftSolver();
}


void IC3::AddNewFrame() {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_AddFrame");
    int level = static_cast<int>(m_transSolvers.size());
    LOG_L(m_log, 2, "Adding new frame F_", level);

    m_lfm.EnsureLevel(level);

    auto solver = std::make_shared<SATSolver>(m_model, m_settings.solver);
    if (m_settings.satSolveInDomain) solver->SetSolveInDomain();
    solver->AddTrans();
    solver->AddConstraints();
    if (m_loopRefuting) solver->AddWallConstraints(m_walls);
    m_transSolvers.push_back(solver);
}


void IC3::AddLemmaToSolvers(const Cube &blockingCube, int beginLevel, int endLevel) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_AddUC");
    // add lemma to trans solvers
    for (int i = beginLevel; i <= endLevel; ++i) {
        m_transSolvers[i]->AddUC(blockingCube);
    }

    // add lemma to start solver
    if (endLevel >= m_k) {
        m_startSolver->AddUC(blockingCube);
    }
}


int IC3::AddLemma(const Cube &blockingCube, int frameLevel, bool fromCTI) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_AddLemma");
    // add lemma to lemma forest
    auto res = m_lfm.AddLemma(blockingCube, frameLevel);

    // add lemma to solvers
    AddLemmaToSolvers(blockingCube, res.beginLevel, res.endLevel);

    // update minUpdateLevel
    // Skip the implicit initial frame.
    int min_update_level = m_searchFromInitSucc ? 0 : 1;
    int update_level = std::max(res.beginLevel, min_update_level);
    if (update_level < m_minUpdateLevel) m_minUpdateLevel = update_level;

    // active lemma learning
    if (fromCTI && m_settings.activeLemmaLearning) {
        ActiveLemmaLearning(res.lemmaId);
    }
    return res.lemmaId;
}

void IC3::ActiveLemmaLearning(int newLemmaId) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_ALL");
    auto ancestor_chain = m_lfm.GetAncestorChain(newLemmaId);
    if (ancestor_chain.empty()) return;

    auto hot_spots = FindHotSpots(ancestor_chain);

    for (int hotspot_lemma_id : hot_spots) {
        if (!m_lfm.Alive(hotspot_lemma_id) ||
            m_lfm.Reachable(hotspot_lemma_id)) continue;

        m_allPushAttempted++;
        m_lfm.ResetRefineCountSinceALL(hotspot_lemma_id);

        auto status = ActiveProve(hotspot_lemma_id);

        if (status == ALLProveStatus::Invalidated) {
            m_allStatusInvalidated++;
            continue;
        }
        if (status == ALLProveStatus::Bailout) {
            m_allStatusBailout++;
            continue;
        }
        if (status == ALLProveStatus::Reachable) {
            m_allStatusReachable++;
            m_lfm.MarkReachableChain(hotspot_lemma_id);
            continue;
        }

        assert(status == ALLProveStatus::Proved);
        m_allStatusProved++;

        if (!m_lfm.Alive(hotspot_lemma_id)) continue;

        const int frame_level = m_lfm.FrameLevelOf(hotspot_lemma_id);
        PropagateUp(hotspot_lemma_id, frame_level);
    }
}

std::vector<int> IC3::FindHotSpots(const std::vector<int> &ancestorChain) {
    std::vector<int> hot_spots;
    for (int lemma_id : ancestorChain) {
        if (m_lfm.Reachable(lemma_id)) break;
        if (m_lfm.RefineCountSinceALL(lemma_id) >= m_settings.allThreshold) {
            hot_spots.push_back(lemma_id);
        }
    }
    std::reverse(hot_spots.begin(), hot_spots.end());
    return hot_spots;
}

IC3::ALLProveStatus IC3::ActiveProve(int targetLemmaId) {
    int attempts_left = m_settings.allMaxStates;

    while (true) {
        if (!m_lfm.Alive(targetLemmaId)) return ALLProveStatus::Invalidated;

        int goal_level = m_lfm.FrameLevelOf(targetLemmaId);
        if (goal_level < 1 || goal_level >= static_cast<int>(m_transSolvers.size())) {
            return ALLProveStatus::Invalidated;
        }

        const Cube goal_cube = m_lfm.CubeOf(targetLemmaId);

        if (!m_lfm.HasCTPPreds(targetLemmaId)) {
            if (!IsReachable(goal_cube, m_transSolvers[goal_level])) {
                return ALLProveStatus::Proved;
            }
            if (attempts_left <= 0) return ALLProveStatus::Bailout;

            auto ctp_assignment = m_transSolvers[goal_level]->GetAssignment(false);
            auto ctp_state = std::make_shared<State>(nullptr, ctp_assignment.first, ctp_assignment.second, 0);
            auto succ_state = std::make_shared<State>(nullptr, Cube{}, goal_cube, 0);
            GeneralizePredecessor(ctp_state, succ_state);
            m_lfm.PushCTPPred(targetLemmaId, ctp_state->latches, goal_level);
        }

        if (attempts_left <= 0) return ALLProveStatus::Bailout;

        Cube ctp_cube;
        int ctp_level = -1;
        if (!m_lfm.PopCTPPred(targetLemmaId, ctp_cube, ctp_level)) {
            continue;
        }
        attempts_left--;

        if (ctp_level < 1 || ctp_level >= static_cast<int>(m_transSolvers.size())) {
            return ALLProveStatus::Invalidated;
        }

        if (GetSubsumeLevel(ctp_cube, ctp_level) != -1) {
            continue;
        }

        auto ctp_solver = m_transSolvers[ctp_level - 1];
        Cube ctp_cube_sorted(ctp_cube);
        OrderAssumption(ctp_cube_sorted);
        if (IsInductive(ctp_cube_sorted, ctp_solver)) {
            auto ctp_core = GetAndValidateCore(ctp_solver, ctp_cube);
            Generalize(ctp_core, ctp_level - 1, 0);
            int ctp_lemma_id = AddLemma(ctp_core, ctp_level);
            PropagateUp(ctp_lemma_id, ctp_level);
            continue;
        }

        if (ctp_level == 1) return ALLProveStatus::Reachable;

        m_lfm.PushCTPPred(targetLemmaId, ctp_cube, ctp_level);
        auto new_ctp_assignment = ctp_solver->GetAssignment(false);
        auto new_ctp_state = std::make_shared<State>(nullptr, new_ctp_assignment.first, new_ctp_assignment.second, 0);
        auto pred_succ_state = std::make_shared<State>(nullptr, Cube{}, ctp_cube, 0);
        GeneralizePredecessor(new_ctp_state, pred_succ_state);
        m_lfm.PushCTPPred(targetLemmaId, new_ctp_state->latches, ctp_level - 1);
    }
}


void IC3::PrintALLStats() const {
    if (!m_settings.activeLemmaLearning) return;
    m_log.L("ALL stats: pushAttempted=", m_allPushAttempted,
            ", statusProved=", m_allStatusProved,
            ", statusReachable=", m_allStatusReachable,
            ", statusBailout=", m_allStatusBailout,
            ", statusInvalidated=", m_allStatusInvalidated);
}


Cube IC3::GetUnsatCore(const std::shared_ptr<SATSolver> &solver, const Cube &fallbackCube, bool prime) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_UCore");
    Cube core;
    if (!prime) {
        for (const auto &lit : fallbackCube) {
            if (solver->Failed(lit)) {
                core.push_back(lit);
            }
        }
        return core;
    } else {
        for (const auto &lit : fallbackCube) {
            Lit lit_p = m_model.LookupPrime(lit);
            if (solver->Failed(lit_p)) {
                core.push_back(lit);
            }
        }
        return core;
    }
}


std::shared_ptr<State> IC3::EnumerateStartState() {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_StartEnum");
    LOG_L(m_log, 2, "Searching for a start state at level ", m_k);
    bool sat = false;
    {
        [[maybe_unused]] auto sat_scope = m_log.Section("SAT_Start");
        sat = m_startSolver->Solve();
    }
    if (sat) {
        if (m_loopRefuting) {
            std::shared_ptr<State> bad_state(new State(nullptr, {}, m_customInit, 0));
            return bad_state;
        }

        auto p = m_startSolver->GetAssignment(false);

        if (m_settings.searchFromBadPred) {
            // start state is the predecessor of a bad state
            Cube inputs_prime;
            for (int i : m_model.GetPropertyCOIInputs()) {
                Lit i_p = m_model.EnsurePrimeK(MkLit(i), 1);
                if (m_startSolver->GetModel(VarOf(i_p)) == T_TRUE)
                    inputs_prime.push_back(i_p);
                else if (m_startSolver->GetModel(VarOf(i_p)) == T_FALSE)
                    inputs_prime.push_back(~i_p);
            }

            // (p) & input & T & input' & T' -> (bad' & c' & c)
            // (p) & input & T & input' & T' & (!bad' | !c' | !c) is unsat
            Cube partial_latch = p.second;

            // (!bad' | !c' | !c)
            Clause cls;
            cls.push_back(~m_model.EnsurePrimeK(m_model.GetBad(), 1));
            for (auto cons : m_model.GetConstraints())
                cls.push_back(~m_model.EnsurePrimeK(cons, 1));
            for (auto cons : m_model.GetConstraints())
                cls.push_back(~cons);
            m_badLiftSolver->AddTempClause(cls);

            int gen_tried = 0;

            while (true) {
                Cube assumption;
                std::copy(partial_latch.begin(), partial_latch.end(), std::back_inserter(assumption));
                OrderAssumption(assumption);

                if (gen_tried == 1) std::reverse(assumption.begin(), assumption.end());
                if (gen_tried > 1) std::random_shuffle(assumption.begin(), assumption.end());
                gen_tried++;

                std::copy(p.first.begin(), p.first.end(), std::back_inserter(assumption));
                std::copy(inputs_prime.begin(), inputs_prime.end(), std::back_inserter(assumption));

                bool res;
                {
                    [[maybe_unused]] auto sat_bad_pred = m_log.Section("SAT_BadLift");
                    res = m_badLiftSolver->Solve(assumption);
                }
                assert(!res);
                Cube temp_p = GetUnsatCore(m_badLiftSolver, partial_latch, false);
                if (temp_p.size() >= partial_latch.size())
                    break;
                else {
                    partial_latch.swap(temp_p);
                }
            }
            m_badLiftSolver->ReleaseTempClause();
            p.second = partial_latch;

            Cube inputs_bad;
            for (int i : m_model.GetPropertyCOIInputs()) {
                Lit i_p = m_model.EnsurePrimeK(MkLit(i), 1);
                if (m_startSolver->GetModel(VarOf(i_p)) == T_TRUE)
                    inputs_bad.push_back(MkLit(i));
                else if (m_startSolver->GetModel(VarOf(i_p)) == T_FALSE)
                    inputs_bad.push_back(~MkLit(i));
            }
            std::shared_ptr<State> bad_state(new State(nullptr, inputs_bad, Cube(), 0));
            std::shared_ptr<State> bad_pred_state(new State(bad_state, p.first, p.second, 0));
            return bad_pred_state;
        } else {
            // start state is a bad state
            // (p) -> (bad & c)
            // (p) & (!bad | !c) is unsat
            Cube partial_latch = p.second;
            LOG_L(m_log, 3, "Bad State Latches Before Lifting: ", CubeToStr(partial_latch));

            // (!bad | !c)
            Clause cls;
            cls.push_back(~m_model.GetBad());
            for (auto cons : m_model.GetConstraints())
                cls.push_back(~cons);
            for (auto l : m_shoalsLabels) cls.push_back(~l);
            for (auto l : m_wallsLabels) cls.push_back(~l);
            m_badLiftSolver->AddTempClause(cls);
            LOG_L(m_log, 3, "lift assume: ", CubeToStr(cls));

            int gen_tried = 0;

            while (true) {
                Cube assumption;
                std::copy(partial_latch.begin(), partial_latch.end(), std::back_inserter(assumption));
                OrderAssumption(assumption);

                if (gen_tried == 1) std::reverse(assumption.begin(), assumption.end());
                if (gen_tried > 1) std::random_shuffle(assumption.begin(), assumption.end());
                gen_tried++;

                std::copy(p.first.begin(), p.first.end(), std::back_inserter(assumption));

                bool res;
                {
                    [[maybe_unused]] auto sat_bad_pred = m_log.Section("SAT_BadLift");
                    res = m_badLiftSolver->Solve(assumption);
                }
                assert(!res);
                Cube temp_p = GetUnsatCore(m_badLiftSolver, partial_latch, false);
                if (temp_p.size() >= partial_latch.size())
                    break;
                else {
                    partial_latch.swap(temp_p);
                }
            }
            m_badLiftSolver->ReleaseTempClause();
            p.second = partial_latch;

            std::shared_ptr<State> bad_state(new State(nullptr, p.first, p.second, 0));
            return bad_state;
        }
    } else {
        return nullptr;
    }
}

bool IC3::Strengthen() {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_Strengthen");
    m_minUpdateLevel = m_k;

    while (true) {
        if (!HandleObligations()) {
            return false;
        }

        std::shared_ptr<State> start_state = EnumerateStartState();
        if (start_state != nullptr) {
            AddObligation(start_state, m_k - 1, 1);
        } else {
            LOG_L(m_log, 2, "No more CTIs at level ", m_k, ". Frame is strengthened.");
            return true;
        }
    }
}


// ================================================================================
// @brief: Get a frame level where cb is subsumed
// @input:
// @output: -1 if not subsumed
// ================================================================================
int IC3::GetSubsumeLevel(const Cube &cb, int startLvl) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_Subsumed");
    if (startLvl < 0) startLvl = 0;
    if (startLvl > m_k + 1) return -1;

    for (int lvl = startLvl; lvl <= m_k + 1; ++lvl) {
        if (m_lfm.IsBlockedAtLevel(cb, lvl)) {
            return lvl;
        }
    }
    return -1;
}

ObligationRef IC3::AddObligation(std::shared_ptr<State> state, int level, int depth, double act) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_AddPO");
    auto ob = std::make_shared<Obligation>(state, level, depth, act);
    m_obligations.insert(ob);
    return ob;
}

bool IC3::PopObligation(ObligationRef &ob) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_PopPO");
    while (!m_obligations.empty()) {
        auto it = m_obligations.begin();
        if ((*it)->level > m_k) return false;

        ob = *it;
        m_obligations.erase(it);
        return true;
    }
    return false;
}


void IC3::PushObligation(const ObligationRef &ob, int newLevel) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_PushPO");
    while (ob->level < newLevel) {
        ob->level++;
        ob->act *= 0.6;
    }
    m_obligations.insert(ob);
}


bool IC3::HandleObligations() {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_HandlePO");
    auto handle_f0_candidate = [&](const std::shared_ptr<State> &candidate,
                                   int initial_depth) {
        if (!IsInitSuccessor(candidate->latches)) {
            Cube image_core = GetUnsatCore(m_initSolver,
                                           candidate->latches,
                                           true);
            LOG_L(m_log, 2, "Refining successor-image F_0 with core: ",
                  CubeToStr(image_core));
            AddLemma(image_core, 0);
            return false;
        }

        auto init_assignment = m_initSolver->GetAssignment(false);
        m_cexStart = std::make_shared<State>(candidate,
                                             init_assignment.first,
                                             init_assignment.second,
                                             initial_depth);
        return true;
    };

    ObligationRef ob;
    while (PopObligation(ob)) {
        int subsume_lvl = GetSubsumeLevel(ob->state->latches, ob->level + 1);
        if (subsume_lvl != -1) {
            LOG_L(m_log, 2, "Obligation at level ", ob->level + 1, " depth ", ob->depth, " is subsumed at level ", subsume_lvl, ". Skipped.");
            PushObligation(ob, subsume_lvl);
            continue;
        }

        if (++ob->act > m_k / 10.0 + m_settings.maxObligationAct) {
            LOG_L(m_log, 2, "Obligation at level ", ob->level, " depth ", ob->depth, " reached max activity. Skipped.");
            continue;
        }

        if (m_searchFromInitSucc && ob->level < 0) {
            if (handle_f0_candidate(ob->state, ob->depth + 1)) {
                LOG_L(m_log, 2, "UNSAFE: F_0 candidate is an actual initial successor.");
                return false;
            }
            continue;
        }

        // Query: F_{ob.level} & T & cti'
        LOG_L(m_log, 2, "Handling obligation at level ", ob->level);

        auto &trans_slv = m_transSolvers[ob->level];
        auto &cti_cube = ob->state->latches;
        Cube cti_cube_sorted(cti_cube);
        OrderAssumption(cti_cube_sorted);

        if (!IsReachable(cti_cube_sorted, trans_slv)) {
            auto uc = GetAndValidateCore(trans_slv, cti_cube);
            Generalize(uc, ob->level);
            int lemma_id = AddLemma(uc, ob->level + 1, true);
            int push_level = PropagateUp(lemma_id, ob->level + 1);

            LOG_L(m_log, 2, "Creating new obligation for same state at higher level ", push_level);
            PushObligation(ob, push_level);
        } else {
            auto p = trans_slv->GetAssignment(false);
            auto predecessor_state =
                std::make_shared<State>(ob->state, p.first, p.second, ob->depth + 1);

            if (ob->level == 0) {
                if (m_searchFromInitSucc) {
                    if (handle_f0_candidate(predecessor_state, ob->depth + 2)) {
                        LOG_L(m_log, 2, "UNSAFE: Found a path from an actual initial successor.");
                        return false;
                    }
                    m_obligations.insert(ob);
                    continue;
                }

                LOG_L(m_log, 2, "UNSAFE: Found a path from the initial state.");
                m_cexStart = predecessor_state;
                return false;
            }

            GeneralizePredecessor(predecessor_state, ob->state);

            int old_level = ob->level;
            int old_depth = ob->depth;
            LOG_L(m_log, 2, "Found predecessor for CTI. New obligation at level ", old_level - 1);
            PushObligation(ob, old_level);
            AddObligation(predecessor_state, old_level - 1, old_depth + 1);
        }
    }
    return true;
}

bool IC3::IsInductive(const Cube &cb, const std::shared_ptr<SATSolver> &slv) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_IsInd");
    Clause cls;
    cls.reserve(cb.size());
    for (const auto &lit : cb) {
        cls.push_back(~lit);
    }

    slv->AddTempClause(cls);
    Cube assumption(cb);
    GetPrimed(assumption);
    slv->SetTempDomainCOI(assumption);
    bool res;
    {
        [[maybe_unused]] auto sat_scope = m_log.Section("SAT_Ind");
        res = !slv->Solve(assumption);
    }
    slv->ReleaseTempClause();
    return res;
}


static bool LitTrueInModel(const std::shared_ptr<SATSolver> &solver, Lit lit) {
    Tbool val = solver->GetModel(VarOf(lit));
    if (val == T_UNDEF) return false;

    return Sign(lit) ? val == T_FALSE : val == T_TRUE;
}


bool IC3::Down(Cube &downCube, int frameLvl, int recLvl, const LitSet &triedLits, const Cube &fullCube, std::vector<std::pair<LitSet, LitSet>> &cexCache) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_Down");
    LOG_L(m_log, 3, "Down: ", CubeToStr(downCube), " at frame level ", frameLvl, " and recursion level ", recLvl);
    int ctgs = 0;
    int joins = 0;
    LitSet ctg_lits;
    auto &trans_slv = m_transSolvers[frameLvl];

    while (true) {
        LOG_L(m_log, 3, "Down attempt: ", CubeToStr(downCube));

        // initial state inclusion check
        if (!InitiationCheck(downCube)) {
            return false;
        }

        // cex cache check
        for (const auto &[s, t] : cexCache) {
            if (!SubsumeSet(downCube, s) && SubsumeSet(downCube, t)) {
                return false;
            }
        }

        // inductive check
        if (IsInductive(downCube, trans_slv)) {
            Cube down_core = GetAndValidateCore(trans_slv, downCube);
            downCube.swap(down_core);
            return true;
        }

        // plain join down
        if (recLvl >= m_settings.ctgMaxRecursionDepth) {
            Cube cube_new;
            bool keep_conflict = false;

            for (Lit lit : downCube) {
                bool lit_true = LitTrueInModel(trans_slv, lit);

                if (triedLits.Has(lit) && !lit_true) {
                    keep_conflict = true;
                    break;
                }

                if (lit_true) cube_new.push_back(lit);
            }

            LitSet s;
            LitSet t;
            for (Lit lit : fullCube) {
                Lit base_lit = MkLit(VarOf(lit));

                Tbool val = trans_slv->GetModel(VarOf(lit));
                if (val == T_TRUE) {
                    s.Insert(base_lit);
                } else if (val == T_FALSE) {
                    s.Insert(~base_lit);
                }

                Lit lit_p = m_model.LookupPrime(lit);
                Tbool val_p = trans_slv->GetModel(VarOf(lit_p));
                if (val_p == T_TRUE) {
                    t.Insert(base_lit);
                } else if (val_p == T_FALSE) {
                    t.Insert(~base_lit);
                }
            }
            cexCache.emplace_back(std::move(s), std::move(t));

            if (keep_conflict) return false;
            if (cube_new.size() == downCube.size()) return false;

            downCube.swap(cube_new);
            continue;
        }

        for (Lit lit : downCube) {
            if (!triedLits.Has(lit)) continue;

            if (!LitTrueInModel(trans_slv, lit)) return false;
        }

        // ctg down
        std::shared_ptr<State> down_state = std::make_shared<State>(nullptr, Cube(), downCube, 0);
        auto p = trans_slv->GetAssignment(false);
        auto ctg_state = std::make_shared<State>(down_state, p.first, p.second, 0);
        GeneralizePredecessor(ctg_state, down_state);

        const Cube &ctg_cube = ctg_state->latches;
        LOG_L(m_log, 3, "CTG Cube: ", CubeToStr(ctg_cube));

        if (!InitiationCheck(ctg_cube)) return false;

        if (ctgs < m_settings.ctgMaxCTG && frameLvl > 0) {
            int block_limit = m_settings.ctgMaxBlocks;
            if (ExCTGBlock(ctg_cube, frameLvl - 1, recLvl + 1, block_limit)) {
                ctgs++;
                LOG_L(m_log, 3, "EXCTG blocked CTG cube at level ", frameLvl - 1);
                continue;
            }
        }
        ctgs = 0;
        ctg_lits.NewSet(ctg_cube);
        Cube join_cube;
        for (size_t i = 0; i < downCube.size(); i++) {
            if (ctg_lits.Has(downCube[i])) {
                join_cube.push_back(downCube[i]);
            } else if (triedLits.Has(downCube[i])) {
                return false;
            }
        }
        LOG_L(m_log, 3, "Joint Cube: ", CubeToStr(join_cube));
        downCube.swap(join_cube);
    }
}


bool IC3::ExCTGBlock(const Cube &cb, int frameLvl, int recLvl, int blockLimit) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_ExCTG");
    if (!InitiationCheck(cb)) return false;

    Cube assumption(cb);
    OrderAssumption(assumption);

    while (true) {
        if (IsInductive(assumption, m_transSolvers[frameLvl])) {
            Cube core = GetAndValidateCore(m_transSolvers[frameLvl], cb);
            Generalize(core, frameLvl, recLvl);

            int lemma_id = AddLemma(core, frameLvl + 1);
            PropagateUp(lemma_id, frameLvl + 1);
            return true;
        }

        if (frameLvl <= 0 || blockLimit <= 1) return false;

        auto p = m_transSolvers[frameLvl]->GetAssignment(false);
        auto succ = std::make_shared<State>(nullptr, Cube(), cb, 0);
        auto pred = std::make_shared<State>(succ, p.first, p.second, 0);
        GeneralizePredecessor(pred, succ);

        if (!ExCTGBlock(pred->latches, frameLvl - 1, recLvl, blockLimit - 1)) {
            return false;
        }
    }
}


void IC3::Generalize(Cube &cb, int frameLvl, int recLvl) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_Gen");

    if (m_settings.mlqp > 0) {
        auto &solver = m_transSolvers[frameLvl];
        bool reduced;
        {
            [[maybe_unused]] auto mlqp_scope = m_log.Section("IC3_MLQP");
            OrderAssumption(cb);
            Cube core_assumps(cb);
            GetPrimed(core_assumps);
            solver->SetTempDomainCOI(core_assumps);
            reduced = solver->MLQP(core_assumps, m_settings.mlqp);
        }
        if (reduced) {
            Cube core = GetAndValidateCore(solver, cb);
            if (core.size() < cb.size()) cb.swap(core);
        }
    }

    LOG_L(m_log, 3, "Generalizing Cube: ", CubeToStr(cb), ", at frameLvl: ", frameLvl, ", recLvl: ", recLvl);

    Cube blocker;
    LitSet tried_lits;
    std::vector<std::pair<LitSet, LitSet>> cex_cache;

    m_lfm.GetParentCube(cb, frameLvl, blocker);
    if (m_settings.referSkipping) {
        for (const auto &lit : blocker) {
            tried_lits.Insert(lit);
        }
    }

    bool limited_attempts = m_settings.genMaxFail > 0;
    int attempts = m_settings.genMaxFail;

    OrderAssumption(cb);
    // Iterate backwards to handle the shrinking Cube size gracefully.
    for (int i = cb.size() - 1; i >= 0; --i) {
        if (cb.size() < 3) break;
        Lit lit_to_drop = cb[i];

        // If we have already tried and failed to drop this literal, skip.
        if (tried_lits.Has(lit_to_drop)) {
            continue;
        }

        // Create a temporary Cube with one literal removed.
        Cube drop_cube;
        drop_cube.reserve(cb.size() - 1);
        for (int j = 0; j < cb.size(); ++j) {
            if (i == j) continue;
            drop_cube.push_back(cb[j]);
        }

        if (Down(drop_cube, frameLvl, recLvl, tried_lits, cb, cex_cache)) {
            // dropCube is sorted
            cb.swap(drop_cube);
            i = cb.size();
            if (limited_attempts) attempts = m_settings.genMaxFail;
        } else {
            if (limited_attempts && --attempts == 0) break;
            tried_lits.Insert(lit_to_drop);
        }
    }

    std::sort(cb.begin(), cb.end());
    if (cb.size() <= blocker.size() || frameLvl == 0) {
        m_branching->Update(cb);
    }
}


void IC3::GeneralizePredecessor(const std::shared_ptr<State> &predecessorState, const std::shared_ptr<State> &successorState) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_GenPred");
    LOG_L(m_log, 3, "Generalizing predecessor. Initial latch size: ", predecessorState->latches.size(), ", input size: ", predecessorState->inputs.size(), ", Successor state latch size: ", successorState->latches.size());

    Clause succ_negation_clause;
    succ_negation_clause.reserve(successorState->latches.size());
    for (const auto &lit : successorState->latches) {
        succ_negation_clause.push_back(~m_model.LookupPrime(lit));
    }
    for (auto cons : m_model.GetConstraints()) {
        succ_negation_clause.push_back(~cons);
    }
    m_liftSolver->AddTempClause(succ_negation_clause);
    m_liftSolver->SetTempDomainCOI(succ_negation_clause);

    auto &partial_latch = predecessorState->latches;

    while (true) {
        Cube assumption(partial_latch);
        OrderAssumption(assumption);
        assumption.insert(assumption.begin(), predecessorState->inputs.begin(), predecessorState->inputs.end());
        // There exist some successors whose predecessors are the entire set. (All latches are determined solely by the inputs.)

        bool result;
        {
            [[maybe_unused]] auto sat_lift = m_log.Section("SAT_Lift");
            result = m_liftSolver->Solve(assumption);
        }
        assert(!result);

        auto core = GetUnsatCore(m_liftSolver, partial_latch, false);
        LOG_L(m_log, 3, "Core size: ", core.size(), ", Partial latch size: ", partial_latch.size());

        if (core.size() == 0) break;
        if (core.size() >= partial_latch.size()) {
            break;
        } else {
            partial_latch.swap(core);
        }
    }
    m_liftSolver->ReleaseTempClause();
    LOG_L(m_log, 3, "Generalized predecessor. Final latch size: ", predecessorState->latches.size());
}

bool IC3::InitiationCheck(const Cube &cb) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_InitChk");
    if (m_searchFromInitSucc) {
        return !IsInitSuccessor(cb);
    }

    for (const auto &lit : cb) {
        if (m_initialStateSet.count(~lit)) {
            return true; // Disjoint (UNSAT), check passes.
        }
    }
    LOG_L(m_log, 3, "Initiation check failed.");
    return false;
}


bool IC3::IsInitSuccessor(const Cube &cb) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_IsInitSucc");

    assert(m_searchFromInitSucc);
    assert(m_initSolver);

    Cube assumptions(cb);
    GetPrimed(assumptions);
    m_initSolver->SetTempDomainCOI(assumptions);

    return m_initSolver->Solve(assumptions);
}


Cube IC3::GetAndValidateCore(const std::shared_ptr<SATSolver> &solver, const Cube &fallbackCube) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_ValidCore");
    // fallbackCube is sorted
    Cube core = GetUnsatCore(solver, fallbackCube, true);
    LOG_L(m_log, 3, "Got UNSAT core: ", CubeToStr(core));

    if (InitiationCheck(core)) {
        return core;
    }

    if (m_searchFromInitSucc) {
        return fallbackCube;
    }

    LOG_L(m_log, 3, "GetAndValidateCore: core intersects with initial states. Repairing core.");

    Lit init_blocking_lit{};
    bool found = false;
    for (Lit lit : fallbackCube) {
        if (m_initialStateSet.count(~lit)) {
            init_blocking_lit = lit;
            found = true;
            break;
        }
    }

    if (!found) {
        LOG_L(m_log, 3, "GetAndValidateCore: no init-blocking literal found in fallback Cube. Reverting to fallback Cube.");
        return fallbackCube;
    }

    Cube repaired;
    repaired.reserve(core.size() + 1);
    for (Lit lit : fallbackCube) {
        Lit lit_p = m_model.LookupPrime(lit);
        if (solver->Failed(lit_p) || lit == init_blocking_lit) {
            repaired.push_back(lit);
        }
    }

    assert(InitiationCheck(repaired));
    LOG_L(m_log, 3, "Repaired UNSAT core: ", CubeToStr(repaired));
    return repaired;
}


std::string IC3::FramesInfo() const {
    std::stringstream ss;
    ss << "Frames " << m_transSolvers.size() << std::endl;
    for (size_t i = 0; i < m_transSolvers.size(); ++i) {
        ss << m_lfm.BorderSize(static_cast<int>(i)) << " ";
    }
    return ss.str();
}


std::string IC3::FramesDetail() const {
    std::stringstream ss;
    ss << "Frames " << m_transSolvers.size() << std::endl;
    for (size_t i = 0; i < m_transSolvers.size(); ++i) {
        ss << "Frame " << i << ": " << std::endl;
        std::vector<int> lemmas_to_iterate = m_lfm.BorderIds(i);
        for (int lemma_id : lemmas_to_iterate) {
            if (!m_lfm.Alive(lemma_id) || m_lfm.Reachable(lemma_id)) continue;

            Cube cb = m_lfm.CubeOf(lemma_id);
            ss << CubeToStr(cb) << std::endl;
        }
    }
    return ss.str();
}


bool IC3::IsReachable(const Cube &cb, const std::shared_ptr<SATSolver> &slv) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_IsReach");
    Cube assumption(cb);
    GetPrimed(assumption);
    slv->SetTempDomainCOI(assumption);

    {
        [[maybe_unused]] auto sat_scope = m_log.Section("SAT_Reach");
        return slv->Solve(assumption);
    }
}


// ================================================================================
// @brief: ~cb is in F_i, check if F_i (& ~cb) & T & cb' is UNSAT?
// @input:
// @output:
// ================================================================================
bool IC3::Propagate(int lemmaId, int lvl) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_Prop");
    bool result;
    Cube cb = m_lfm.CubeOf(lemmaId);

    if (!IsReachable(cb, m_transSolvers[lvl])) {
        auto core = GetAndValidateCore(m_transSolvers[lvl], cb);
        if (core.size() < cb.size()) {
            AddLemma(core, lvl + 1);
        } else {
            int propagated_level = m_lfm.PropagateLemma(lemmaId, lvl + 1);
            AddLemmaToSolvers(cb, propagated_level, propagated_level);
        }
        m_branching->Update(core);
        result = true;
    } else {
        result = false;
    }
    return result;
}


int IC3::PropagateUp(int LemmaId, int startLevel) {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_PropUp");
    int lvl = startLevel;
    while (lvl <= m_k) {
        if (!m_lfm.Alive(LemmaId) || !Propagate(LemmaId, lvl))
            break;
        lvl++;
    }
    return lvl;
}


bool IC3::PropagateFrame() {
    [[maybe_unused]] auto scoped = m_log.Section("IC3_PropFrame");
    LOG_L(m_log, 2, "Propagating clauses.");

    for (int i = m_minUpdateLevel; i <= m_k; ++i) {
        int lemmas_kept = 0;
        int lemmas_propagated = 0;

        m_lfm.CleanDeadBorders(i);
        m_lfm.SortBorderByCubeSize(i);

        std::vector<int> lemmas_to_iterate = m_lfm.BorderIds(i);
        for (int lemma_id : lemmas_to_iterate) {
            if (!m_lfm.Alive(lemma_id) || m_lfm.Reachable(lemma_id)) continue;

            if (Propagate(lemma_id, i)) {
                lemmas_propagated++;
            } else {
                lemmas_kept++;
            }
        }

        LOG_L(m_log, 2, "Frame ", i, " propagation: ", lemmas_propagated, " propagated, ", lemmas_kept, " kept.");

        if (m_lfm.BorderEmpty(i)) {
            LOG_L(m_log, 2, "SAFE: Frame F_", i, " is empty.");
            m_invariantLevel = i + 1;
            LOG_L(m_log, 2, "m_invariantLevel: ", m_invariantLevel);
            LOG_L(m_log, 2, FramesInfo());
            return true; // Proof found
        }
    }

    return false;
}


void IC3::RefineWitnessPropertyLit(WitnessBuilder &builder) const {
    std::set<Cube, bool (*)(const Cube &, const Cube &)> ind_inv(CubeComp);
    for (int i = m_invariantLevel; i <= m_k + 1; ++i) {
        for (const Cube &cb : m_lfm.BorderCubes(i)) {
            ind_inv.insert(cb);
        }
    }

    Frame inv(ind_inv.begin(), ind_inv.end());
    if (m_settings.shrinkInvariant) inv = ShrinkInv(std::move(inv));
    std::vector<unsigned> clause_terms;
    clause_terms.reserve(inv.size());
    for (const Cube &cube : inv) {
        clause_terms.push_back(builder.Negate(builder.BuildCube(cube)));
    }
    unsigned invariant_lit = clause_terms.empty() ? builder.TrueLit() : builder.BuildAnd(clause_terms);
    builder.SetPropertyLit(builder.BuildAnd({builder.GetPropertyLit(), invariant_lit}));
}

} // namespace car
