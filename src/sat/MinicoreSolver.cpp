#include "MinicoreSolver.h"
#include <algorithm>

namespace car {
MinicoreSolver::MinicoreSolver(Model &m) : m_model(m) {
    m_maxId = m_model.NumVar() + 1; // reserve variable numbers for one step reachability check
    // verbosity = 1;
}

MinicoreSolver::~MinicoreSolver() {}

bool MinicoreSolver::Solve() {
    return solve() == minicore::l_True;
}


bool MinicoreSolver::Solve(const Cube &assumption) {
    return solve(assumption) == minicore::l_True;
}


void MinicoreSolver::AddClause(const Cube &cls) {
    for (Lit l : cls) {
        if (VarOf(l) > m_maxId) m_maxId = VarOf(l) + 1;
        while (static_cast<int>(VarOf(l)) >= nVars()) newVar();
    }
    bool result = addClause(cls);
}


std::pair<Cube, Cube> MinicoreSolver::GetAssignment(bool prime) {
    Cube inputs;
    Cube latches;
    inputs.reserve(m_model.GetNumInputs());
    latches.reserve(m_model.GetNumLatches());
    for (Var i : m_model.GetModelInputs()) {
        if (value(static_cast<int>(i)) == minicore::l_True) {
            inputs.emplace_back(MkLit(i));
        } else if (value(static_cast<int>(i)) == minicore::l_False) {
            inputs.emplace_back(~MkLit(i));
        }
    }
    if (!prime) {
        for (Var i : m_model.GetModelLatches()) {
            if (value(static_cast<int>(i)) == minicore::l_True) {
                latches.emplace_back(MkLit(i));
            } else if (value(static_cast<int>(i)) == minicore::l_False) {
                latches.emplace_back(~MkLit(i));
            }
        }
        for (Var i : m_model.GetInnards()) {
            if (value(static_cast<int>(i)) == minicore::l_True) {
                latches.emplace_back(MkLit(i));
            } else if (value(static_cast<int>(i)) == minicore::l_False) {
                latches.emplace_back(~MkLit(i));
            }
        }
    } else {
        for (Var i : m_model.GetModelLatches()) {
            Lit p = m_model.LookupPrime(MkLit(i));
            minicore::lbool val = value(static_cast<int>(VarOf(p)));
            if ((val == minicore::l_True && !Sign(p)) || (val == minicore::l_False && Sign(p))) {
                latches.emplace_back(MkLit(i));
            } else if ((val == minicore::l_True && Sign(p)) || (val == minicore::l_False && !Sign(p))) {
                latches.emplace_back(~MkLit(i));
            }
        }
        for (Var i : m_model.GetInnards()) {
            Lit p = m_model.LookupPrime(MkLit(i));
            minicore::lbool val = value(static_cast<int>(VarOf(p)));
            if ((val == minicore::l_True && !Sign(p)) || (val == minicore::l_False && Sign(p))) {
                latches.emplace_back(MkLit(i));
            } else if ((val == minicore::l_True && Sign(p)) || (val == minicore::l_False && !Sign(p))) {
                latches.emplace_back(~MkLit(i));
            }
        }
    }
    return std::pair<Cube, Cube>(inputs, latches);
}


bool MinicoreSolver::Failed(Lit assumption) {
    return failed(assumption);
}


bool MinicoreSolver::MLQP(const Cube &coreAssumptions, int strategy) {
    return mlqp(coreAssumptions, strategy);
}


void MinicoreSolver::AddTempClause(const Cube &cls) {
#ifndef NDEBUG
    for (Lit l : cls) {
        assert(static_cast<int>(VarOf(l)) < nVars());
    }
#endif
    addTempClause(cls);
}


void MinicoreSolver::ReleaseTempClause() {
    releaseTempClause();
}

} // namespace car
