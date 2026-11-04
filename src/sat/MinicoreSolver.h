#pragma once

#include "ISolver.h"
#include "Model.h"
#include "minicore/src/solver.h"
#include <memory>

namespace car {

class MinicoreSolver : public ISolver, public minicore::Solver {
  public:
    MinicoreSolver(Model &m);
    ~MinicoreSolver();

    void AddClause(const Cube &cls) override;
    bool Solve() override;
    bool Solve(const Cube &assumption) override;
    std::pair<Cube, Cube> GetAssignment(bool prime) override;
    bool Failed(Lit assumption) override;
    bool MLQP(const Cube &coreAssumptions, int strategy) override;
    inline Var GetNewVar() override {
        return ++m_maxId;
    }
    void AddTempClause(const Cube &cls) override;
    void ReleaseTempClause() override;
    inline Tbool GetModel(Var id) override {
        if (value(id) == minicore::l_True)
            return T_TRUE;
        else if (value(id) == minicore::l_False)
            return T_FALSE;
        else
            return T_UNDEF;
    }
  protected:
    Model &m_model;
    Var m_maxId;
};

} // namespace car
