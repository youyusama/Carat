#pragma once

#include "CarTypes.h"
#include "TernarySim.h"
#include <memory>
#include <vector>

namespace car {

class ISolver {
  public:
    virtual void AddClause(const Cube &cls) = 0;
    virtual bool Solve() = 0;
    virtual bool Solve(const Cube &assumption) = 0;
    virtual std::pair<Cube, Cube> GetAssignment(bool prime) = 0;
    virtual bool Failed(Lit assumption) = 0;
    virtual bool MLQP(const Cube &coreAssumptions, int strategy) { return false; }
    virtual Var GetNewVar() = 0;
    virtual void AddTempClause(const Cube &cls) = 0;
    virtual void ReleaseTempClause() = 0;
    virtual Tbool GetModel(Var id) = 0;

  private:
};

} // namespace car
