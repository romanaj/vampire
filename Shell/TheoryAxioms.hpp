/**
 * @file TheoryAxioms.hpp
 * Defines class TheoryAxioms.
 */

#ifndef __TheoryAxioms__
#define __TheoryAxioms__

#include "Forwards.hpp"

#include "Kernel/Theory.hpp"
#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class TheoryAxioms {
public:
  TheoryAxioms(Problem& prb) :
    _prb(prb)
  {} 

static unsigned const CHEAP = 0;
static unsigned const EXPENSIVE = 1;

  void apply();

  /**
   * There is a separate method for adding the FOOL domain axiom because unlike
   * for the other supported theories, reasoning in FOOL is complete, so we
   * want to be sure to always add the axiom when FOOL subexpressions are met,
   * which is a different condition that is used to apply axioms than the one,
   * used for the other theories.
   */
  void applyFOOL();

private:

  Problem& _prb;

  void addCommutativity(Interpretation op);
  void addAssociativity(Interpretation op);
  void addRightIdentity(Interpretation op, TermList idElement);
  void addLeftIdentity(Interpretation op, TermList idElement);
  void addCommutativeGroupAxioms(Interpretation op, Interpretation inverse, TermList idElement);

  void addRightInverse(Interpretation op, Interpretation inverse);

  void addNonReflexivity(Interpretation op);
  void addTransitivity(Interpretation op);
  void addOrderingTotality(Interpretation less);
  void addTotalOrderAxioms(Interpretation less);
  void addMonotonicity(Interpretation less, Interpretation addition);
  void addPlusOneGreater(Interpretation plus, TermList oneElement, Interpretation less);
  void addAdditionAndOrderingAxioms(Interpretation plus, Interpretation unaryMinus,
				    TermList zeroElement, TermList oneElement,
				    Interpretation less);
  void addAdditionOrderingAndMultiplicationAxioms(Interpretation plus, Interpretation unaryMinus,
						  TermList zeroElement, TermList oneElement,
						  Interpretation less, Interpretation multiply);
  void addExtraIntegerOrderingAxiom(Interpretation plus, TermList oneElement, Interpretation less);
  void addQuotientAxioms(Interpretation quotient, Interpretation multiply, TermList zeroElement, TermList oneElement,
                         Interpretation less);
  void addIntegerDivisionWithModuloAxioms(Interpretation plus, Interpretation unaryMinus, Interpretation less,
                                Interpretation multiply, Interpretation divide, Interpretation divides,
                                Interpretation modulo, Interpretation abs, TermList zeroElement,
                                TermList oneElement);
  void addIntegerAbsAxioms(Interpretation abs, Interpretation less,
                           Interpretation unaryMinus, TermList zeroElement);
  void addIntegerDividesAxioms(Interpretation divides, Interpretation multiply, TermList zero, TermList n);

  void addBooleanArrayExtensionalityAxioms(Interpretation select, Interpretation store, unsigned skolem);
  void addArrayExtensionalityAxioms(Interpretation select, Interpretation store, unsigned skolem);
  void addBooleanArrayWriteAxioms(Interpretation select, Interpretation store);
  void addTupleAxioms(unsigned tupleSort);
  void addFloorAxioms(Interpretation floor, Interpretation less, Interpretation unaryMinus,
                      Interpretation plus, TermList oneElement);
  void addCeilingAxioms(Interpretation ceiling, Interpretation less, Interpretation plus, 
                        TermList oneElement);
  void addRoundAxioms(Interpretation round, Interpretation floor, Interpretation ceiling); 
  void addTruncateAxioms(Interpretation truncate, Interpretation less, Interpretation unaryMinus,
                      Interpretation plus, TermList zeroElement, TermList oneElement);
  void addArrayWriteAxioms(Interpretation select, Interpretation store);

  // term algebra axioms
  void addExhaustivenessAxiom(TermAlgebra* ta);
  void addDistinctnessAxiom(TermAlgebra* ta);
  void addInjectivityAxiom(TermAlgebra* ta);
  void addDiscriminationAxiom(TermAlgebra* ta);
  void addCyclicityAxiom(TermAlgebra* ta);

  /* Subterm definitions used by the acyclicity axiom. */
  void addSubtermDefinitions(unsigned subtermPredicate, TermAlgebraConstructor* c);
  void addSubtermIrreflexivity(unsigned subtermPredicate);

  /* Same thing for the subst and cycle functions, used to axiomatize infinite trees (a.k.a. co-datatypes) */
  void addSubstFunctionDefinitions(unsigned substFunction, TermAlgebraConstructor* c);
  void addSubstFunctionIdentity(unsigned substFunction, unsigned srt);
  void addCycleFunctionDefinitions(TermAlgebra* ta);

  void addTheoryUnitClause(Literal* lit, unsigned level);
  void addTheoryUnitClause(Literal* lit, Inference* inf, unsigned level);
  void addTheoryNonUnitClause(Literal* lit1, Literal* lit2,unsigned level);
  void addTheoryNonUnitClause(Literal* lit1, Literal* lit2, Literal* lit3,unsigned level);
  void addTheoryNonUnitClause(Literal* lit1, Literal* lit2, Literal* lit3, Literal* lit4,unsigned level);
  void addAndOutputTheoryUnit(Unit* unit, unsigned level);
};

}

#endif // __TheoryAxioms__
