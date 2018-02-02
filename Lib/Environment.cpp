
/*
 * File Environment.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Environment.cpp
 * Implements environment used by the current prover.
 *
 * @since 06/05/2007 Manchester
 */

#include "Debug/Tracer.hpp"

#include "Lib/Sys/SyncPipe.hpp"

#include "Indexing/TermSharing.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Timer.hpp"

#include "Environment.hpp"
#include "Predictor.hpp"

namespace Lib
{

using namespace std;
using namespace Kernel;
using namespace Indexing;
using namespace Shell;

/**
 * @since 06/05/2007 Manchester
 */
Environment::Environment()
  : signature(0),
    sharing(0),
    property(0),
    clausePriorities(0),
    maxClausePriority(1),
    colorUsed(false),
    _outputDepth(0),
    _priorityOutput(0),
    _pipe(0)
{
  options = new Options;
  statistics = new Statistics;  
  sorts = new Sorts;
  signature = new Signature;
  sharing = new TermSharing;

  _features = new float[1000 * 376];
  timer = Timer::instance();
  timer->start();
} // Environment::Environment

Environment::~Environment()
{
  CALL("Environment::~Environment");

  //in the usual cases the _outputDepth should be zero at this point, but in case of
  //thrown exceptions this might not be true.
//  ASS_EQ(_outputDepth,0);

  while(_outputDepth!=0) {
    endOutput();
  }

// #if CHECK_LEAKS
  delete sharing;
  delete signature;
  delete sorts;
  delete statistics;
  delete _features;
  if(clausePriorities) delete clausePriorities; 
  {
    BYPASSING_ALLOCATOR; // use of std::function in options
    delete options;
  }
// #endif
}

/**
 * If the global time limit reached set Statistics::terminationReason
 * to TIME_LIMIT and return true, otherwise return false.
 * @since 25/03/2008 Torrevieja
 */
bool Environment::timeLimitReached() const
{
  CALL("Environment::timeLimitReached");

  if (options->timeLimitInDeciseconds() &&
      timer->elapsedDeciseconds() > options->timeLimitInDeciseconds()) {
    statistics->terminationReason = Shell::Statistics::TIME_LIMIT;
    return true;
  }
  return false;
} // Environment::timeLimitReached


/**
 * Return remaining time in miliseconds.
 */
int Environment::remainingTime() const
{
  return options->timeLimitInDeciseconds()*100 - timer->elapsedMilliseconds();
}

/**
 * Acquire an output stream
 *
 * A process cannot hold an output stream during forking.
 */
void Environment::beginOutput()
{
  CALL("Environment::beginOutput");
  ASS_GE(_outputDepth,0);

  _outputDepth++;
  if(_outputDepth==1 && _pipe) {
    _pipe->acquireWrite();
  }
}

/**
 * Release the output stream
 */
void Environment::endOutput()
{
  CALL("Environment::endOutput");
  ASS_G(_outputDepth,0);

  _outputDepth--;
  if(_outputDepth==0) {
    if(_pipe) {
      cout.flush();
      _pipe->releaseWrite();
    }
    else {
      cout.flush();
    }
  }
}

/**
 * Return true if we have an output stream acquired
 */
bool Environment::haveOutput()
{
  CALL("Environment::haveOutput");

  return _outputDepth;
}

/**
 * Return the output stream if we have it acquired
 *
 * Process must have an output stream acquired in order to call
 * this function.
 */
ostream& Environment::out()
{
  CALL("Environment::out");
  ASS(_outputDepth);

  if(_priorityOutput) {
    return *_priorityOutput;
  }
  else if(_pipe) {
    return _pipe->out();
  }
  else {
    return cout;
  }
}

/**
 * Direct @b env.out() into @b pipe or to @b cout if @b pipe is zero
 *
 * This function cannot be called when an output is in progress.
 */
void Environment::setPipeOutput(SyncPipe* pipe)
{
  CALL("Environment::setPipeOutput");
  ASS(!haveOutput());

  _pipe=pipe;
}

void Environment::setPriorityOutput(ostream* stm)
{
  CALL("Environment::setPriorityOutput");
  ASS(!_priorityOutput || !stm);

  _priorityOutput=stm;

}

#define DUMP_STAT(x) DUMP(statistics->x)
#define DUMP_PROP(x) DUMP(property->x)
#define DUMP_OPT(x) DUMP(options->x)
#define DO_DUMP\
  DUMP_STAT(inputClauses);\
  DUMP_STAT(inputFormulas);\
  DUMP_STAT(formulaNames);\
  DUMP_STAT(skolemFunctions);\
  DUMP_STAT(purePredicates);\
  DUMP_STAT(trivialPredicates);\
  DUMP_STAT(unusedPredicateDefinitions);\
  DUMP_STAT(functionDefinitions);\
  DUMP_STAT(selectedBySine);\
  DUMP_STAT(sineIterations);\
  DUMP_STAT(splitInequalities);\
  DUMP_STAT(initialClauses);\
  DUMP_STAT(generatedClauses);\
  DUMP_STAT(activeClauses);\
  DUMP_STAT(passiveClauses);\
  DUMP_STAT(extensionalityClauses);\
  DUMP_STAT(blockedClauses);\
  DUMP_STAT(finalActiveClauses);\
  DUMP_STAT(finalPassiveClauses);\
  DUMP_STAT(finalExtensionalityClauses);\
  DUMP_STAT(discardedNonRedundantClauses);\
  DUMP_STAT(inferencesSkippedDueToColors);\
  DUMP_STAT(inferencesBlockedForOrderingAftercheck);\
  DUMP_STAT(duplicateLiterals);\
  DUMP_STAT(trivialInequalities);\
  DUMP_STAT(forwardSubsumptionResolution);\
  DUMP_STAT(backwardSubsumptionResolution);\
  DUMP_STAT(forwardDemodulations);\
  DUMP_STAT(backwardDemodulations);\
  DUMP_STAT(forwardLiteralRewrites);\
  DUMP_STAT(innerRewrites);\
  DUMP_STAT(condensations);\
  DUMP_STAT(globalSubsumption);\
  DUMP_STAT(evaluations);\
  DUMP_STAT(interpretedSimplifications);\
  DUMP_STAT(simpleTautologies);\
  DUMP_STAT(equationalTautologies);\
  DUMP_STAT(deepEquationalTautologies);\
  DUMP_STAT(forwardSubsumed);\
  DUMP_STAT(backwardSubsumed);\
  DUMP_STAT(forwardDemodulationsToEqTaut);\
  DUMP_STAT(backwardDemodulationsToEqTaut);\
  DUMP_STAT(innerRewritesToEqTaut);\
  DUMP_STAT(resolution);\
  DUMP_STAT(urResolution);\
  DUMP_STAT(cResolution);\
  DUMP_STAT(factoring);\
  DUMP_STAT(forwardSuperposition);\
  DUMP_STAT(backwardSuperposition);\
  DUMP_STAT(selfSuperposition);\
  DUMP_STAT(cForwardSuperposition);\
  DUMP_STAT(cSelfSuperposition);\
  DUMP_STAT(equalityFactoring);\
  DUMP_STAT(equalityResolution);\
  DUMP_STAT(forwardExtensionalityResolution);\
  DUMP_STAT(backwardExtensionalityResolution);\
  DUMP_STAT(theoryInstSimp);\
  DUMP_STAT(theoryInstSimpCandidates);\
  DUMP_STAT(theoryInstSimpTautologies);\
  DUMP_STAT(theoryInstSimpLostSolution);\
  DUMP_STAT(taDistinctnessSimplifications);\
  DUMP_STAT(taDistinctnessTautologyDeletions);\
  DUMP_STAT(taInjectivitySimplifications);\
  DUMP_STAT(taNegativeInjectivitySimplifications);\
  DUMP_STAT(taAcyclicityGeneratedDisequalities);\
  DUMP_STAT(splitClauses);\
  DUMP_STAT(splitComponents);\
  DUMP_STAT(uniqueComponents);\
  DUMP_STAT(satSplitRefutations);\
  DUMP_STAT(smtFallbacks);\
  DUMP_STAT(instGenGeneratedClauses);\
  DUMP_STAT(instGenRedundantClauses);\
  DUMP_STAT(instGenKeptClauses);\
  DUMP_STAT(instGenIterations);\
  DUMP_STAT(maxBFNTModelSize);\
  DUMP_STAT(satClauses);\
  DUMP_STAT(unitSatClauses);\
  DUMP_STAT(binarySatClauses);\
  DUMP_STAT(learntSatClauses);\
  DUMP_STAT(learntSatLiterals);\
  DUMP_STAT(satTWLClauseCount);\
  DUMP_STAT(satTWLVariablesCount);\
  DUMP_STAT(satTWLSATCalls);\
  DUMP_STAT(satPureVarsEliminated);\
  DUMP_PROP(clauses());\
  DUMP_PROP(formulas());\
  DUMP_PROP(unitClauses());\
  DUMP_PROP(hornClauses());\
  DUMP_PROP(atoms());\
  DUMP_PROP(equalityAtoms());\
  DUMP_PROP(positiveEqualityAtoms());\
  DUMP_PROP(hasFormulas());\
  DUMP_PROP(maxFunArity());\
  DUMP_PROP(totalNumberOfVariables());\
  for(int i = 0; i <= 41; ++i)\
    DUMP_PROP(hasProp(1 << i));\
  for(unsigned i = Interpretation::EQUAL; i < Interpretation::INVALID_INTERPRETATION; ++i)\
    DUMP_PROP(hasInterpretedOperation(static_cast<Interpretation>(i)));\
  DUMP_PROP(hasInterpretedOperations());\
  DUMP_PROP(hasInterpretedEquality());\
  DUMP_PROP(hasNonDefaultSorts());\
  DUMP_PROP(hasFOOL());\
  DUMP_PROP(sortsUsed());\
  DUMP_PROP(onlyFiniteDomainDatatypes());\
  DUMP_PROP(knownInfiniteDomain());\
  DUMP_PROP(getSMTLIBLogic());\
  DUMP_PROP(allNonTheoryClausesGround());\
  DUMP_OPT(fmbNonGroundDefs());\
  DUMP_OPT(fmbStartSize());\
  DUMP_OPT(fmbSymmetryRatio());\
  DUMP_OPT(fmbSymmetryWidgetOrders());\
  DUMP_OPT(fmbSymmetryOrderSymbols());\
  DUMP_OPT(fmbAdjustSorts());\
  DUMP_OPT(fmbDetectSortBounds());\
  DUMP_OPT(fmbDetectSortBoundsTimeLimit());\
  DUMP_OPT(fmbSizeWeightRatio());\
  DUMP_OPT(fmbEnumerationStrategy());\
  DUMP_OPT(flattenTopLevelConjunctions());\
  DUMP_OPT(ltbLearning());\
  DUMP_OPT(mode());\
  DUMP_OPT(multicore());\
  DUMP_OPT(normalize());\
  DUMP_OPT(activationLimit());\
  DUMP_OPT(rowVariableMaxLength());\
  DUMP_OPT(unificationWithAbstraction());\
  DUMP_OPT(unusedPredicateDefinitionRemoval());\
  DUMP_OPT(blockedClauseElimination());\
  DUMP_OPT(weightIncrement());\
  DUMP_OPT(satSolver());\
  DUMP_OPT(saturationAlgorithm());\
  DUMP_OPT(selection());\
  DUMP_OPT(literalComparisonMode());\
  DUMP_OPT(forwardSubsumptionResolution());\
  DUMP_OPT(forwardDemodulation());\
  DUMP_OPT(binaryResolution());\
  DUMP_OPT(bfnt());\
  DUMP_OPT(unitResultingResolution());\
  DUMP_OPT(hyperSuperposition());\
  DUMP_OPT(innerRewriting());\
  DUMP_OPT(equationalTautologyRemoval());\
  DUMP_OPT(arityCheck());\
  DUMP_OPT(backwardDemodulation());\
  DUMP_OPT(demodulationRedundancyCheck());\
  DUMP_OPT(backwardSubsumption());\
  DUMP_OPT(backwardSubsumptionResolution());\
  DUMP_OPT(forwardSubsumption());\
  DUMP_OPT(forwardLiteralRewriting());\
  DUMP_OPT(lrsFirstTimeCheck());\
  DUMP_OPT(lrsWeightLimitOnly());\
  DUMP_OPT(lookaheadDelay());\
  DUMP_OPT(simulatedTimeLimit());\
  DUMP_OPT(maxInferenceDepth());\
  DUMP_OPT(symbolPrecedence());\
  DUMP_OPT(symbolPrecedenceBoost());\
  DUMP_OPT(timeLimitInDeciseconds());\
  DUMP_OPT(memoryLimit());\
  DUMP_OPT(inequalitySplitting());\
  DUMP_OPT(maxActive());\
  DUMP_OPT(maxAnswers());\
  DUMP_OPT(maxPassive());\
  DUMP_OPT(maxWeight());\
  DUMP_OPT(ageRatio());\
  DUMP_OPT(weightRatio());\
  DUMP_OPT(literalMaximalityAftercheck());\
  DUMP_OPT(superpositionFromVariables());\
  DUMP_OPT(equalityProxy());\
  DUMP_OPT(equalityResolutionWithDeletion());\
  DUMP_OPT(extensionalityResolution());\
  DUMP_OPT(FOOLParamodulation());\
  DUMP_OPT(termAlgebraInferences());\
  DUMP_OPT(termAlgebraCyclicityCheck());\
  DUMP_OPT(extensionalityMaxLength());\
  DUMP_OPT(extensionalityAllowPosEq());\
  DUMP_OPT(nongoalWeightCoefficient());\
  DUMP_OPT(sos());\
  DUMP_OPT(sosTheoryLimit());\
  DUMP_OPT(functionDefinitionElimination());\
  DUMP_OPT(globalSubsumption());\
  DUMP_OPT(globalSubsumptionSatSolverPower());\
  DUMP_OPT(globalSubsumptionExplicitMinim());\
  DUMP_OPT(globalSubsumptionAvatarAssumptions());\
  DUMP_OPT(increasedNumeralWeight());\
  DUMP_OPT(theoryAxioms());\
  DUMP_OPT(interpretedSimplification());\
  DUMP_OPT(condensation());\
  DUMP_OPT(generalSplitting());\
  DUMP_OPT(splitting());\
  DUMP_OPT(nonliteralsInClauseWeight());\
  DUMP_OPT(sineDepth());\
  DUMP_OPT(sineGeneralityThreshold());\
  DUMP_OPT(sineSelection());\
  DUMP_OPT(sineTolerance());\
  DUMP_OPT(smtlibConsiderIntsReal());\
  DUMP_OPT(smtlibFletAsDefinition());\
  DUMP_OPT(colorUnblocking());\
  DUMP_OPT(instantiation());\
  DUMP_OPT(theoryFlattening());\
  DUMP_OPT(instGenBigRestartRatio());\
  DUMP_OPT(instGenPassiveReactivation());\
  DUMP_OPT(instGenResolutionRatioInstGen());\
  DUMP_OPT(instGenResolutionRatioResolution());\
  DUMP_OPT(instGenRestartPeriod());\
  DUMP_OPT(instGenRestartPeriodQuotient());\
  DUMP_OPT(instGenSelection());\
  DUMP_OPT(instGenWithResolution());\
  DUMP_OPT(useHashingVariantIndex());\
  DUMP_OPT(satClauseActivityDecay());\
  DUMP_OPT(satClauseDisposer());\
  DUMP_OPT(satLearntMinimization());\
  DUMP_OPT(satLearntSubsumptionResolution());\
  DUMP_OPT(satRestartFixedCount());\
  DUMP_OPT(satRestartGeometricIncrease());\
  DUMP_OPT(satRestartGeometricInit());\
  DUMP_OPT(satRestartLubyFactor());\
  DUMP_OPT(satRestartMinisatIncrease());\
  DUMP_OPT(satRestartMinisatInit());\
  DUMP_OPT(satRestartStrategy());\
  DUMP_OPT(satVarActivityDecay());\
  DUMP_OPT(satVarSelector());\
  DUMP_OPT(nicenessOption());\
  DUMP_OPT(getWhileNumber());\
  DUMP_OPT(getFunctionNumber());\
  DUMP_OPT(nonGoalWeightCoeffitientNumerator());\
  DUMP_OPT(nonGoalWeightCoeffitientDenominator());\
  DUMP_OPT(splitAtActivation());\
  DUMP_OPT(splittingNonsplittableComponents());\
  DUMP_OPT(splittingAddComplementary());\
  DUMP_OPT(splittingMinimizeModel());\
  DUMP_OPT(splittingLiteralPolarityAdvice());\
  DUMP_OPT(splittingDeleteDeactivated());\
  DUMP_OPT(splittingFastRestart());\
  DUMP_OPT(splittingBufferedSolver());\
  DUMP_OPT(splittingFlushPeriod());\
  DUMP_OPT(splittingFlushQuotient());\
  DUMP_OPT(splittingEagerRemoval());\
  DUMP_OPT(splittingCongruenceClosure());\
  DUMP_OPT(ccUnsatCores());\
  DUMP_OPT(bpEquivalentVariableRemoval());\
  DUMP_OPT(bpMaximalPropagatedEqualityLength());\
  DUMP_OPT(bpAlmostHalfBoundingRemoval());\
  DUMP_OPT(bpFmElimination());\
  DUMP_OPT(bpAllowedFMBalance());\
  DUMP_OPT(bpAssignmentSelector());\
  DUMP_OPT(bpCollapsingPropagation());\
  DUMP_OPT(bpUpdatesByOneConstraint());\
  DUMP_OPT(bpConservativeAssignmentSelection());\
  DUMP_OPT(bpConflictSelector());\
  DUMP_OPT(backjumpTargetIsDecisionPoint());\
  DUMP_OPT(bpPropagateAfterConflict());\
  DUMP_OPT(bpVariableSelector());\
  DUMP_OPT(bpSelectUnusedVariablesFirst());\
  DUMP_OPT(bpStartWithPrecise());\
  DUMP_OPT(bpStartWithRational());\
  DUMP_OPT(newCNF());\
  DUMP_OPT(getIteInliningThreshold());\
  DUMP_OPT(getIteInlineLet());\
  DUMP(Allocator::getUsedMemory() / 1024)

void Environment::printFeatures(std::ostream &out)
{
  CALL("Environment::printFeatures");
# define DUMP(x) out << x << ",";
  DO_DUMP
# undef DUMP
  out << std::endl;
}

void Environment::saveFeatures()
{
  CALL("Environment::saveFeatures");
  static int step = 0;

  if(step % 10 != 0)
  {
    step++;
    return;
  }

  unsigned idx = step / 10;
  ASS_L(idx, 1000);
  float *writer = _features + 376 * idx;
# define DUMP(x) *writer++ = static_cast<float>(x);
  DO_DUMP
# undef DUMP
  if(idx > 0 && idx % 10 == 0)
  {
    updatePrediction(_features, idx);
    Multiprocessing::instance()->stop();
  }
  step++;
}

}
