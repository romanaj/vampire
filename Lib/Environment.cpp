
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

static const size_t FEATURE_DIMENSIONS = 376;
static const unsigned SAMPLE_FREQUENCY = 10;
static const unsigned UPDATE_FREQUENCY = 10;
static const size_t MAX_FEATURE_RECORDS = 10000;

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

  _features = new float[MAX_FEATURE_RECORDS * 376];
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
  DUMP_STAT(discardedNonRedundantClauses);\
  DUMP_STAT(duplicateLiterals);\
  DUMP_STAT(trivialInequalities);\
  DUMP_STAT(forwardSubsumptionResolution);\
  DUMP_STAT(backwardSubsumptionResolution);\
  DUMP_STAT(forwardDemodulations);\
  DUMP_STAT(backwardDemodulations);\
  DUMP_STAT(forwardLiteralRewrites);\
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
  DUMP_STAT(splitClauses);\
  DUMP_STAT(splitComponents);\
  DUMP_STAT(uniqueComponents);\
  DUMP_STAT(satSplitRefutations);\
  DUMP_STAT(instGenGeneratedClauses);\
  DUMP_STAT(instGenRedundantClauses);\
  DUMP_STAT(instGenKeptClauses);\
  DUMP_STAT(instGenIterations);\
  DUMP_STAT(satClauses);\
  DUMP_STAT(unitSatClauses);\
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
  for(int i = 0; i <= 4; ++i)\
    DUMP_PROP(hasProp(1 << i));\
  for(int i = 18; i <= 31; ++i)\
    DUMP_PROP(hasProp(1 << i));\
  DUMP_PROP(hasInterpretedOperations());\
  DUMP_OPT(activationLimit());\
  DUMP_OPT(unusedPredicateDefinitionRemoval());\
  DUMP_OPT(blockedClauseElimination());\
  DUMP_OPT(satSolver());\
  DUMP_OPT(saturationAlgorithm());\
  DUMP_OPT(selection());\
  DUMP_OPT(literalComparisonMode());\
  DUMP_OPT(forwardSubsumptionResolution());\
  DUMP_OPT(forwardDemodulation());\
  DUMP_OPT(binaryResolution());\
  DUMP_OPT(unitResultingResolution());\
  DUMP_OPT(equationalTautologyRemoval());\
  DUMP_OPT(backwardDemodulation());\
  DUMP_OPT(demodulationRedundancyCheck());\
  DUMP_OPT(backwardSubsumption());\
  DUMP_OPT(backwardSubsumptionResolution());\
  DUMP_OPT(forwardSubsumption());\
  DUMP_OPT(forwardLiteralRewriting());\
  DUMP_OPT(lrsFirstTimeCheck());\
  DUMP_OPT(lrsWeightLimitOnly());\
  DUMP_OPT(lookaheadDelay());\
  DUMP_OPT(symbolPrecedence());\
  DUMP_OPT(timeLimitInDeciseconds());\
  DUMP_OPT(inequalitySplitting());\
  DUMP_OPT(ageRatio());\
  DUMP_OPT(weightRatio());\
  DUMP_OPT(literalMaximalityAftercheck());\
  DUMP_OPT(superpositionFromVariables());\
  DUMP_OPT(equalityProxy());\
  DUMP_OPT(equalityResolutionWithDeletion());\
  DUMP_OPT(extensionalityResolution());\
  DUMP_OPT(nongoalWeightCoefficient());\
  DUMP_OPT(sos());\
  DUMP_OPT(functionDefinitionElimination());\
  DUMP_OPT(globalSubsumption());\
  DUMP_OPT(theoryAxioms());\
  DUMP_OPT(condensation());\
  DUMP_OPT(generalSplitting());\
  DUMP_OPT(splitting());\
  DUMP_OPT(nonliteralsInClauseWeight());\
  DUMP_OPT(sineDepth());\
  DUMP_OPT(sineGeneralityThreshold());\
  DUMP_OPT(sineSelection());\
  DUMP_OPT(sineTolerance());\
  DUMP_OPT(instantiation());\
  DUMP_OPT(nonGoalWeightCoeffitientNumerator());\
  DUMP_OPT(nonGoalWeightCoeffitientDenominator());\
  DUMP_OPT(splitAtActivation());\
  DUMP_OPT(splittingNonsplittableComponents());\
  DUMP_OPT(splittingAddComplementary());\
  DUMP_OPT(splittingMinimizeModel());\
  DUMP_OPT(splittingLiteralPolarityAdvice());\
  DUMP_OPT(splittingDeleteDeactivated());\
  DUMP_OPT(splittingFastRestart());\
  DUMP_OPT(splittingFlushPeriod());\
  DUMP_OPT(splittingFlushQuotient());\
  DUMP_OPT(splittingEagerRemoval());\
  DUMP_OPT(splittingCongruenceClosure());\
  DUMP_OPT(newCNF());\
  DUMP(Allocator::getUsedMemory() / 1024)

static unsigned feature_records;
void Environment::saveFeatures()
{
  CALL("Environment::saveFeatures");
  static int step = 0;

  if(step % SAMPLE_FREQUENCY != 0)
  {
    step++;
    return;
  }

  feature_records = step / SAMPLE_FREQUENCY;
  ASS_L(feature_records, MAX_FEATURE_RECORDS);
  if(feature_records > MAX_FEATURE_RECORDS)
  {
	  return;
  }

  float *writer = _features + FEATURE_DIMENSIONS * feature_records;
# define DUMP(x) *writer++ = static_cast<float>(x);
  DO_DUMP
# undef DUMP
  if(feature_records > 0 && feature_records % UPDATE_FREQUENCY == 0)
  {
    updatePrediction(_features, feature_records);
    Timer::instance()->stop();
    Multiprocessing::instance()->stop();
    Timer::instance()->start();
  }
  step++;
}

#ifdef VDUMP
#include <cstdlib>
#include <fstream>

void Environment::dumpFeatures(bool success)
{
  char templ[100];
  strcpy(templ, success ? "/tmp/vdump-success-XXXXXX" : "/tmp/vdump-failure-XXXXXX");
  std::ofstream out(mktemp(templ));

  for(unsigned i = 0; i < feature_records; ++i)
  {
    out << _features[FEATURE_DIMENSIONS * i];
    for(unsigned j = 1; j < FEATURE_DIMENSIONS; ++j)
    {
      out << "," << _features[FEATURE_DIMENSIONS * i + j];
    }
    out << std::endl;
  }
}
#endif

}
