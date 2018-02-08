#include "Predictor.hpp"
#include "Predictor_weights.hpp"

#include "Lib/System.hpp"
#include <sys/mman.h>
#include <cmath>
#include <iostream>

using namespace Lib;

static const unsigned MAX_PIDS = 1000;
static const unsigned FEATURE_DIMENSIONS = 376;
static const unsigned NUM_BUCKETS = 10;

static pid_t *pids = nullptr;
static float *predictions = nullptr;
static unsigned pid_idx = 0;

void Lib::initializePredictor()
{
  CALL("initializePredictor")
  void *map = mmap
  (
    NULL,
    MAX_PIDS * sizeof(pid_t),
    PROT_READ | PROT_WRITE,
    MAP_SHARED | MAP_ANONYMOUS,
    -1,
    0
  );
  ASS_NEQ(map, MAP_FAILED);
  pids = static_cast<pid_t *>(map);

  map = mmap
  (
    NULL,
    MAX_PIDS * sizeof(float),
    PROT_READ | PROT_WRITE,
    MAP_SHARED | MAP_ANONYMOUS,
    -1,
    0
  );
  ASS_NEQ(map, MAP_FAILED);
  predictions = static_cast<float *>(map);

  for(unsigned i = 0; i < MAX_PIDS; ++i)
  {
    pids[i] = -1;
    predictions[i] = 1.0;
  }
}

void Lib::registerForPrediction(pid_t pid)
{
  CALL("registerForPrediction")
  pids[pid_idx++] = pid;
  ASS_L(pid_idx, MAX_PIDS);
}

static unsigned pid_index(pid_t pid)
{
  for(unsigned i = 0; i < MAX_PIDS; ++i)
  {
    if(pids[i] == pid)
    {
      return i;
    }
  }
  ASSERTION_VIOLATION;
  return -1;
}

// don't blow the stack
static float inputs[FEATURE_DIMENSIONS * NUM_BUCKETS];
static float predict(float *featureLog, unsigned records)
{
  CALL("predict")
  for(unsigned input = 0; input < FEATURE_DIMENSIONS * NUM_BUCKETS; ++input)
  {
    inputs[input] = 0;
  }
  // produce a "shape" from the log
  unsigned bucket_size = records / NUM_BUCKETS;
  if(bucket_size == 0)
  {
    return 1.0;
  }

  for(unsigned record = 0; record < records; ++record)
  {
    unsigned bucket = record / bucket_size;
    ASS_L(bucket, NUM_BUCKETS)
    for(unsigned row = 0; row < FEATURE_DIMENSIONS; ++row)
    {
        inputs[FEATURE_DIMENSIONS * bucket + row] += featureLog[FEATURE_DIMENSIONS * record + row];
    }
  }

  // scale all totals back to the mean
  for(unsigned i = 0; i < FEATURE_DIMENSIONS * NUM_BUCKETS; ++i)
  {
    inputs[i] /= bucket_size;
  }

  // scale inputs to normalized values
  for(unsigned i = 0; i < FEATURE_DIMENSIONS * NUM_BUCKETS; ++i)
  {
    unsigned row = i % FEATURE_DIMENSIONS;
    inputs[i] -= MEAN_FEATURES[row];
    inputs[i] /= SCALE_FEATURES[row];
  }

  // compute dot product of weights and inputs
  float result = 0;
  for(unsigned i = 0; i < FEATURE_DIMENSIONS * NUM_BUCKETS; ++i)
  {
    result += NN_WEIGHTS[i] * inputs[i];
  }

  // sigmoid activation
  result = 1.0 / (1.0 + std::exp(-result));
  return result;
}

void Lib::updatePrediction(float *featureLog, unsigned records)
{
  CALL("updatePrediction")
  auto pid = System::getPID();
  predictions[pid_index(pid)] = predict(featureLog, records);
}

float Lib::predictionFor(pid_t pid)
{
  CALL("predictionFor")
  return predictions[pid_index(pid)];
}
