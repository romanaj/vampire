#include "Predictor.hpp"
#include "Predictor_weights.hpp"

#include "Lib/System.hpp"
#include <sys/mman.h>
#include <cmath>
#include <iostream>

using namespace Lib;

#define MAX_PIDS 1000

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
static float inputs[3760];
static float predict(float *featureLog, unsigned records)
{
  CALL("predict")
  for(unsigned input = 0; input < 3760; ++input)
  {
    inputs[input] = 0;
  }
  // produce a "shape" from the log
  unsigned bucket_size = records / 10;
  if(bucket_size == 0)
  {
    return 1.0;
  }

  for(unsigned record = 0; record < records; ++record)
  {
    unsigned bucket = record / bucket_size;
    ASS_L(bucket, 10)
    for(unsigned row = 0; row < 376; ++row)
    {
        inputs[376 * bucket + row] += featureLog[376 * record + row];
    }
  }

  // scale all totals back to the mean
  for(unsigned i = 0; i < 3760; ++i)
  {
    inputs[i] /= bucket_size;
  }

  // scale inputs to normalized values
  for(unsigned i = 0; i < 3760; ++i)
  {
    unsigned row = i % 376;
    inputs[i] -= MEAN_FEATURES[row];
    inputs[i] /= SCALE_FEATURES[row];
  }

  // compute dot product of weights and inputs
  float result = 0;
  for(unsigned i = 0; i < 3760; ++i)
  {
    result += NN_WEIGHTS[i] * inputs[i];
  }

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
