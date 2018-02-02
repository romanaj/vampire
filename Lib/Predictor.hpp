#ifndef __Predictor__
#define __Predictor__

#include "Lib/Sys/Multiprocessing.hpp"

namespace Lib
{

void initializePredictor();
void registerForPrediction(pid_t pid);
void updatePrediction(float *featureLog, unsigned records);
float predictionFor(pid_t pid);

}

#endif
