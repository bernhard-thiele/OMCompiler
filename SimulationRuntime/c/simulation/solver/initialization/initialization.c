/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-2014, Open Source Modelica Consortium (OSMC),
 * c/o Linköpings universitet, Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF THE BSD NEW LICENSE OR THE
 * GPL VERSION 3 LICENSE OR THE OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.2.
 * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
 * RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GPL VERSION 3,
 * ACCORDING TO RECIPIENTS CHOICE.
 *
 * The OpenModelica software and the OSMC (Open Source Modelica Consortium)
 * Public License (OSMC-PL) are obtained from OSMC, either from the above
 * address, from the URLs: http://www.openmodelica.org or
 * http://www.ida.liu.se/projects/OpenModelica, and in the OpenModelica
 * distribution. GNU version 3 is obtained from:
 * http://www.gnu.org/copyleft/gpl.html. The New BSD License is obtained from:
 * http://www.opensource.org/licenses/BSD-3-Clause.
 *
 * This program is distributed WITHOUT ANY WARRANTY; without even the implied
 * warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE, EXCEPT AS
 * EXPRESSLY SET FORTH IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE
 * CONDITIONS OF OSMC-PL.
 *
 */

/*! \file initialization.c
 */

#include "initialization.h"

#include "method_simplex.h"
#include "method_newuoa.h"
#include "method_nelderMeadEx.h"
#include "method_kinsol.h"
#include "method_ipopt.h"

#include "simulation_data.h"
#include "util/omc_error.h"
#include "openmodelica.h"
#include "openmodelica_func.h"
#include "model_help.h"
#include "read_matlab4.h"
#include "events.h"
#include "stateset.h"

#include "initialization_data.h"
#include "mixedSystem.h"
#include "linearSystem.h"
#include "nonlinearSystem.h"
#include "delay.h"

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

/*! \fn int reportResidualValue(INIT_DATA *initData)
 *
 *  return 1: if funcValue >  1e-5
 *         0: if funcValue <= 1e-5
 *
 *  \param [in]  [initData]
 */
int reportResidualValue(INIT_DATA *initData)
{
  long i = 0;
  double funcValue = leastSquareWithLambda(initData, 1.0);

  if(1e-5 < funcValue)
  {
    if (ACTIVE_STREAM(LOG_INIT))
    {
      infoStreamPrint(LOG_INIT, 1, "error in initialization. System of initial equations are not consistent\n(least square function value is %g)", funcValue);
      for(i=0; i<initData->nInitResiduals; i++) {
        if(1e-5 < fabs(initData->initialResiduals[i])) {
          infoStreamPrint(LOG_INIT, 0, "residual[%ld] = %g", i+1, initData->initialResiduals[i]);
        }
      }
      messageClose(LOG_INIT);
    }
    return 1;
  }
  return 0;
}

/*! \fn double leastSquareWithLambda(INIT_DATA *initData, double lambda)
 *
 *  This function calculates the residual value as the sum of squared residual equations.
 *
 *  \param [ref] [initData]
 *  \param [in]  [lambda] E [0; 1]
 */
double leastSquareWithLambda(INIT_DATA *initData, double lambda)
{
  DATA *data = initData->simData;

  long i = 0, ix;
  double funcValue = 0.0;
  double scalingCoefficient;

  updateSimData(initData);

  data->callback->updateBoundParameters(data);
  /*functionODE(data);*/
  data->callback->functionDAE(data);
  data->callback->functionAlgebraics(data);
  data->callback->initial_residual(data, initData->initialResiduals);

  for(i=0; i<data->modelData.nInitResiduals; ++i)
  {
    if(initData->residualScalingCoefficients)
      scalingCoefficient = initData->residualScalingCoefficients[i]; /* use scaling coefficients */
    else
      scalingCoefficient = 1.0; /* no scaling coefficients given */

    funcValue += (initData->initialResiduals[i] / scalingCoefficient) * (initData->initialResiduals[i] / scalingCoefficient);
  }

  if(lambda < 1.0)
  {
    funcValue *= lambda;
    ix = 0;

    /* for real variables */
    for(i=0; i<data->modelData.nVariablesReal; ++i)
      if(data->modelData.realVarsData[i].attribute.useStart)
      {
        if(initData->startValueResidualScalingCoefficients)
          scalingCoefficient = initData->startValueResidualScalingCoefficients[ix++]; /* use scaling coefficients */
        else
          scalingCoefficient = 1.0; /* no scaling coefficients given */

        funcValue += (1.0-lambda)*((data->modelData.realVarsData[i].attribute.start-data->localData[0]->realVars[i])/scalingCoefficient)*((data->modelData.realVarsData[i].attribute.start-data->localData[0]->realVars[i])/scalingCoefficient);
      }

      /* for real parameters */
      for(i=0; i<data->modelData.nParametersReal; ++i)
        if(data->modelData.realParameterData[i].attribute.useStart && !data->modelData.realParameterData[i].attribute.fixed)
        {
          if(initData->startValueResidualScalingCoefficients)
            scalingCoefficient = initData->startValueResidualScalingCoefficients[ix++]; /* use scaling coefficients */
          else
            scalingCoefficient = 1.0; /* no scaling coefficients given */

          funcValue += (1.0-lambda)*((data->modelData.realParameterData[i].attribute.start-data->simulationInfo.realParameter[i])/scalingCoefficient)*((data->modelData.realParameterData[i].attribute.start-data->simulationInfo.realParameter[i])/scalingCoefficient);
        }

      /* for real discrete */
      for(i=data->modelData.nVariablesReal-data->modelData.nDiscreteReal; i<data->modelData.nDiscreteReal; ++i)
          if(data->modelData.realVarsData[i].attribute.useStart && !data->modelData.realVarsData[i].attribute.fixed)
          {
              if(initData->startValueResidualScalingCoefficients)
                  scalingCoefficient = initData->startValueResidualScalingCoefficients[ix++]; /* use scaling coefficients */
              else
                  scalingCoefficient = 1.0; /* no scaling coefficients given */

              funcValue += (1.0-lambda)*((data->modelData.realVarsData[i].attribute.start-data->simulationInfo.realParameter[i])/scalingCoefficient)*((data->modelData.realVarsData[i].attribute.start-data->simulationInfo.realParameter[i])/scalingCoefficient);
          }
  }

  return funcValue;
}

/*! \fn void dumpInitialization(INIT_DATA *initData)
 *
 *  \param [in]  [initData]
 *
 *  \author lochel
 */
void dumpInitialization(DATA *data, INIT_DATA *initData)
{
  long i;
  double fValueScaled = leastSquareWithLambda(initData, 1.0);
  double fValue = 0.0;

  if (!ACTIVE_STREAM(LOG_INIT)) return;
  for(i=0; i<initData->nInitResiduals; ++i)
    fValue += initData->initialResiduals[i] * initData->initialResiduals[i];

  infoStreamPrint(LOG_INIT, 1, "initialization status");
  if(initData->residualScalingCoefficients)
    infoStreamPrint(LOG_INIT, 0, "least square value: %g [scaled: %g]", fValue, fValueScaled);
  else
    infoStreamPrint(LOG_INIT, 0, "least square value: %g", fValue);

  infoStreamPrint(LOG_INIT, 1, "unfixed variables");
  for(i=0; i<initData->nStates; ++i)
    if(initData->nominal)
      infoStreamPrint(LOG_INIT, 0, "[%ld] [%15g] := %s [scaling coefficient: %g]", i+1, initData->vars[i], initData->name[i], initData->nominal[i]);
    else
      infoStreamPrint(LOG_INIT, 0, "[%ld] [%15g] := %s", i+1, initData->vars[i], initData->name[i]);

  for(; i<initData->nStates+initData->nParameters; ++i)
    if(initData->nominal)
      infoStreamPrint(LOG_INIT, 0, "[%ld] [%15g] := %s (parameter) [scaling coefficient: %g]", i+1, initData->vars[i], initData->name[i], initData->nominal[i]);
    else
      infoStreamPrint(LOG_INIT, 0, "[%ld] [%15g] := %s (parameter)", i+1, initData->vars[i], initData->name[i]);

  for(; i<initData->nVars; ++i)
    if(initData->nominal)
      infoStreamPrint(LOG_INIT, 0, "[%ld] [%15g] := %s (discrete) [scaling coefficient: %g]", i+1, initData->vars[i], initData->name[i], initData->nominal[i]);
    else
      infoStreamPrint(LOG_INIT, 0, "[%ld] [%15g] := %s (discrete)", i+1, initData->vars[i], initData->name[i]);
  messageClose(LOG_INIT);

  infoStreamPrint(LOG_INIT, 1, "initial residuals");
  for(i=0; i<initData->nInitResiduals; ++i)
    if(initData->residualScalingCoefficients)
      infoStreamPrint(LOG_INIT, 0, "[%ld] [%15g] := %s [scaling coefficient: %g]", i+1, initData->initialResiduals[i], data->callback->initialResidualDescription(i), initData->residualScalingCoefficients[i]);
    else
      infoStreamPrint(LOG_INIT, 0, "[%ld] [%15g] := %s", i+1, initData->initialResiduals[i], data->callback->initialResidualDescription(i));
  messageClose(LOG_INIT);
  messageClose(LOG_INIT);
}

/*! \fn void dumpInitializationStatus(DATA *data)
 *
 *  \param [in]  [data]
 *
 *  \author lochel
 */
void dumpInitialSolution(DATA *simData)
{
  long i, j;

  const MODEL_DATA      *mData = &(simData->modelData);
  const SIMULATION_INFO *sInfo = &(simData->simulationInfo);

  if (ACTIVE_STREAM(LOG_INIT))
    printParameters(simData, LOG_INIT);

  if (!ACTIVE_STREAM(LOG_SOTI)) return;
  infoStreamPrint(LOG_SOTI, 1, "### SOLUTION OF THE INITIALIZATION ###");

  if (0 < mData->nStates)
  {
    infoStreamPrint(LOG_SOTI, 1, "states variables");
    for(i=0; i<mData->nStates; ++i)
      infoStreamPrint(LOG_SOTI, 0, "[%ld] Real %s(start=%g, nominal=%g) = %g (pre: %g)", i+1,
                                   mData->realVarsData[i].info.name,
                                   mData->realVarsData[i].attribute.start,
                                   mData->realVarsData[i].attribute.nominal,
                                   simData->localData[0]->realVars[i],
                                   sInfo->realVarsPre[i]);
    messageClose(LOG_SOTI);
  }

  if (0 < mData->nStates)
  {
    infoStreamPrint(LOG_SOTI, 1, "derivatives variables");
    for(i=mData->nStates; i<2*mData->nStates; ++i)
      infoStreamPrint(LOG_SOTI, 0, "[%ld] Real %s = %g (pre: %g)", i+1,
                                   mData->realVarsData[i].info.name,
                                   simData->localData[0]->realVars[i],
                                   sInfo->realVarsPre[i]);
    messageClose(LOG_SOTI);
  }

  if (2*mData->nStates < mData->nVariablesReal)
  {
    infoStreamPrint(LOG_SOTI, 1, "other real variables");
    for(i=2*mData->nStates; i<mData->nVariablesReal; ++i)
      infoStreamPrint(LOG_SOTI, 0, "[%ld] Real %s(start=%g, nominal=%g) = %g (pre: %g)", i+1,
                                   mData->realVarsData[i].info.name,
                                   mData->realVarsData[i].attribute.start,
                                   mData->realVarsData[i].attribute.nominal,
                                   simData->localData[0]->realVars[i],
                                   sInfo->realVarsPre[i]);
    messageClose(LOG_SOTI);
  }

  if (0 < mData->nVariablesInteger)
  {
    infoStreamPrint(LOG_SOTI, 1, "integer variables");
    for(i=0; i<mData->nVariablesInteger; ++i)
      infoStreamPrint(LOG_SOTI, 0, "[%ld] Integer %s(start=%ld) = %ld (pre: %ld)", i+1,
                                   mData->integerVarsData[i].info.name,
                                   mData->integerVarsData[i].attribute.start,
                                   simData->localData[0]->integerVars[i],
                                   sInfo->integerVarsPre[i]);
    messageClose(LOG_SOTI);
  }

  if (0 < mData->nVariablesBoolean)
  {
    infoStreamPrint(LOG_SOTI, 1, "boolean variables");
    for(i=0; i<mData->nVariablesBoolean; ++i)
      infoStreamPrint(LOG_SOTI, 0, "[%ld] Boolean %s(start=%s) = %s (pre: %s)", i+1,
                                   mData->booleanVarsData[i].info.name,
                                   mData->booleanVarsData[i].attribute.start ? "true" : "false",
                                   simData->localData[0]->booleanVars[i] ? "true" : "false",
                                   sInfo->booleanVarsPre[i] ? "true" : "false");
    messageClose(LOG_SOTI);
  }

  if (0 < mData->nVariablesString)
  {
    infoStreamPrint(LOG_SOTI, 1, "string variables");
    for(i=0; i<mData->nVariablesString; ++i)
      infoStreamPrint(LOG_SOTI, 0, "[%ld] String %s(start=\"%s\") = \"%s\" (pre: \"%s\")", i+1,
                                   mData->stringVarsData[i].info.name,
                                   mData->stringVarsData[i].attribute.start,
                                   simData->localData[0]->stringVars[i],
                                   sInfo->stringVarsPre[i]);
    messageClose(LOG_SOTI);
  }

  messageClose(LOG_SOTI);
}

/*! \fn static int initialize2(INIT_DATA *initData, int optiMethod, int useScaling, int lambda_steps)
 *
 *  This is a helper function for initialize.
 *
 *  \param [ref] [initData]
 *  \param [in]  [optiMethod] specified optimization method
 *  \param [in]  [useScaling] specifies whether scaling should be used or not
 *  \param [in]  [lambda_steps] number of steps
 *
 *  \author lochel
 */
static int initialize2(INIT_DATA *initData, int optiMethod, int useScaling, int lambda_steps)
{
  DATA *data = initData->simData;

  double STOPCR = 1.e-12;
  double lambda = 0.0;
  double funcValue;

  long i, j;

  int retVal = 0;

  double *bestZ = (double*)malloc(initData->nVars * sizeof(double));
  double bestFuncValue;

  funcValue = leastSquareWithLambda(initData, 1.0);

  bestFuncValue = funcValue;
  for(i=0; i<initData->nVars; i++)
    bestZ[i] = initData->vars[i] = initData->start[i];

  for(j=1; j<=200 && STOPCR < funcValue; j++)
  {
    infoStreamPrint(LOG_INIT, 0, "initialization-nr. %ld", j);

    if(useScaling)
      computeInitialResidualScalingCoefficients(initData);

    if(optiMethod == IOM_SIMPLEX)
      retVal = simplex_initialization(initData);
    else if(optiMethod == IOM_NEWUOA)
      retVal = newuoa_initialization(initData);
    else if(optiMethod == IOM_NELDER_MEAD_EX)
      retVal = nelderMeadEx_initialization(initData, &lambda, lambda_steps);
    else if(optiMethod == IOM_KINSOL)
      retVal = kinsol_initialization(initData);
    else if(optiMethod == IOM_KINSOL_SCALED)
      retVal = kinsol_initialization(initData);
    else if(optiMethod == IOM_IPOPT)
      retVal = ipopt_initialization(data, initData, 0);
    else
      throwStreamPrint(data->threadData, "unsupported option -iom");

    /*storePreValues(data);*/                       /* save pre-values */
    overwriteOldSimulationData(data);           /* if there are non-linear equations */
    updateDiscreteSystem(data);                 /* evaluate discrete variables */

    /* valid system for the first time! */
    saveZeroCrossings(data);
    /*storePreValues(data);*/                       /* save pre-values */
    overwriteOldSimulationData(data);

    funcValue = leastSquareWithLambda(initData, 1.0);

    if(retVal >= 0 && funcValue < bestFuncValue)
    {
      bestFuncValue = funcValue;
      for(i=0; i<initData->nVars; i++)
        bestZ[i] = initData->vars[i];
      infoStreamPrint(LOG_INIT, 0, "updating bestZ");
      dumpInitialization(data,initData);
    }
    else if(retVal >= 0 && funcValue == bestFuncValue)
    {
      /* warningStreamPrint("local minimum"); */
      infoStreamPrint(LOG_INIT, 0, "not updating bestZ");
      break;
    }
    else
      infoStreamPrint(LOG_INIT, 0, "not updating bestZ");
  }

  setZ(initData, bestZ);
  free(bestZ);

  infoStreamPrint(LOG_INIT, 0, "optimization-calls: %ld", j-1);

  return retVal;
}

/*! \fn static int initialize(DATA *data, int optiMethod)
 *
 *  \param [ref] [data]
 *  \param [in]  [optiMethod] specified optimization method
 *
 *  \author lochel
 */
static int initialize(DATA *data, int optiMethod, int lambda_steps)
{
  const double h = 1e-6;

  int retVal = -1;
  long i, j, k;
  double f;
  double *z_f = NULL;
  double* nominal;
  double funcValue;

  /* set up initData struct */
  INIT_DATA *initData = initializeInitData(data);

  /* no initial values to calculate */
  if(initData->nVars == 0)
  {
    infoStreamPrint(LOG_INIT, 0, "no variables to initialize");
    /* call initial_residual to execute algorithms with no counted outputs, for examples external objects as used in modelica3d */
    if(data->modelData.nInitResiduals == 0)
      data->callback->initial_residual(data, initData->initialResiduals);
    free(initData);
    return 0;
  }

  /* no initial equations given */
  if(data->modelData.nInitResiduals == 0)
  {
    infoStreamPrint(LOG_INIT, 0, "no initial residuals (neither initial equations nor initial algorithms)");
    /* call initial_residual to execute algorithms with no counted outputs, for examples external objects as used in modelica3d */
    data->callback->initial_residual(data, initData->initialResiduals);
    free(initData);
    return 0;
  }

  if(initData->nInitResiduals < initData->nVars)
  {
    infoStreamPrint(LOG_INIT, 1, "under-determined");

    z_f = (double*)malloc(initData->nVars * sizeof(double));
    nominal = initData->nominal;
    initData->nominal = NULL;
    f = leastSquareWithLambda(initData, 1.0);
    initData->nominal = nominal;
    for(i=0; i<initData->nVars; ++i)
    {
      initData->vars[i] += h;
      nominal = initData->nominal;
      initData->nominal = NULL;
      z_f[i] = fabs(leastSquareWithLambda(initData, 1.0) - f) / h;
      initData->nominal = nominal;
      initData->vars[i] -= h;
    }

    for(j=0; j < data->modelData.nInitResiduals; ++j)
    {
      k = 0;
      for(i=1; i<initData->nVars; ++i)
        if(z_f[i] > z_f[k])
          k = i;
      z_f[k] = -1.0;
    }

    k = 0;
    infoStreamPrint(LOG_INIT, 1, "setting fixed=true for:");
    for(i=0; i<data->modelData.nStates; ++i)
    {
      if(data->modelData.realVarsData[i].attribute.fixed == 0)
      {
        if(z_f[k] >= 0.0)
        {
          data->modelData.realVarsData[i].attribute.fixed = 1;
          infoStreamPrint(LOG_INIT, 0, "%s(fixed=true) = %g", initData->name[k], initData->vars[k]);
        }
        k++;
      }
    }
    for(i=0; i<data->modelData.nParametersReal; ++i)
    {
      if(data->modelData.realParameterData[i].attribute.fixed == 0)
      {
        if(z_f[k] >= 0.0)
        {
          data->modelData.realParameterData[i].attribute.fixed = 1;
          infoStreamPrint(LOG_INIT, 0, "%s(fixed=true) = %g", initData->name[k], initData->vars[k]);
        }
        k++;
      }
    for(i=data->modelData.nVariablesReal-data->modelData.nDiscreteReal; i<data->modelData.nDiscreteReal; ++i)
    {
      if(data->modelData.realParameterData[i].attribute.fixed == 0)
      {
        if(z_f[k] >= 0.0)
        {
          data->modelData.realParameterData[i].attribute.fixed = 1;
          infoStreamPrint(LOG_INIT, 0, "%s(fixed=true) = %g", initData->name[k], initData->vars[k]);
        }
        k++;
      }
    }

    }
    if (ACTIVE_STREAM(LOG_INIT)) {
      messageClose(LOG_INIT);
      messageClose(LOG_INIT);
    }

    free(z_f);

    freeInitData(initData);
    /* FIX */
    initData = initializeInitData(data);
    /* no initial values to calculate. (not possible to be here) */
    if(initData->nVars == 0)
    {
      infoStreamPrint(LOG_INIT, 0, "no initial values to calculate");
      free(initData);
      return 0;
    }
  }
  else if(data->modelData.nInitResiduals > initData->nVars)
  {
    infoStreamPrint(LOG_INIT, 0, "over-determined");

    /*
     * infoStreamPrint("initial problem is [over-determined]");
     * if(optiMethod == IOM_KINSOL)
     * {
     *   optiMethod = IOM_NELDER_MEAD_EX;
     *   infoStreamPrint("kinsol-method is unable to solve over-determined problems.");
     *   infoStreamPrint("| using %-15s [%s]", OPTI_METHOD_NAME[optiMethod], OPTI_METHOD_DESC[optiMethod]);
     * }
    */
  }

  /* with scaling */
  if(optiMethod == IOM_KINSOL_SCALED ||
     optiMethod == IOM_NELDER_MEAD_EX)
  {
    infoStreamPrint(LOG_INIT, 0, "start with scaling");

    initialize2(initData, optiMethod, 1, lambda_steps);

    dumpInitialization(data,initData);

    for(i=0; i<initData->nVars; ++i)
      initData->start[i] = initData->vars[i];
  }

  /* w/o scaling */
  funcValue = leastSquareWithLambda(initData, 1.0);
  if(1e-9 < funcValue)
  {
    if(initData->nominal)
    {
      free(initData->nominal);
      initData->nominal = NULL;
    }

    if(initData->residualScalingCoefficients)
    {
      free(initData->residualScalingCoefficients);
      initData->residualScalingCoefficients = NULL;
    }

    if(initData->startValueResidualScalingCoefficients)
    {
      free(initData->startValueResidualScalingCoefficients);
      initData->startValueResidualScalingCoefficients = NULL;
    }

    initialize2(initData, optiMethod, 0, lambda_steps);

    /* dump final solution */
    dumpInitialization(data,initData);

    funcValue = leastSquareWithLambda(initData, 1.0);
  }
  else
    infoStreamPrint(LOG_INIT, 0, "skip w/o scaling");

  infoStreamPrint(LOG_INIT, 1, "### FINAL INITIALIZATION RESULTS ###");
  dumpInitialization(data,initData);
  retVal = reportResidualValue(initData);
  messageClose(LOG_INIT);
  freeInitData(initData);

  return retVal;
}

/*! \fn static int numeric_initialization(DATA *data, int optiMethod, int lambda_steps)
 *
 *  \param [ref] [data]
 *  \param [in]  [optiMethod] specified optimization method
 *  \param [in]  [lambda_steps] number of steps
 *
 *  \author lochel
 */
static int numeric_initialization(DATA *data, int optiMethod, int lambda_steps)
{
  int retVal = 0;

  /* initial sample and delay before initial the system */
  initDelay(data, data->simulationInfo.startTime);

  /* initialize all relations that are ZeroCrossings */
  storePreValues(data);
  overwriteOldSimulationData(data);

  updateDiscreteSystem(data);

  /* and restore start values */
  restoreExtrapolationDataOld(data);
  initializeStateSetPivoting(data);   /* reset state selection */
  updateRelationsPre(data);
  storePreValues(data);

  retVal = initialize(data, optiMethod, lambda_steps);

  /*storePreValues(data);*/                 /* save pre-values */
  overwriteOldSimulationData(data);     /* if there are non-linear equations */
  updateDiscreteSystem(data);           /* evaluate discrete variables */

  /* valid system for the first time! */
  saveZeroCrossings(data);
  /*storePreValues(data);*/                 /* save pre-values */
  overwriteOldSimulationData(data);     /* if there are non-linear equations */

  return retVal;
}

/*! \fn static int symbolic_initialization(DATA *data)
 *
 *  \param [ref] [data]
 *
 *  \author lochel
 */
static int symbolic_initialization(DATA *data, long numLambdaSteps)
{
  long step;

  /* initial sample and delay before initial the system */
  initDelay(data, data->simulationInfo.startTime);

  /* initialize all relations that are ZeroCrossings */
  storePreValues(data);
  overwriteOldSimulationData(data);

  /* do pivoting for dynamic state selection */
  stateSelection(data, 0, 1);
  if (data->callback->useHomotopy && numLambdaSteps > 1) {
    long i;
    char buffer[4096];
    FILE *pFile = NULL;

    modelica_real* realVars = (modelica_real*)calloc(data->modelData.nVariablesReal, sizeof(modelica_real));
    modelica_integer* integerVars = (modelica_integer*)calloc(data->modelData.nVariablesInteger, sizeof(modelica_integer));
    modelica_boolean* booleanVars = (modelica_boolean*)calloc(data->modelData.nVariablesBoolean, sizeof(modelica_boolean));
    modelica_string* stringVars = (modelica_string*)calloc(data->modelData.nVariablesString, sizeof(modelica_string));
    MODEL_DATA *mData = &(data->modelData);

    assertStreamPrint(data->threadData, 0 != realVars, "out of memory");
    assertStreamPrint(data->threadData, 0 != integerVars, "out of memory");
    assertStreamPrint(data->threadData, 0 != booleanVars, "out of memory");
    assertStreamPrint(data->threadData, 0 != stringVars, "out of memory");

    for(i=0; i<mData->nVariablesReal; ++i)
      realVars[i] = mData->realVarsData[i].attribute.start;
    for(i=0; i<mData->nVariablesInteger; ++i)
      integerVars[i] = mData->integerVarsData[i].attribute.start;
    for(i=0; i<mData->nVariablesBoolean; ++i)
      booleanVars[i] = mData->booleanVarsData[i].attribute.start;
    for(i=0; i<mData->nVariablesString; ++i)
      stringVars[i] = mData->stringVarsData[i].attribute.start;

    if(ACTIVE_STREAM(LOG_INIT))
    {
      sprintf(buffer, "%s_homotopy.csv", mData->modelFilePrefix);
      pFile = fopen(buffer, "wt");
      fprintf(pFile, "%s,", "lambda");
      for(i=0; i<mData->nVariablesReal; ++i)
        fprintf(pFile, "%s,", mData->realVarsData[i].info.name);
      fprintf(pFile, "\n");
    }

    infoStreamPrint(LOG_INIT, 1, "homotopy process");
    for(step=0; step<numLambdaSteps; ++step)
    {
      data->simulationInfo.lambda = ((double)step)/(numLambdaSteps-1);

      if(data->simulationInfo.lambda > 1.0)
        data->simulationInfo.lambda = 1.0;

      data->callback->functionInitialEquations(data);

      infoStreamPrint(LOG_INIT, 0, "lambda = %g done", data->simulationInfo.lambda);

      if(ACTIVE_STREAM(LOG_INIT))
      {
        fprintf(pFile, "%.16g,", data->simulationInfo.lambda);
        for(i=0; i<mData->nVariablesReal; ++i)
          fprintf(pFile, "%.16g,", data->localData[0]->realVars[i]);
        fprintf(pFile, "\n");
      }

      if(check_nonlinear_solutions(data, 0) ||
         check_linear_solutions(data, 0) ||
         check_mixed_solutions(data, 0))
        break;

      setAllStartToVars(data);
    }
    messageClose(LOG_INIT);

    if(ACTIVE_STREAM(LOG_INIT))
      fclose(pFile);

    for(i=0; i<mData->nVariablesReal; ++i)
      mData->realVarsData[i].attribute.start = realVars[i];
    for(i=0; i<mData->nVariablesInteger; ++i)
      mData->integerVarsData[i].attribute.start = integerVars[i];
    for(i=0; i<mData->nVariablesBoolean; ++i)
      mData->booleanVarsData[i].attribute.start = booleanVars[i];
    for(i=0; i<mData->nVariablesString; ++i)
      mData->stringVarsData[i].attribute.start = stringVars[i];

    free(realVars);
    free(integerVars);
    free(booleanVars);
    free(stringVars);
  }
  else
  {
    data->simulationInfo.lambda = 1.0;
    data->callback->functionInitialEquations(data);
  }
  storeRelations(data);

  /* do pivoting for dynamic state selection if selection changed try again an */
  if(stateSelection(data, 1, 1) == 1)
  {
    data->callback->functionInitialEquations(data);
    storeRelations(data);

    /* report a warning about strange start values */
    if(stateSelection(data, 1, 1) == 1)
      warningStreamPrint(LOG_STDOUT, 0, "Cannot initialize the dynamic state selection in an unique way. Use -lv LOG_DSS to see the switching state set.");
  }

  /* check for over-determined systems */
  return data->callback->functionRemovedInitialEquations(data);
}

/*! \fn static char *mapToDymolaVars(const char *varname)
 *
 *  \param [in]  [varname]
 *
 *  converts a given variable name into dymola style
 *  ** der(foo.foo2) -> foo.der(foo2)
 *  ** foo.foo2[1,2,3] -> foo.foo2[1, 2, 3]
 *
 *  \author lochel
 */
static char *mapToDymolaVars(const char *varname)
{
  unsigned int varnameSize = strlen(varname);
  unsigned int level = 0;
  unsigned int i=0, j=0, pos=0;
  char* newVarname = NULL;
  unsigned int newVarnameSize = 0;

  newVarnameSize = varnameSize;
  for(i=0; i<varnameSize; i++)
  {
    if(varname[i] == '[')
      level++;
    else if(varname[i] == ']')
      level--;

    if(level > 0 && varname[i] == ',' && varname[i+1] != ' ')
      newVarnameSize++;
  }

  newVarname = (char*)malloc((newVarnameSize+1) * sizeof(char));
  for(i=0,j=0; i<newVarnameSize; i++,j++)
  {
    if(varname[j] == '[')
      level++;
    else if(varname[j] == ']')
      level--;

    newVarname[i] = varname[j];
    if(level > 0 && varname[j] == ',' && varname[j+1] != ' ')
    {
      i++;
      newVarname[i] = ' ';
    }
  }
  newVarname[newVarnameSize] = '\0';

  while(!memcmp((const void*)newVarname, (const void*)"der(", 4*sizeof(char)))
  {
    for(pos=newVarnameSize; pos>=4; pos--)
      if(newVarname[pos] == '.')
        break;

    if(pos == 3)
      break;

    memcpy((void*)newVarname, (const void*)(newVarname+4), (pos-3)*sizeof(char));
    memcpy((void*)(newVarname+pos-3), (const void*)"der(", 4*sizeof(char));
  }

  return newVarname;
}

/*! \fn static int importStartValues(DATA *data, const char *pInitFile, double initTime)
 *
 *  \param [ref] [data]
 *  \param [in]  [pInitFile]
 *  \param [in]  [initTime]
 *
 *  \author lochel
 */
static int importStartValues(DATA *data, const char *pInitFile, double initTime)
{
  ModelicaMatReader reader;
  ModelicaMatVariable_t *pVar = NULL;
  double value;
  const char *pError = NULL;
  char* newVarname = NULL;

  MODEL_DATA *mData = &(data->modelData);
  long i;

  infoStreamPrint(LOG_INIT, 0, "import start values\nfile: %s\ntime: %g", pInitFile, initTime);

  if(!strcmp(data->modelData.resultFileName, pInitFile))
  {
    errorStreamPrint(LOG_INIT, 0, "Cannot import a result file for initialization that is also the current output file <%s>.\nConsider redirecting the output result file (-r=<new_res.mat>) or renaming the result file that is used for initialization import.", pInitFile);
    return 1;
  }

  pError = omc_new_matlab4_reader(pInitFile, &reader);
  if(pError)
  {
    throwStreamPrint(data->threadData, "unable to read input-file <%s> [%s]", pInitFile, pError);
    return 1;
  } else {
    infoStreamPrint(LOG_INIT, 0, "import real variables");
    for(i=0; i<mData->nVariablesReal; ++i) {
      pVar = omc_matlab4_find_var(&reader, mData->realVarsData[i].info.name);

      if(!pVar) {
        newVarname = mapToDymolaVars(mData->realVarsData[i].info.name);
        pVar = omc_matlab4_find_var(&reader, newVarname);
        free(newVarname);
      }

      if(pVar) {
        omc_matlab4_val(&(mData->realVarsData[i].attribute.start), &reader, pVar, initTime);
        infoStreamPrint(LOG_INIT, 0, "| %s(start=%g)", mData->realVarsData[i].info.name, mData->realVarsData[i].attribute.start);
      } else {
        /* skipp warnings about self generated variables */
        if(((strncmp (mData->realVarsData[i].info.name,"$ZERO.",6) != 0) && (strncmp (mData->realVarsData[i].info.name,"$pDER.",6) != 0)) || ACTIVE_STREAM(LOG_INIT)) {
          warningStreamPrint(LOG_INIT, 0, "unable to import real variable %s from given file", mData->realVarsData[i].info.name);
        }
      }
    }

    infoStreamPrint(LOG_INIT, 0, "import real parameters");
    for(i=0; i<mData->nParametersReal; ++i)
    {
      pVar = omc_matlab4_find_var(&reader, mData->realParameterData[i].info.name);

      if(!pVar) {
        newVarname = mapToDymolaVars(mData->realParameterData[i].info.name);
        pVar = omc_matlab4_find_var(&reader, newVarname);
        free(newVarname);
      }

      if(pVar) {
        omc_matlab4_val(&(mData->realParameterData[i].attribute.start), &reader, pVar, initTime);
        infoStreamPrint(LOG_INIT, 0, "| %s(start=%g)", mData->realParameterData[i].info.name, mData->realParameterData[i].attribute.start);
      } else {
        warningStreamPrint(LOG_INIT, 0, "unable to import real parameter %s from given file", mData->realParameterData[i].info.name);
      }
    }

    infoStreamPrint(LOG_INIT, 0, "import real discrete");
    for(i=mData->nVariablesReal-mData->nDiscreteReal; i<mData->nDiscreteReal; ++i)
    {
      pVar = omc_matlab4_find_var(&reader, mData->realParameterData[i].info.name);

      if(!pVar) {
        newVarname = mapToDymolaVars(mData->realParameterData[i].info.name);
        pVar = omc_matlab4_find_var(&reader, newVarname);
        free(newVarname);
      }

      if(pVar) {
        omc_matlab4_val(&(mData->realParameterData[i].attribute.start), &reader, pVar, initTime);
        infoStreamPrint(LOG_INIT, 0, "| %s(start=%g)", mData->realParameterData[i].info.name, mData->realParameterData[i].attribute.start);
      } else {
        warningStreamPrint(LOG_INIT, 0, "unable to import real parameter %s from given file", mData->realParameterData[i].info.name);
      }
    }


    infoStreamPrint(LOG_INIT, 0, "import integer parameters");
    for(i=0; i<mData->nParametersInteger; ++i)
    {
      pVar = omc_matlab4_find_var(&reader, mData->integerParameterData[i].info.name);

      if(!pVar) {
        newVarname = mapToDymolaVars(mData->integerParameterData[i].info.name);
        pVar = omc_matlab4_find_var(&reader, newVarname);
        free(newVarname);
      }

      if(pVar) {
        omc_matlab4_val(&value, &reader, pVar, initTime);
        mData->integerParameterData[i].attribute.start = (modelica_integer)value;
        infoStreamPrint(LOG_INIT, 0, "| %s(start=%ld)", mData->integerParameterData[i].info.name, mData->integerParameterData[i].attribute.start);
      } else {
        warningStreamPrint(LOG_INIT, 0, "unable to import integer parameter %s from given file", mData->integerParameterData[i].info.name);
      }
    }

    infoStreamPrint(LOG_INIT, 0, "import boolean parameters");
    for(i=0; i<mData->nParametersBoolean; ++i)
    {
      pVar = omc_matlab4_find_var(&reader, mData->booleanParameterData[i].info.name);

      if(!pVar) {
        newVarname = mapToDymolaVars(mData->booleanParameterData[i].info.name);
        pVar = omc_matlab4_find_var(&reader, newVarname);
        free(newVarname);
      }

      if(pVar) {
        omc_matlab4_val(&value, &reader, pVar, initTime);
        mData->booleanParameterData[i].attribute.start = (modelica_boolean)value;
        infoStreamPrint(LOG_INIT, 0, "| %s(start=%s)", mData->booleanParameterData[i].info.name, mData->booleanParameterData[i].attribute.start ? "true" : "false");
      } else {
        warningStreamPrint(LOG_INIT, 0, "unable to import boolean parameter %s from given file", mData->booleanParameterData[i].info.name);
      }
    }
    omc_free_matlab4_reader(&reader);
  }

  return 0;
}

/*! \fn int initialization(DATA *data, const char* pInitMethod, const char* pOptiMethod, const char* pInitFile, double initTime)
 *
 *  \param [ref] [data]
 *  \param [in]  [pInitMethod] user defined initialization method
 *  \param [in]  [pOptiMethod] user defined optimization method
 *  \param [in]  [pInitFile] extra argument for initialization-method "file"
 *  \param [in]  [initTime] extra argument for initialization-method "file"
 *
 *  \author lochel
 */
int initialization(DATA *data, const char* pInitMethod, const char* pOptiMethod, const char* pInitFile, double initTime, int lambda_steps)
{
  int initMethod = data->callback->useSymbolicInitialization ? IIM_SYMBOLIC : IIM_NUMERIC; /* default method */
  int optiMethod = IOM_NELDER_MEAD_EX; /* default method */
  int retVal = -1;
  int i;

  TRACE_PUSH

  infoStreamPrint(LOG_INIT, 0, "### START INITIALIZATION ###");

  setAllParamsToStart(data);
  data->callback->updateBoundParameters(data);
  data->callback->updateBoundVariableAttributes(data);

  /* import start values from extern mat-file */
  if(pInitFile && strcmp(pInitFile, ""))
  {
    if(importStartValues(data, pInitFile, initTime))
    {
      TRACE_POP
      return 1;
    }
  }

  /* set up all variables with their start-values */
  setAllVarsToStart(data);

  /* update static data of non-linear system solvers */
  updateStaticDataOfNonlinearSystems(data);

  /* if there are user-specified options, use them! */
  if(pInitMethod && strcmp(pInitMethod, ""))
  {
    initMethod = IIM_UNKNOWN;

    for(i=1; i<IIM_MAX; ++i)
    {
      if(!strcmp(pInitMethod, INIT_METHOD_NAME[i]))
      {
        initMethod = i;
      }
    }

    if(initMethod == IIM_UNKNOWN)
    {
      warningStreamPrint(LOG_STDOUT, 0, "unrecognized option -iim %s", pInitMethod);
      warningStreamPrint(LOG_STDOUT, 0, "current options are:");
      for(i=1; i<IIM_MAX; ++i)
      {
        warningStreamPrint(LOG_STDOUT, 0, "| %-15s [%s]", INIT_METHOD_NAME[i], INIT_METHOD_DESC[i]);
      }
      throwStreamPrint(data->threadData, "see last warning");
    }
  }

  if(pOptiMethod && strcmp(pOptiMethod, ""))
  {
    optiMethod = IOM_UNKNOWN;

    for(i=1; i<IOM_MAX; ++i)
    {
      if(!strcmp(pOptiMethod, OPTI_METHOD_NAME[i]))
      {
        optiMethod = i;
      }
    }

    if(optiMethod == IOM_UNKNOWN)
    {
      warningStreamPrint(LOG_STDOUT, 0, "unrecognized option -iom %s", pOptiMethod);
      warningStreamPrint(LOG_STDOUT, 0, "current options are:");
      for(i=1; i<IOM_MAX; ++i)
      {
        warningStreamPrint(LOG_STDOUT, 0, "| %-15s [%s]", OPTI_METHOD_NAME[i], OPTI_METHOD_DESC[i]);
      }
      throwStreamPrint(data->threadData, "see last warning");
    }
  }

  infoStreamPrint(LOG_INIT, 0, "initialization method: %-15s [%s]", INIT_METHOD_NAME[initMethod], INIT_METHOD_DESC[initMethod]);
  if(initMethod == IIM_NUMERIC)
  {
    infoStreamPrint(LOG_INIT, 0, "optimization method:   %-15s [%s]", OPTI_METHOD_NAME[optiMethod], OPTI_METHOD_DESC[optiMethod]);
  }

  /* start with the real initialization */
  data->simulationInfo.initial = 1;             /* to evaluate when-equations with initial()-conditions */

  /* initialize all (nonlinear|linear|mixed) systems
   * This is a workaround and should be removed as soon as possible.
   */
  for(i=0; i<data->modelData.nNonLinearSystems; ++i)
  {
    data->simulationInfo.nonlinearSystemData[i].solved = 1;
  }
  for(i=0; i<data->modelData.nLinearSystems; ++i)
  {
    data->simulationInfo.linearSystemData[i].solved = 1;
  }
  for(i=0; i<data->modelData.nMixedSystems; ++i)
  {
    data->simulationInfo.mixedSystemData[i].solved = 1;
  }
  /* end workaround */

  /* select the right initialization-method */
  if(IIM_NONE == initMethod)
  {
    retVal = 0;
  }
  else if(IIM_NUMERIC == initMethod)
  {
    retVal = numeric_initialization(data, optiMethod, lambda_steps);
  }
  else if(IIM_SYMBOLIC == initMethod)
  {
    retVal = symbolic_initialization(data, lambda_steps);
  }
  else
  {
    throwStreamPrint(data->threadData, "unsupported option -iim");
  }

  /* check for unsolved (nonlinear|linear|mixed) systems
   * This is a workaround and should be removed as soon as possible.
   */
  if(check_nonlinear_solutions(data, 1))
  {
    retVal = -2;
  }
  else if(check_linear_solutions(data, 1))
  {
    retVal = -3;
  }
  else if(check_mixed_solutions(data, 1))
  {
    retVal = -4;
  }
  /* end workaround */

  dumpInitialSolution(data);
  infoStreamPrint(LOG_INIT, 0, "### END INITIALIZATION ###");

  data->simulationInfo.initial = 0;
  /* initialization is done */

  storePreValues(data);                 /* save pre-values */
  updateDiscreteSystem(data);           /* evaluate discrete variables (event iteration) */
  saveZeroCrossings(data);

  initSample(data, data->simulationInfo.startTime, data->simulationInfo.stopTime);
  data->callback->function_storeDelayed(data);
  data->callback->function_updateRelations(data, 1);

  /* valid system for the first time! */
  TRACE_POP
  return retVal;
}
