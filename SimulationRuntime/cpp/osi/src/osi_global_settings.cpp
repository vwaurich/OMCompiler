/** @addtogroup coreSimulationSettings
 *
 *  @{
 */

#include <Core/ModelicaDefine.h>
#include <Core/Modelica.h>
//#define BOOST_EXTENSION_GLOBALSETTINGS_DECL BOOST_EXTENSION_EXPORT_DECL
#include <osi_global_settings.h>

OSIGlobalSettings::OSIGlobalSettings()
  : _startTime(0.0)
  , _endTime(5.0)
  , _hOutput(0.001)
  , _emitResults(EMIT_ALL)
  , _infoOutput(true)
  , _selected_solver("Euler")
  , _selected_lin_solver("linearSolver")
  , _selected_nonlin_solver("Newton")
  , _resultsfile_name("results.csv")
  , _endless_sim(false)
  , _nonLinSolverContinueOnError(false)
  , _outputPointType(OPT_ALL)
  , _alarm_time(0)
  , _outputFormat(MAT)
  ,_init_file_path("")
{
}

OSIGlobalSettings::~OSIGlobalSettings()
{
}

///< Start time of integration (default: 0.0)
double OSIGlobalSettings::getStartTime()
{
  return _startTime;
}

void OSIGlobalSettings::setStartTime(double time)
{
  _startTime = time;
}

///< End time of integraiton (default: 1.0)
double OSIGlobalSettings::getEndTime()
{
  return _endTime;
}

void OSIGlobalSettings::setEndTime(double time)
{
  _endTime = time;
}

///< Output step size (default: 20 ms)
double OSIGlobalSettings::gethOutput()
{
  return _hOutput;
}

void OSIGlobalSettings::sethOutput(double h)
{
  _hOutput = h;
}

bool OSIGlobalSettings::useEndlessSim()
{
  return _endless_sim ;
}

void OSIGlobalSettings::useEndlessSim(bool endles)
{
  _endless_sim = endles;
}

OutputPointType OSIGlobalSettings::getOutputPointType()
{
  return _outputPointType;
}

void OSIGlobalSettings::setOutputPointType(OutputPointType type)
{
  _outputPointType = type;
}

LogSettings OSIGlobalSettings::getLogSettings()
{
  return _log_settings;
}

void OSIGlobalSettings::setLogSettings(LogSettings set)
{
  _log_settings = set;
}

///< Write out results (default: EMIT_ALL)
EmitResults OSIGlobalSettings::getEmitResults()
{
  return _emitResults;
}

void OSIGlobalSettings::setEmitResults(EmitResults emitResults)
{
  _emitResults = emitResults;
}

void OSIGlobalSettings::setResultsFileName(string name)
{
  _resultsfile_name = name;
}

string  OSIGlobalSettings::getResultsFileName()
{
  return _resultsfile_name;
}

///< Write out statistical simulation infos, e.g. number of steps (at the end of simulation); [false,true]; default: true)
bool OSIGlobalSettings::getInfoOutput()
{
  return _infoOutput;
}

void OSIGlobalSettings::setInfoOutput(bool output)
{
  _infoOutput = output;
}

string OSIGlobalSettings::getOutputPath()
{
  return _output_path ;
}
 string OSIGlobalSettings::getInitfilePath()
 {
        return _init_file_path;
 }
 void OSIGlobalSettings::setInitfilePath(string path)
 {
        _init_file_path = path;
 }
void OSIGlobalSettings::setOutputPath(string path)
{
  _output_path = path;
}

string OSIGlobalSettings::getSelectedSolver()
{
  return _selected_solver;
}

void OSIGlobalSettings::setSelectedSolver(string solver)
{
  _selected_solver = solver;
}

string   OSIGlobalSettings::getSelectedLinSolver()
{
  return _selected_lin_solver;
}

void OSIGlobalSettings::setSelectedLinSolver(string solver)
{
  _selected_lin_solver = solver;
}

string OSIGlobalSettings::getSelectedNonLinSolver()
{
  return _selected_nonlin_solver;
}

void OSIGlobalSettings::setSelectedNonLinSolver(string solver)
{
  _selected_nonlin_solver = solver;
}

/**
initializes settings object by an xml file
*/
void OSIGlobalSettings::load(std::string xml_file)
{
}

void OSIGlobalSettings::setRuntimeLibrarypath(string path)
{
  _runtimeLibraryPath = path;
}

string OSIGlobalSettings::getRuntimeLibrarypath()
{
  return _runtimeLibraryPath;
}

void OSIGlobalSettings::setAlarmTime(unsigned int t)
{
  _alarm_time = t;
}

unsigned int OSIGlobalSettings::getAlarmTime()
{
  return _alarm_time;
}

void OSIGlobalSettings::setNonLinearSolverContinueOnError(bool value)
{
  _nonLinSolverContinueOnError = value;
}

bool OSIGlobalSettings::getNonLinearSolverContinueOnError()
{
  return _nonLinSolverContinueOnError;
}

void OSIGlobalSettings::setSolverThreads(int val)
{
  _solverThreads = val;
}

int OSIGlobalSettings::getSolverThreads()
{
  return _solverThreads;
}

 OutputFormat OSIGlobalSettings::getOutputFormat()
 {
     return _outputFormat;
 }
  void OSIGlobalSettings::setOutputFormat(OutputFormat outputFormat)
  {
      _outputFormat = outputFormat;
  }
/** @} */ // end of coreSimulationSettings
