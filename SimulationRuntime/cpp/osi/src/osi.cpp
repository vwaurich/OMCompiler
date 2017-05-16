/**
 *  \file osi.cpp
 *  \brief Brief
 */


//Cpp Simulation kernel includes
#include <Core/ModelicaDefine.h>
#include <Core/Modelica.h>
#include <Core/SimController/ISimController.h>
#include <Core/System/FactoryExport.h>
#include <Core/Utils/extension/logger.hpp>
#ifdef RUNTIME_STATIC_LINKING
   #include <SimCoreFactory/OMCFactory/StaticOMCFactory.h>
#endif


//OpenModelica Simulation Interface
#include <osi.h>



#include <boost/filesystem/operations.hpp>
#include <boost/filesystem/path.hpp>
namespace fs = boost::filesystem;



#if defined(_MSC_VER) || defined(__MINGW32__)
#include <tchar.h>
int _tmain(int argc, const _TCHAR* argv[])
#else
int main(int argc, const char* argv[])
#endif
{


	// default program options
    std::map<std::string, std::string> opts;

	try
    {
          Logger::initialize();
          Logger::setEnabled(true);

          #ifdef RUNTIME_STATIC_LINKING
            shared_ptr<StaticOMCFactory>  _factory =  shared_ptr<StaticOMCFactory>(new StaticOMCFactory());
          #else
            shared_ptr<OMCFactory>  _factory =  shared_ptr<OMCFactory>(new OMCFactory());
          #endif //RUNTIME_STATIC_LINKING
          //SimController to start simulation

          std::pair<shared_ptr<ISimController>, SimSettings> simulation = _factory->createSimulation(argc, argv, opts);

          //create OSU system
          fs::path osu_path(simulation.second.osuPath);
          fs::path osu_name(simulation.second.osuName);
          osu_path/=osu_name;
          weak_ptr<IMixedSystem> system = simulation.first->LoadOSUSystem(osu_path.string(),simulation.second.osuName);
          simulation.first->Start(simulation.second, simulation.second.osuName);


          return 0;

    }
    catch(ModelicaSimulationError& ex)
    {
        if(!ex.isSuppressed())
            std::cerr << "Simulation stopped with error in " << error_id_string(ex.getErrorID()) << ": "  << ex.what();
        return 1;
    }
}