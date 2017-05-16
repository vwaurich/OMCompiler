/**
 *  \file osi_factory.cpp
 *  \brief Brief
 */
//Cpp Simulation kernel includes
#include <Core/ModelicaDefine.h>
#include <Core/Modelica.h>
#include <osi_global_settings.h>
#include <osi_factory.h>
#include <Core/System/SimObjects.h>
#include <Core/SimController/ISimController.h>


shared_ptr<IMixedSystem>  createOSUSystem(shared_ptr<OSIGlobalSettings> globalSettings,string instanceName)
 {

		   //instantiate osu system
          shared_ptr<IMixedSystem> osu  = createOSU(dynamic_pointer_cast<IGlobalSettings>(globalSettings));

          return osu;


 }



