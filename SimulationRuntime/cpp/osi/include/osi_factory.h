#ifndef OIS_FACTORY_H
#define OIS_FACTORY_H


shared_ptr<IMixedSystem> createOSU(shared_ptr<IGlobalSettings> globalSettings);
shared_ptr<IMixedSystem> createOSUSystem(shared_ptr<OSIGlobalSettings> globalSettings,string instanceName);


#endif