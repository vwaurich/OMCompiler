#Cpp Simulation  for OpenModelica Simulation Interface (OSI)
PROJECT(OSICPP)
SET(CMAKE_VERBOSE_MAKEFILE ON)


#include path for OpenModelica Simulation Interface (OSI)
include_directories ("../../OSI")
include_directories ("${CMAKE_SOURCE_DIR}/osi/include")
include_directories ("${CMAKE_SOURCE_DIR}/osi/src")
# FMI 2.0 Header
include_directories ("${CMAKE_SOURCE_DIR}/../../3rdParty/FMIL/ThirdParty/FMI/default/FMI2")

add_library(${OSUName} STATIC src/fmi2/osi_fmi2_me.cpp src/fmi2/detail/osi_fmi2_log.cpp src/fmi2/detail/osi_fmi2_wrapper.cpp src/osi_factory.cpp src/osi_global_settings.cpp  )
IF(WIN32)
    target_link_libraries(${OSUName}  ${OMCFactoryName} ${SimControllerName} ${ExtensionUtilitiesName} ${ModelicaUtilitiesName} ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} wsock32 ws2_32)
ELSE(WIN32)
    target_link_libraries(${OSUName} ${OMCFactoryName}  ${SimControllerName} ${ExtensionUtilitiesName} ${ModelicaUtilitiesName} ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} )
ENDIF(WIN32)

install(TARGETS ${OSUName} DESTINATION ${LIBINSTALLEXT})


IF(BUILD_SHARED_LIBS)
	add_executable(${OSUSimName} src/osi.cpp )

    IF(WIN32)
		target_link_libraries(${OSUSimName} ${OMCFactoryName} ${ExtensionUtilitiesName} ${ModelicaUtilitiesName} ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} wsock32 ws2_32)
        target_link_libraries(${OSUName}  ${OMCFactoryName} ${SimControllerName} ${ExtensionUtilitiesName} ${ModelicaUtilitiesName} ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} wsock32 ws2_32)
	ELSE(WIN32)
		target_link_libraries(${OSUSimName} ${OMCFactoryName} ${ExtensionUtilitiesName} ${ModelicaUtilitiesName} ${Boost_LIBRARIES} ${CMAKE_DL_LIBS})
        target_link_libraries(${OSUName} ${OMCFactoryName}  ${SimControllerName} ${ExtensionUtilitiesName} ${ModelicaUtilitiesName} ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} )
    ENDIF(WIN32)

set_target_properties(${OSUName} PROPERTIES COMPILE_DEFINITIONS "RUNTIME_STATIC_LINKING;ENABLE_SUNDIALS_STATIC")
install(TARGETS ${OSUSimName} DESTINATION bin)
ENDIF(BUILD_SHARED_LIBS)





