cmake_minimum_required(VERSION 2.8.9)

project(${SimControllerName})

add_library(${SimControllerName} Configuration.cpp  FactoryExport.cpp Initialization.cpp SimController.cpp SimManager.cpp )

if(NOT BUILD_SHARED_LIBS)
  set_target_properties(${SimControllerName} PROPERTIES COMPILE_DEFINITIONS "RUNTIME_STATIC_LINKING;ENABLE_SUNDIALS_STATIC")
endif(NOT BUILD_SHARED_LIBS)

target_link_libraries(${SimControllerName} ${OMCFactoryName} ${ExtensionUtilitiesName} ${ModelicaUtilitiesName} ${Boost_LIBRARIES} ${CMAKE_DL_LIBS})
add_precompiled_header(${SimControllerName} runtime/include/Core/Modelica.h)

install(TARGETS ${SimControllerName} DESTINATION ${LIBINSTALLEXT})
install(FILES
  ${CMAKE_SOURCE_DIR}/runtime/include/Core/SimController/ISimData.h
  ${CMAKE_SOURCE_DIR}/runtime/include/Core/SimController/ISimController.h
  ${CMAKE_SOURCE_DIR}/runtime/include/Core/SimController/SimController.h
  ${CMAKE_SOURCE_DIR}/runtime/include/Core/SimController/SimManager.h
  ${CMAKE_SOURCE_DIR}/runtime/include/Core/SimController/SimController.h
  ${CMAKE_SOURCE_DIR}/runtime/include/Core/SimController/SimManager.h
  ${CMAKE_SOURCE_DIR}/runtime/include/Core/SimController/Configuration.h
  ${CMAKE_SOURCE_DIR}/runtime/include/Core/SimController/Initialization.h
  DESTINATION include/omc/cpp/Core/SimController)
