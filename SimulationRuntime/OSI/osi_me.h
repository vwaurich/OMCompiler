#ifndef OIS_ME_H
#define OIS_ME_H


#ifdef __cplusplus
extern "C" {
#endif

struct  osi_event_info_t
{
	//has event iteration converged
	bool iteration_converged;
    //is simulation stopped
	bool terminate_simulation;
    // has next time
	bool next_event_time_defined;
    // next time event
	double  next_event_time;
	// change dynamic state selection
	bool state_value_references_changed;
};


//called from fmi2_instantiate
int osi_me_init(osi_t* osi, const char* GUID, const char* resource_location);
//call from fmi2_setup_expriment
void osi_setup_experiment(osi_t* osi, bool tolerance_defined,
                          double relative_tolerance);
//called from fmi2_enter_intialization_mode
int osi_initialize(osi_t* osi);
//called from fmi2_set_real
int osi_set_real(osi_t* osi, const int vr[], size_t nvr, const double value[]);
//called from fmi2_set_integer
int osi_set_integer(osi_t* osi, const int vr[], size_t nvr, const int value[]);
//called from fmi2_set_boolean
int osi_set_boolean(osi_t* osi, const int vr[], size_t nvr, const bool value[]);
//called from fmi2_set_string
int osi_set_string(osi_t* osi, const int vr[], size_t nvr, const const char* value[]);
//called from fmi2_get_real
int osi_get_real(osi_t* osi, const int vr[], size_t nvr, double value[]);
//called from fmi2_get_integer
int osi_get_integer(osi_t* osi, const int vr[], size_t nvr, int value[]);
//called from fmi2_get_boolean
int osi_get_boolean(osi_t* osi, const int vr[], size_t nvr, bool value[]);
//called from fmi2_get_string
int osi_get_string(osi_t* osi, const int vr[], size_t nvr, const char*  value[]);
//called from fmi2_get_directional_derivative
int osi_get_directional_derivative(osi_t* osi,
                const int vUnknown_ref[], size_t nUnknown,
                const int vKnown_ref[],   size_t nKnown,
                const double dvKnown[], double dvUnknown[]);

//called from fmi2_get_derivatives
int osi_get_derivatives(osi_t* osi, double derivatives[] , size_t nx);
//called from fmi2_get_event_indicators
int osi_get_event_indicators(osi_t* osi, double eventIndicators[], size_t ni);
//called from fmi2_get_nominals_of_continuous_states
int osi_get_nominal_continuous_states(osi_t* osi, double x_nominal[], size_t nx);
//called from fmi2_completed_integrator_step
int osi_completed_integrator_step(osi_t* osi, double* triggered_event);
//called from fmi2_set_time
int osi_set_time(osi_t* osi, double time);
//called from  fmi2_set_continuous_states
int osi_set_continuous_states(osi_t* osi, const double x[], size_t nx);
//called from fmi2_terminate
int osi_terminate(osi_t* osi);
//called from fmi2_terminate
int osi_terminate(osi_t* osi);


int osi_next_time_event(osi_t* osi);

#ifdef __cplusplus
}  /* end of extern "C" { */
#endif

#endif
