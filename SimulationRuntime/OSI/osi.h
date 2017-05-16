#ifndef _OSI_H
#define _OSI_H

#ifdef __cplusplus
extern "C" {
#endif


#include "osi_eqns_system.h"


/* forward some types */


 /**
  *   for delay handling
  */
struct RINGBUFFER;

/**
 *  simulation parameter
 */
struct osi_experiment_t
{
	double start_time;
	double stop_time;
	double step_size;
	unsigned int num_outputs;
	double tollerance;
	const char * solver_name;
};

/**
 *   additional file information for debugging
 */
struct file_info
{
	const char* filename;
	int lineStart;
	int colStart;
	int lineEnd;
	int colEnd;
	int readonly;
};
/**
 *   additional equation information for debugging
 */
 struct equation_info_t
 {
  int id;
  int profileBlockIndex;
  int parent;
  int numVar;      // number of unknown variables
  int* variables;  // unknown variables
};

/**
 *   variable attributes
 */
enum var_type {
  TYPE_UNKNOWN = 0,

  TYPE_REAL,
  TYPE_INTEGER,
  TYPE_BOOL,
  TYPE_STRING,

  TYPE_MAX
};

/**
 * real variable attributes
 */
 struct real_var_attribute_t
{
	const char * unit; /* = "" */
	const char * displayUnit; /* = "" */
	double min; /* = -Inf */
	double max; /* = +Inf */
	bool fixed; /* depends on the type */
	bool useNominal; /* = false */
	double nominal; /* = 1.0 */
	bool useStart; /* = false */
	double start; /* = 0.0 */
};
/**
 * integer variable attributes
 */
struct int_var_attribute_t
{
	int min; /* = -Inf */
	int max; /* = +Inf */
	bool fixed; /* depends on the type */
	bool useStart; /* = false */
	int start; /* = 0 */
};
/**
 * boolean variable attributes
 */
struct bool_var_attribute_t
{
	bool fixed; /* depends on the type */
	bool useStart; /* = false */
	bool start; /* = false */
};
/**
 * string variable attributes
 */
struct string_var_attribute_t
{
	bool useStart; /* = false */
	bool start; /* = "" */
};

/**
 *
 */
struct model_variable_info_t
{
	int id;
	const char *name;
	const char *comment;
	int var_type;
	//pointer to variable attribute e.g real_var_attribute
	void* attribute;
	file_info info;
};
/**
 *
 */
struct state_set_t
{
  int nCandidates;
  int nStates;
  int nDummyStates;    /* nCandidates - nStates */

  model_variable_info_t* A;
  int* rowPivot;
  int* colPivot;
  double* J;

  model_variable_info_t** states;
  model_variable_info_t** statescandidates;

  /* jacobian */
  int (*get_jacobian)(sim_data_t* data, void* matrix);
};


/**
 *
 */
struct model_data_t
{
	unsigned int n_states;
	unsigned int n_derivatives;
	unsigned int n_real_vars;
	unsigned int n_int_vars;
	unsigned int n_bool_vars;
	unsigned int n_string_vars;
	unsigned int n_real_parameters;
	unsigned int n_int_parameters;
	unsigned int n_bool_parameters;
	//number of zero crossings
	unsigned int n_zerocrossings;
	model_variable_info_t* model_vars_info_t;
	equation_info_t*  equation_info_t;
};
/**
 *
 */
struct sim_data_t
{
	double* real_vars;
	int* int_vars;
	bool* bool_vars;
	//start index of state variables in real vars array
	unsigned int states_index;
	//start index of derivative variables in real vars array
	unsigned int der_states_index;
    //start index of input real variables in real vars array
	unsigned int inputs_real_index;
	//start index of input integer variables in real vars array
	unsigned int inputs_int_index;
	//start index of input boolean variables in real vars array
	unsigned int inputs_bool_index;
     //start index of output real variables in real vars array
	unsigned int outputs_real_index;
	  //start index of output integer variables in integer vars array
	unsigned int outputs_int_index;
	 //start index of output boolean variables in boolean vars array
	unsigned int outputs_bool_index;
     //start index of discrete real variables in real vars array
	unsigned int discrete_reals_index;

	double* pre_real_vars;
	int* pre_int_vars;
	bool* pre_bool_vars;
	//conditions of zerocrossing functions
	bool* zerocrossings_vars;
	//pre conditions of zerocrossing functions
	bool* pre_zerocrossings_vars;
};

/*
 * type to separate the different solving stages.
 */
typedef enum {
	osi_instantiated_mode,
	osi_initialization_mode,
	osi_continuousTime_mode,
	osi_event_mode,
	osi_none_mode
} osi_solving_mode_t;


/**
 *
 */
struct osi_t
{
	model_data_t model_data;
	sim_data_t sim_data;
	osi_experiment_t* experiment;

};


int osi_initiatiate_osu(osi_t** osi);
int osi_initialize_model(osi_t** osi);
int osi_initialize_solver(osi_t** osi);
int osi_intialize_simulation(osi_t** osi);

#ifdef __cplusplus
}  /* end of extern "C" { */
#endif

#endif
