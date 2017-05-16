#ifndef OIS_CALLBACKS_H
#define OIS_CALLBACKS_H

#ifdef __cplusplus
extern "C" {
#endif

int evaluate_ode(osi_t);
int evaluate_outputs(osi_t);
int evaluate_zerocrossings(osi_t);
int evaluate_discrete_system(osi_t);
int evaluate_bound_parameter(osi_t);
int evaluate_intial_system(osi_t);

#ifdef __cplusplus
}  /* end of extern "C" { */
#endif

#endif