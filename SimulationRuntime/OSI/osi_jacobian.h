#ifndef _OSI_JACOBIAN_H
#define _OSI_JACOBIAN_H

#ifdef __cplusplus
extern "C" {
#endif

struct osi_sparsity_pattern
{
  unsigned int  number_non_zeros;
  unsigned int* colindex;
  unsigned int* rowindex;
};

#ifdef __cplusplus
}  /* end of extern "C" { */
#endif

#endif
