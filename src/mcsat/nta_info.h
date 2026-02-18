
#ifndef MCSAT_NTA_INFO_H_
#define MCSAT_NTA_INFO_H_

#include "utils/int_hash_map.h"
#include "utils/int_hash_sets.h"
#include "utils/int_vectors.h"
#include "mcsat/variable_db.h"
#include "yices.h"

#include <stdint.h>

struct preprocessor_s;
typedef struct preprocessor_s preprocessor_t;

typedef enum taylor_center_kind taylor_center_kind_t;

/** Kind of Taylor polarity produced for sin */
typedef enum {
  NTA_TAYLOR_POLARITY_UPPER = 0,
  NTA_TAYLOR_POLARITY_LOWER = 1
} nta_taylor_polarity_kind_t;

typedef struct {
  /** True if NTA features (sin/pi) are present */
  bool is_nta;
  /** True iff the user set the delta parameter */
  bool delta_mode;
  /** User-specified delta value (valid iff delta_mode is true) */
  int32_t delta;
  /** Whether delta was used in a consistency check */
  bool delta_used;
  /** Constraints where delta was used to accept NTA_TRUE_OR_FALSE */
  int_hset_t delta_used_constraints;
  /** Map from a term t to the term representing sin(t) */
  int_hmap_t sin_map;
  /** Map from a term t to the term t' such that t represents sin(t') */
  int_hmap_t inverse_sin_map;
  /** Map from a term t to the term representing exp(t) */
  int_hmap_t exp_map;
  /** Map from a term t to the term t' such that t represents exp(t') */
  int_hmap_t inverse_exp_map;
  /** Abstracted symbol for pi (optional) */
  
  term_t pi;
  /** Whether to use the period variable for sin abstraction */
  bool use_period_for_sin;
  /** Map from a term t to an integer term i representing the period of sin(t) */
  int_hmap_t sin_period_map;
  /** Inverse map from period integer term i to original term t */
  int_hmap_t inverse_sin_period_map;
  /** Map from (term, center, polarity) to last Taylor degree used for sin(t) */
  int_hmap_t sin_taylor_degree_map;
  /** Set of equations introduced for arg abstraction: (fresh = arg1) */
  int_hset_t nta_arg_equations;
  /** Map from complex arg term -> fresh variable */
  int_hmap_t arg_map;
  /** Inverse map from fresh variable -> complex arg term */
  int_hmap_t inverse_arg_map;
  /** Set of NTA lemma variables added by the plugin */
  int_hset_t nta_lemmas_variables;
  /** Pointer to preprocessor (for access to preprocess_map) */
  preprocessor_t* preprocessor;
  /** Set of atoms from the original preprocessed formula */
  int_hset_t original_atoms;
  /** Map from term -> index in nta_watchlist_lists (constraints waiting for full check) */
  int_hmap_t nta_watchlist;
  /** Vector of ivector_t* (one list of constraint variables per watched term) */
  void **nta_watchlist_lists;
} nta_info_t;

/** Init the nta_info_t */
void nta_info_init(nta_info_t *nta_info);

/** Destructs the nta_info_t */
void nta_info_destruct(nta_info_t *nta_info);

/** Get whether NTA features are present */
bool nta_info_is_nta(const nta_info_t *nta_info);

/** Set if NTA features are present */
void nta_info_set_is_nta(nta_info_t *nta_info);

/** Set abstraction */
void nta_info_set_sin_abstraction(nta_info_t *nta_info, term_t t1, term_t t2, term_t i);

/** Set abstraction representing exp(t1)=t2 */
void nta_info_set_exp_abstraction(nta_info_t *nta_info, term_t t1, term_t t2);

/** Set pi abstraction */
void nta_info_set_pi(nta_info_t *nta_info, term_t pi_term);

/** Get pi abstraction */
term_t nta_info_get_pi(const nta_info_t *nta_info);

/** Get sin period term (i) for a given term t */
term_t nta_info_get_sin_period_term(const nta_info_t *nta_info, term_t t);

/** Get inverse sin period term (t) for a given period term i */
term_t nta_info_get_sin_period_inverse_term(const nta_info_t *nta_info, term_t i);

/** Get inverse term from abstracted sin term (i.e. given y it returns x so that sin(x)=y) */
term_t nta_info_get_sin_inverse_term(const nta_info_t *nta_info, term_t sin_term);

/** Get sin term (i.e. given x it returns y so that sin(x)=y) */
term_t nta_info_get_sin_term(const nta_info_t *nta_info, term_t arg_term);

/** Get inverse term from abstracted exp term (i.e. given y it returns x so that exp(x)=y) */
term_t nta_info_get_exp_inverse_term(const nta_info_t *nta_info, term_t exp_term);

/** Get exp term (i.e. given x it returns y so that exp(x)=y) */
term_t nta_info_get_exp_term(const nta_info_t *nta_info, term_t arg_term);

/** Get fresh variable from complex arg term (checks preprocess_map too) */
term_t nta_info_get_arg_term(const nta_info_t *nta_info, term_t arg_term);

/** Get complex arg term from fresh variable (checks preprocess_map too) */
term_t nta_info_get_inverse_arg_term(const nta_info_t *nta_info, term_t fresh_term);

/** Check whether a term is an arg abstraction equation (checks preprocess_map too) */
bool nta_info_is_arg_equation(const nta_info_t *nta_info, term_t t);

/** Get the last Taylor degree used for a given (term, center, polarity); returns -1 if none */
int nta_info_get_last_taylor_degree(const nta_info_t *nta_info, term_t t, taylor_center_kind_t center, nta_taylor_polarity_kind_t polarity);

/** Set the last Taylor degree used for a given (term, center), polarity derived from degree */
void nta_info_set_last_taylor_degree(nta_info_t *nta_info, term_t t, taylor_center_kind_t center, int degree);

/** Return next Taylor degree for sin: (last_degree + 1) or 1 if none */
int next_taylor_degree_for_sin(const nta_info_t *nta_info, term_t t, taylor_center_kind_t center, nta_taylor_polarity_kind_t polarity);

/** Return initial Taylor degree for a given center/polarity */
int nta_taylor_initial_degree(taylor_center_kind_t center, nta_taylor_polarity_kind_t polarity);

/** Record a lemma variable added by the NTA plugin */
void nta_info_add_nta_lemma_variable(nta_info_t *nta_info, variable_t var);

/** Check whether the variable corresponds to an NTA lemma */
bool nta_info_has_nta_lemma_variable(const nta_info_t *nta_info, variable_t var);

/** Reset the recorded lemma variables */
void nta_info_reset_nta_lemma_variables(nta_info_t *nta_info);

/** Add constraint variable to the watchlist of term */
void nta_info_watchlist_add(nta_info_t *nta_info, term_t term, variable_t cstr_var);

/** Get the watchlist of term (NULL if none) */
const ivector_t* nta_info_watchlist_get(const nta_info_t *nta_info, term_t term);

/** Clear the watchlist of term */
void nta_info_watchlist_clear(nta_info_t *nta_info, term_t term);

#endif

