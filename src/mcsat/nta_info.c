#include "mcsat/nta_info.h"
#include "mcsat/na/nta_functions.h"
#include "mcsat/preprocessor.h"
#include "utils/pointer_vectors.h"
#include "utils/memalloc.h"
#include <limits.h>

/** 
 * Given an abstraction of sin(x) with a fresh variable y, then we have the mappings:
 * sin_map: x -> y
 * inverse_sin_map: y -> x
*/


/** Init the nta_info_t */
void nta_info_init(nta_info_t *nta_info) {
  nta_info->is_nta = false;
  nta_info->delta_mode = false;
  nta_info->delta = 0;
  nta_info->delta_used = false;
  init_int_hset(&nta_info->delta_used_constraints, 0);
  init_int_hmap(&nta_info->sin_map, 0);
  init_int_hmap(&nta_info->inverse_sin_map, 0);
  init_int_hmap(&nta_info->exp_map, 0);
  init_int_hmap(&nta_info->inverse_exp_map, 0);
  nta_info->pi = NULL_TERM;
  nta_info->use_period_for_sin = true;
  init_int_hmap(&nta_info->sin_period_map, 0);
  init_int_hmap(&nta_info->inverse_sin_period_map, 0);
  init_int_hmap(&nta_info->sin_taylor_degree_map, 0);
  init_int_hset(&nta_info->nta_arg_equations, 0);
  init_int_hmap(&nta_info->arg_map, 0);
  init_int_hmap(&nta_info->inverse_arg_map, 0);
  init_int_hset(&nta_info->nta_lemmas_variables, 0);
  nta_info->preprocessor = NULL;
  init_int_hset(&nta_info->original_atoms, 0);
  init_int_hmap(&nta_info->nta_watchlist, 0);
  nta_info->nta_watchlist_lists = NULL;
}

bool nta_info_is_nta(const nta_info_t *nta_info) {
  return nta_info->is_nta;
}

void nta_info_set_is_nta(nta_info_t *nta_info) {
  nta_info->is_nta = true;
}

/** Destructs the nta_info_t */
void nta_info_destruct(nta_info_t *nta_info) {
  delete_int_hmap(&nta_info->sin_map);
  delete_int_hmap(&nta_info->inverse_sin_map);
  delete_int_hmap(&nta_info->exp_map);
  delete_int_hmap(&nta_info->inverse_exp_map);
  delete_int_hmap(&nta_info->sin_period_map);
  delete_int_hmap(&nta_info->inverse_sin_period_map);
  delete_int_hmap(&nta_info->sin_taylor_degree_map);
  delete_int_hset(&nta_info->nta_arg_equations);
  delete_int_hmap(&nta_info->arg_map);
  delete_int_hmap(&nta_info->inverse_arg_map);
  delete_int_hset(&nta_info->nta_lemmas_variables);
  delete_int_hset(&nta_info->delta_used_constraints);
  delete_int_hset(&nta_info->original_atoms);
  delete_int_hmap(&nta_info->nta_watchlist);
  if (nta_info->nta_watchlist_lists != NULL) {
    uint32_t n = pv_size(nta_info->nta_watchlist_lists);
    for (uint32_t i = 0; i < n; i++) {
      ivector_t* list = (ivector_t*) nta_info->nta_watchlist_lists[i];
      if (list != NULL) {
        delete_ivector(list);
        safe_free(list);
      }
    }
    delete_ptr_vector(nta_info->nta_watchlist_lists);
    nta_info->nta_watchlist_lists = NULL;
  }
}

/** Set abstraction representing sin(t1)=t2 with period i */
void nta_info_set_sin_abstraction(nta_info_t *nta_info, term_t t1, term_t t2, term_t i) {
  int_hmap_pair_t* find = int_hmap_find(&nta_info->sin_map, t1);
  int_hmap_pair_t* find_inv = int_hmap_find(&nta_info->inverse_sin_map, t2);
  int_hmap_pair_t* find_p = NULL;
  int_hmap_pair_t* find_p_inv = NULL;
  bool use_period = nta_info->use_period_for_sin && i != NULL_TERM;
  if (use_period) {
    find_p = int_hmap_find(&nta_info->sin_period_map, t1);
    find_p_inv = int_hmap_find(&nta_info->inverse_sin_period_map, i);
  }

  if (find == NULL && find_inv == NULL && (!use_period || (find_p == NULL && find_p_inv == NULL))) {
    int_hmap_add(&nta_info->sin_map, t1, t2);
    int_hmap_add(&nta_info->inverse_sin_map, t2, t1);
    if (use_period) {
      int_hmap_add(&nta_info->sin_period_map, t1, i);
      int_hmap_add(&nta_info->inverse_sin_period_map, i, t1);
    }
  } else {
    /* Check consistency */
    if ((find != NULL && find->val != t2) || (find_inv != NULL && find_inv->val != t1) ||
        (use_period && ((find_p != NULL && find_p->val != i) || (find_p_inv != NULL && find_p_inv->val != t1)))) {
      /* This should not happen */
      fprintf(stderr, "Error: trying to set different original terms for the same abstracted NTA term.\n");
      yices_print_error(stderr);
      return;
    }
  }
}

/** Set abstraction representing exp(t1)=t2 */
void nta_info_set_exp_abstraction(nta_info_t *nta_info, term_t t1, term_t t2) {
  int_hmap_pair_t* find = int_hmap_find(&nta_info->exp_map, t1);
  int_hmap_pair_t* find_inv = int_hmap_find(&nta_info->inverse_exp_map, t2);
  if (find == NULL && find_inv == NULL) {
    int_hmap_add(&nta_info->exp_map, t1, t2);
    int_hmap_add(&nta_info->inverse_exp_map, t2, t1);
  } else {
    if ((find != NULL && find->val != t2) || (find_inv != NULL && find_inv->val != t1)) {
      fprintf(stderr, "Error: trying to set different original terms for the same abstracted exp term.\n");
      yices_print_error(stderr);
      return;
    }
  }
}

/** Set pi abstraction */
void nta_info_set_pi(nta_info_t *nta_info, term_t pi_term) {
  if (nta_info->pi == NULL_TERM) {
    nta_info->pi = pi_term;
  } else {
    if (nta_info->pi != pi_term) {
      fprintf(stderr, "Error: trying to set different pi term.\n");
      yices_print_error(stderr);
    }
  }
}

/** Get pi abstraction */
term_t nta_info_get_pi(const nta_info_t *nta_info) {
  return nta_info->pi;
}

/** Get sin period term (i) for a given term t */
term_t nta_info_get_sin_period_term(const nta_info_t *nta_info, term_t t) {
  if (nta_info == NULL || !nta_info->use_period_for_sin) {
    return NULL_TERM;
  }
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &nta_info->sin_period_map, t);
  if (find == NULL) return NULL_TERM; else return find->val;
}

/** Get inverse sin period term (t) for a given period term i */
term_t nta_info_get_sin_period_inverse_term(const nta_info_t *nta_info, term_t i) {
  if (nta_info == NULL || !nta_info->use_period_for_sin) {
    return NULL_TERM;
  }
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &nta_info->inverse_sin_period_map, i);
  if (find == NULL) return NULL_TERM; else return find->val;
}


/** Get inverse term from abstracted sin term (i.e. given y it returns x so that sin(x)=y) */
term_t nta_info_get_sin_inverse_term(const nta_info_t *nta_info, term_t t1) {
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &nta_info->inverse_sin_map, t1);
  if (find == NULL) {
    return NULL_TERM;
  } else {
    return find->val;
  }
}

/** Get sin term (i.e. given x it returns y so that sin(x)=y) */
term_t nta_info_get_sin_term(const nta_info_t *nta_info, term_t t2) {
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &nta_info->sin_map, t2);
  if (find == NULL) {
    return NULL_TERM;
  } else {
    return find->val;
  }
}

/** Get inverse term from abstracted exp term (i.e. given y it returns x so that exp(x)=y) */
term_t nta_info_get_exp_inverse_term(const nta_info_t *nta_info, term_t t1) {
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &nta_info->inverse_exp_map, t1);
  if (find == NULL) {
    return NULL_TERM;
  } else {
    return find->val;
  }
}

/** Get exp term (i.e. given x it returns y so that exp(x)=y) */
term_t nta_info_get_exp_term(const nta_info_t *nta_info, term_t t2) {
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &nta_info->exp_map, t2);
  if (find == NULL) {
    return NULL_TERM;
  } else {
    return find->val;
  }
}

static term_t nta_info_get_preprocessed_term(const nta_info_t *nta_info, term_t t) {
  if (nta_info == NULL || nta_info->preprocessor == NULL) {
    return NULL_TERM;
  }
  term_t pre = preprocessor_get(nta_info->preprocessor, t);
  if (pre == NULL_TERM || pre == t) {
    return NULL_TERM;
  }
  return pre;
}

static term_t nta_info_get_unpreprocessed_term(const nta_info_t *nta_info, term_t t_pre) {
  if (nta_info == NULL || nta_info->preprocessor == NULL) {
    return NULL_TERM;
  }
  term_t orig = preprocessor_get_inverse(nta_info->preprocessor, t_pre);
  if (orig == NULL_TERM || orig == t_pre) {
    return NULL_TERM;
  }
  return orig;
}

term_t nta_info_get_arg_term(const nta_info_t *nta_info, term_t arg_term) {
  if (nta_info == NULL) {
    return NULL_TERM;
  }
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &nta_info->arg_map, arg_term);
  if (find != NULL) {
    return find->val;
  }
  term_t pre = nta_info_get_preprocessed_term(nta_info, arg_term);
  if (pre != NULL_TERM) {
    find = int_hmap_find((int_hmap_t*) &nta_info->arg_map, pre);
    if (find != NULL) {
      return find->val;
    }
  }
  term_t orig = nta_info_get_unpreprocessed_term(nta_info, arg_term);
  if (orig != NULL_TERM) {
    find = int_hmap_find((int_hmap_t*) &nta_info->arg_map, orig);
    if (find != NULL) {
      return find->val;
    }
  }
  return NULL_TERM;
}

term_t nta_info_get_inverse_arg_term(const nta_info_t *nta_info, term_t fresh_term) {
  if (nta_info == NULL) {
    return NULL_TERM;
  }
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &nta_info->inverse_arg_map, fresh_term);
  if (find != NULL) {
    term_t orig = nta_info_get_unpreprocessed_term(nta_info, find->val);
    return orig != NULL_TERM ? orig : find->val;
  }
  term_t pre = nta_info_get_preprocessed_term(nta_info, fresh_term);
  if (pre != NULL_TERM) {
    find = int_hmap_find((int_hmap_t*) &nta_info->inverse_arg_map, pre);
    if (find != NULL) {
      term_t orig = nta_info_get_unpreprocessed_term(nta_info, find->val);
      return orig != NULL_TERM ? orig : find->val;
    }
  }
  term_t orig = nta_info_get_unpreprocessed_term(nta_info, fresh_term);
  if (orig != NULL_TERM) {
    find = int_hmap_find((int_hmap_t*) &nta_info->inverse_arg_map, orig);
    if (find != NULL) {
      term_t unpre = nta_info_get_unpreprocessed_term(nta_info, find->val);
      return unpre != NULL_TERM ? unpre : find->val;
    }
  }
  return NULL_TERM;
}

bool nta_info_is_arg_equation(const nta_info_t *nta_info, term_t t) {
  if (nta_info == NULL) {
    return false;
  }
  term_t atom = unsigned_term(t);
  if (int_hset_member((int_hset_t*) &nta_info->nta_arg_equations, atom)) {
    return true;
  }
  term_t pre = nta_info_get_preprocessed_term(nta_info, atom);
  if (pre != NULL_TERM) {
    return int_hset_member((int_hset_t*) &nta_info->nta_arg_equations, pre);
  }
  term_t orig = nta_info_get_unpreprocessed_term(nta_info, atom);
  if (orig != NULL_TERM) {
    return int_hset_member((int_hset_t*) &nta_info->nta_arg_equations, orig);
  }
  return false;
}

// TODO_NTA: Key packing is only safe if term ids are non-negative and small enough
// that ((t * 4 + center) * 2 + polarity) fits in int32_t. Consider a more robust
// structure (e.g., per-term table) if term ids can grow large.
static int32_t nta_taylor_degree_key(term_t t, taylor_center_kind_t center, nta_taylor_polarity_kind_t polarity) {
  int64_t key = ((int64_t) t * 4 + (int64_t) center) * 2 + (int64_t) polarity;
  if (key < 0 || key > INT32_MAX) {
    return -1;
  }
  return (int32_t) key;
}

static int nta_taylor_polarity_from_center_degree(taylor_center_kind_t center, int degree) {
  assert(degree >= 0);

  int mod = degree % 4;  // degree modulo 4 to match the 4k residue classes
  switch (center) {
  case TAYLOR_CENTER_ZERO:
    if (mod == 1) {
      return NTA_TAYLOR_POLARITY_UPPER;
    }
    if (mod == 3) {
      return NTA_TAYLOR_POLARITY_LOWER;
    }
    assert(false);
    return -1;
  case TAYLOR_CENTER_PI_2:
    if (mod == 0) {
      return NTA_TAYLOR_POLARITY_UPPER;
    }
    if (mod == 2) {
      return NTA_TAYLOR_POLARITY_LOWER;
    }
    assert(false);
    return -1;
  case TAYLOR_CENTER_PI:  // upper polarity means upper bound on the left side and lower on the right side 
    if (mod == 1) {
      return NTA_TAYLOR_POLARITY_UPPER;
    }
    if (mod == 3) {
      return NTA_TAYLOR_POLARITY_LOWER;
    }
    assert(false);
    return -1;
  case TAYLOR_CENTER_PI_3_2:
    if (mod == 2) {
      return NTA_TAYLOR_POLARITY_UPPER;
    }
    if (mod == 0) {
      return NTA_TAYLOR_POLARITY_LOWER;
    }
    assert(false);
    return -1;
  case TAYLOR_CENTER_2_PI:
    if (mod == 3) {
      return NTA_TAYLOR_POLARITY_UPPER;
    }
    if (mod == 1) {
      return NTA_TAYLOR_POLARITY_LOWER;
    }
    assert(false);
    return -1;
  default:
    assert(false);
    return -1;
  }
}

int nta_taylor_initial_degree(taylor_center_kind_t center, nta_taylor_polarity_kind_t polarity) {
  switch (center) {
  case TAYLOR_CENTER_ZERO:
    return (polarity == NTA_TAYLOR_POLARITY_UPPER) ? 1 : 3;
  case TAYLOR_CENTER_PI_2:
    return (polarity == NTA_TAYLOR_POLARITY_UPPER) ? 4 : 2;
  case TAYLOR_CENTER_PI:
    return (polarity == NTA_TAYLOR_POLARITY_UPPER) ? 1 : 3;
  case TAYLOR_CENTER_PI_3_2:
    return (polarity == NTA_TAYLOR_POLARITY_UPPER) ? 2 : 4;
  case TAYLOR_CENTER_2_PI:
    return (polarity == NTA_TAYLOR_POLARITY_UPPER) ? 3 : 1;
  default:
    return -1;
  }
}

int nta_info_get_last_taylor_degree(const nta_info_t *nta_info, term_t t, taylor_center_kind_t center, nta_taylor_polarity_kind_t polarity) {
  if (nta_info == NULL) {
    return -1;
  }
  int32_t key = nta_taylor_degree_key(t, center, polarity);
  if (key < 0) {
    return -1;
  }
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &nta_info->sin_taylor_degree_map, key);
  if (find == NULL) {
    return -1;
  }
  return find->val;
}

void nta_info_set_last_taylor_degree(nta_info_t *nta_info, term_t t, taylor_center_kind_t center, int degree) {
  assert(degree >= 0);
  assert(nta_info != NULL);
  
  int polarity_val = nta_taylor_polarity_from_center_degree(center, degree);
  assert(polarity_val == NTA_TAYLOR_POLARITY_UPPER || polarity_val == NTA_TAYLOR_POLARITY_LOWER);
  
  nta_taylor_polarity_kind_t polarity = (nta_taylor_polarity_kind_t) polarity_val;
  int32_t key = nta_taylor_degree_key(t, center, polarity);
  assert(key >= 0);
  
  int_hmap_pair_t* find = int_hmap_find(&nta_info->sin_taylor_degree_map, key);
  if (find == NULL) {
    int_hmap_add(&nta_info->sin_taylor_degree_map, key, degree);
  } else {
    find->val = degree;
  }
}

int next_taylor_degree_for_sin(const nta_info_t *nta_info, term_t t, taylor_center_kind_t center, nta_taylor_polarity_kind_t polarity) {
  int last = nta_info_get_last_taylor_degree(nta_info, t, center, polarity);
  if (last < 0) {
    return nta_taylor_initial_degree(center, polarity);
  }
  assert(last < INT_MAX);
  return last + 4;
}

/** Record a lemma variable added by the NTA plugin */
void nta_info_add_nta_lemma_variable(nta_info_t *nta_info, variable_t var) {
  if (nta_info == NULL || var == variable_null) {
    return;
  }
  int_hset_add(&nta_info->nta_lemmas_variables, (uint32_t) var);
}

/** Check whether the variable corresponds to an NTA lemma */
bool nta_info_has_nta_lemma_variable(const nta_info_t *nta_info, variable_t var) {
  if (nta_info == NULL || var == variable_null) {
    return false;
  }
  return int_hset_member((int_hset_t*) &nta_info->nta_lemmas_variables, (uint32_t) var);
}

/** Reset the recorded lemma variables */
void nta_info_reset_nta_lemma_variables(nta_info_t *nta_info) {
  if (nta_info == NULL) {
    return;
  }
  int_hset_reset(&nta_info->nta_lemmas_variables);
}

static ivector_t* nta_info_get_or_create_watchlist(nta_info_t *nta_info, term_t term) {
  assert (nta_info != NULL && term != NULL_TERM);
  int_hmap_pair_t* find = int_hmap_find(&nta_info->nta_watchlist, term);
  if (find == NULL) {
    ivector_t* list = (ivector_t*) safe_malloc(sizeof(ivector_t));
    init_ivector(list, 0);
    add_ptr_to_vector(&nta_info->nta_watchlist_lists, list);
    int32_t index = (int32_t) (pv_size(nta_info->nta_watchlist_lists) - 1);
    int_hmap_add(&nta_info->nta_watchlist, term, index);
    return list;
  }
  int32_t index = find->val;
  if (index < 0 || nta_info->nta_watchlist_lists == NULL || (uint32_t) index >= pv_size(nta_info->nta_watchlist_lists)) {
    return NULL;
  }
  return (ivector_t*) nta_info->nta_watchlist_lists[index];
}

void nta_info_watchlist_add(nta_info_t *nta_info, term_t term, variable_t cstr_var) {
  assert (nta_info != NULL && term != NULL_TERM && cstr_var != variable_null);
  ivector_t* list = nta_info_get_or_create_watchlist(nta_info, term);
  if (list == NULL) {
    return;
  }
  for (uint32_t i = 0; i < list->size; i++) {
    if (list->data[i] == cstr_var) {
      return;
    }
  }
  ivector_push(list, cstr_var);
}

const ivector_t* nta_info_watchlist_get(const nta_info_t *nta_info, term_t term) {
  if (nta_info == NULL || term == NULL_TERM) {
    return NULL;
  }
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &nta_info->nta_watchlist, term);
  if (find == NULL) {
    return NULL;
  }
  int32_t index = find->val;
  if (index < 0 || nta_info->nta_watchlist_lists == NULL || (uint32_t) index >= pv_size(nta_info->nta_watchlist_lists)) {
    return NULL;
  }
  return (const ivector_t*) nta_info->nta_watchlist_lists[index];
}

void nta_info_watchlist_clear(nta_info_t *nta_info, term_t term) {
  if (nta_info == NULL || term == NULL_TERM) {
    return;
  }
  int_hmap_pair_t* find = int_hmap_find(&nta_info->nta_watchlist, term);
  if (find == NULL) {
    return;
  }
  int32_t index = find->val;
  if (index < 0 || nta_info->nta_watchlist_lists == NULL || (uint32_t) index >= pv_size(nta_info->nta_watchlist_lists)) {
    return;
  }
  ivector_t* list = (ivector_t*) nta_info->nta_watchlist_lists[index];
  if (list != NULL) {
    ivector_reset(list);
  }
}



