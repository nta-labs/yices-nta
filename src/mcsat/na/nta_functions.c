#include <math.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "utils/dprng.h"
#include "mcsat/value.h"
#include "mcsat/na/nta_functions.h"
#include "mcsat/na/na_plugin_internal.h"
#include "mcsat/variable_db.h"
#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "terms/rationals.h"
#include "terms/terms.h"
#include "terms/pprod_table.h"
#include "terms/term_manager.h"
#include "terms/rba_buffer_terms.h"
#include "io/term_printer.h"
#include "terms/balanced_arith_buffers.h"
#include "api/yices_api_lock_free.h"
#include <poly/value.h>
#include "mcsat/utils/lp_utils.h"
#include "model/models.h"
#include "model/model_eval.h"
#include <poly/polynomial.h>
#include <poly/variable_order.h>
#include <poly/variable_list.h>
#include <poly/variable_db.h>
#include <poly/assignment.h>

/* Use ARB for rigorous interval arithmetic */
#include <flint/arb.h>
#include <flint/arf.h>
#include <flint/fmpz.h>
#include <mpfr.h>

/* Define M_PI if not already defined */
#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

typedef enum {
  NO_NOTABLE_VALUE = 0,
  IS_ZERO,
  IS_PI_2,
  IS_PI,
  IS_PI_3_2
} nta_notable_value_kind_t;


double lp_value_to_double_safe_from_above(const lp_value_t* v) {
  switch (v->type) {
  case LP_VALUE_NONE:
    return 0;
  case LP_VALUE_PLUS_INFINITY:
    return INFINITY;
  case LP_VALUE_MINUS_INFINITY:
    return -INFINITY;
  default:
    break;
  }

  double ret = lp_value_to_double(v);
  if (isnan(ret)) {
    return ret;
  }

  lp_rational_t q_ret;
  lp_rational_construct_from_double(&q_ret, ret);
  int cmp = lp_value_cmp_rational(v, &q_ret);
  /* cmp < 0 => v < q_ret  (ret > value) */
  while (cmp >= 0) {
    double old = ret;
    ret = nextafter(old, INFINITY);
    if (ret == old || isinf(ret)) {
      /* can't move further */
      break;
    }
    lp_rational_destruct(&q_ret);
    lp_rational_construct_from_double(&q_ret, ret);
    cmp = lp_value_cmp_rational(v, &q_ret);
  }
  lp_rational_destruct(&q_ret);
  return ret;
}

double lp_value_to_double_safe_from_below(const lp_value_t* v) {
  switch (v->type) {
  case LP_VALUE_NONE:
    return 0;
  case LP_VALUE_PLUS_INFINITY:
    return INFINITY;
  case LP_VALUE_MINUS_INFINITY:
    return -INFINITY;
  default:
    break;
  }

  double ret = lp_value_to_double(v);
  if (isnan(ret)) {
    return ret;
  }

  lp_rational_t q_ret;
  lp_rational_construct_from_double(&q_ret, ret);
  int cmp = lp_value_cmp_rational(v, &q_ret);
  /* cmp > 0 => v > q_ret  (ret < value) */
  while (cmp <= 0) {
    double old = ret;
    ret = nextafter(old, -INFINITY);
    if (ret == old || isinf(ret)) {
      /* can't move further */
      break;
    }
    lp_rational_destruct(&q_ret);
    lp_rational_construct_from_double(&q_ret, ret);
    cmp = lp_value_cmp_rational(v, &q_ret);
  }
  lp_rational_destruct(&q_ret);
  return ret;
}

/**
 * Forward declaration for mcsat_value_to_arb.
 */
static bool mcsat_value_to_arb(const mcsat_value_t *value, arb_t result, slong prec);

/* Forward declaration for trail-based evaluation helper */
static void nta_build_eval_from_trail(const na_plugin_t* na, term_manager_t* tm,
                                      variable_db_t* var_db, model_t* model,
                                      evaluator_t* eval, value_table_t** vtbl_out);

/* Forward declarations for local helpers used before definition */
static int nta_compare_sin(const mcsat_value_t *val_x, const mcsat_value_t *val_sin_x);
static int nta_compare_exp(const mcsat_value_t *val_x, const mcsat_value_t *val_exp_x);
static term_t nta_term_from_mpfr(term_manager_t* tm, const mpfr_t v);
static void nta_build_pade_exp_terms(term_t x, term_t c_term, int n, term_t* n_term, term_t* d_term);
static double nta_exp_distance(const mcsat_value_t *val_x, const mcsat_value_t *val_exp_x);
static taylor_center_kind_t find_closest_taylor_center(const mcsat_value_t *val_x);
static int compute_pi_precision_up_to_digit(const mcsat_value_t *val_pi);
static bool refine_pi_bounds(na_plugin_t* na, term_manager_t* tm, nta_info_t* nta_info,
                             variable_db_t* var_db, const mcsat_value_t* val_pi,
                             ivector_t* refinements);

static bool nta_get_period_var_for_variable(const nta_info_t* nta_info, variable_db_t* var_db,
                                            variable_t var, variable_t* period_var_out);
static nta_notable_value_kind_t nta_var_has_notable_value_pi(na_plugin_t* na, variable_t var,
                                                             const nta_info_t* nta_info,
                                                             variable_db_t* var_db);
static bool nta_build_notable_value_arb(const mcsat_value_t* period_value,
                                        nta_notable_value_kind_t kind, arb_t out, slong prec);

/**
 * Helper function to construct lp_rational from yices rational_t.
 */
static void lp_rational_construct_from_yices_rational(lp_rational_t* q_lp, const rational_t* q) {
  if (is_ratgmp(q)) {
    mpq_t gmp_q;
    mpq_init(gmp_q);
    q_get_mpq(q, gmp_q);
    lp_rational_construct_copy(q_lp, gmp_q);
    mpq_clear(gmp_q);
  } else {
    lp_rational_construct_from_int(q_lp, get_num(q), get_den(q));
  }
}

/**
 * Initialize an nta_value with an mcsat_value_t.
 */
static void nta_value_init_mcsat(nta_value* nv, const mcsat_value_t* val) {
  nv->type = NTA_VALUE_MCSAT;
  mcsat_value_construct_copy(&nv->mcsat_val, val);
}

/**
 * Clear an nta_value, freeing any resources.
 */
static void nta_value_clear(nta_value* nv) {
  if (nv->type == NTA_VALUE_MCSAT) {
    mcsat_value_destruct(&nv->mcsat_val);
  } else {
    arb_clear(nv->arb_val);
  }
}

/**
 * Convert an nta_value to arb_t.
 * If already arb_t, copies it. If mcsat_value_t, converts it.
 */
static bool nta_value_to_arb(const nta_value* nv, arb_t result, slong prec) {
  if (nv->type == NTA_VALUE_ARB) {
    arb_set(result, nv->arb_val);
    return true;
  } else {
    return mcsat_value_to_arb(&nv->mcsat_val, result, prec);
  }
}

/* Forward declaration */
static int mcsat_value_cmp(const mcsat_value_t* v1, const mcsat_value_t* v2);

/**
 * Compute a safe union of two ranges.
 * If both ranges are identical exact values, keep the exact value.
 * Otherwise, return an ARB interval hull covering both ranges.
 */
static bool nta_union_ranges(const nta_value* a, const nta_value* b, nta_value* result, slong prec) {
  assert(a != NULL && b != NULL && result != NULL);

  if (a->type == NTA_VALUE_MCSAT && b->type == NTA_VALUE_MCSAT) {
    if (mcsat_value_cmp(&a->mcsat_val, &b->mcsat_val) == 0) {
      nta_value_init_mcsat(result, &a->mcsat_val);
      return true;
    }
  }

  arb_t a_arb, b_arb;
  arb_init(a_arb);
  arb_init(b_arb);
  if (!nta_value_to_arb(a, a_arb, prec) || !nta_value_to_arb(b, b_arb, prec)) {
    arb_clear(a_arb);
    arb_clear(b_arb);
    return false;
  }

  mpfr_t a_low, a_high, b_low, b_high, low, high;
  mpfr_init2(a_low, (mpfr_prec_t) prec);
  mpfr_init2(a_high, (mpfr_prec_t) prec);
  mpfr_init2(b_low, (mpfr_prec_t) prec);
  mpfr_init2(b_high, (mpfr_prec_t) prec);
  mpfr_init2(low, (mpfr_prec_t) prec);
  mpfr_init2(high, (mpfr_prec_t) prec);

  arb_get_interval_mpfr(a_low, a_high, a_arb);
  arb_get_interval_mpfr(b_low, b_high, b_arb);

  if (mpfr_cmp(a_low, b_low) <= 0) {
    mpfr_set(low, a_low, MPFR_RNDD);
  } else {
    mpfr_set(low, b_low, MPFR_RNDD);
  }

  if (mpfr_cmp(a_high, b_high) >= 0) {
    mpfr_set(high, a_high, MPFR_RNDU);
  } else {
    mpfr_set(high, b_high, MPFR_RNDU);
  }

  result->type = NTA_VALUE_ARB;
  arb_init(result->arb_val);
  arb_set_interval_mpfr(result->arb_val, low, high, prec);

  mpfr_clear(a_low);
  mpfr_clear(a_high);
  mpfr_clear(b_low);
  mpfr_clear(b_high);
  mpfr_clear(low);
  mpfr_clear(high);
  arb_clear(a_arb);
  arb_clear(b_arb);
  return true;
}

void nta_value_print(na_plugin_t* na, const nta_value* nv, FILE* out, slong prec) {
  if (nv == NULL || out == NULL) {
    return;
  }

  if (nv->type == NTA_VALUE_MCSAT) {
    mcsat_value_print(&nv->mcsat_val, out);
    return;
  }
  else{
    // mpfr_t mpfr_val;
    // mpfr_init2(mpfr_val, (mpfr_prec_t) prec);

    // arf_get_mpfr(mpfr_val, arb_midref(nv->arb_val), MPFR_RNDN);
    // ctx_trace_printf(na->ctx, "(arb, approximated center with precision %ld): ", prec);
    // mpfr_out_str(out, 10, (size_t) prec, mpfr_val, MPFR_RNDN);

    fprintf(out, "(arb with precision %ld) ", prec);
    arb_fprintd(out, nv->arb_val, prec);
    
    // mpfr_clear(mpfr_val);
  }
}

/**
 * Record a variable for which the safe check is incomplete.
 */
static void nta_record_incomplete_var(ivector_t* incomplete_vars, variable_t var) {
  assert (incomplete_vars != NULL && var != variable_null);
  for (uint32_t i = 0; i < incomplete_vars->size; i++) {
    if (incomplete_vars->data[i] == var) {
      return;
    }
  }
  ivector_push(incomplete_vars, var);
}

/**
 * Convert an mcsat_value_t to a double.
 */
static double mcsat_value_to_double(const mcsat_value_t *value) {
  assert(value->type == VALUE_RATIONAL || value->type == VALUE_LIBPOLY);
  if (value->type == VALUE_RATIONAL) {
    // Convert rational to double
    return q_get_double((rational_t*) &value->q);
  } else  {
    assert(value->type == VALUE_LIBPOLY);
    //lp_algebraic_number_to_double
    lp_value_t* lp_val = (lp_value_t*) &value->lp_value;
    double d = lp_value_to_double(lp_val);
    return d;
  }
}

/**
 * Compare two mcsat values (rational or libpoly).
 * Returns <0 if v1 < v2, 0 if equal, >0 if v1 > v2.
 */
static int mcsat_value_cmp(const mcsat_value_t* v1, const mcsat_value_t* v2) {
  assert(v1->type == VALUE_RATIONAL || v1->type == VALUE_LIBPOLY);
  assert(v2->type == VALUE_RATIONAL || v2->type == VALUE_LIBPOLY);

  if (v1->type == VALUE_RATIONAL && v2->type == VALUE_RATIONAL) {
    return q_cmp(&v1->q, &v2->q);
  } else if (v1->type == VALUE_LIBPOLY && v2->type == VALUE_LIBPOLY) {
    return lp_value_cmp(&v1->lp_value, &v2->lp_value);
  } else if (v1->type == VALUE_RATIONAL && v2->type == VALUE_LIBPOLY) {
    mpq_t v1_mpq;
    mpq_init(v1_mpq);
    q_get_mpq((rational_t*)&v1->q, v1_mpq);
    lp_value_t v1_lp;
    lp_value_construct_none(&v1_lp);
    lp_value_assign_raw(&v1_lp, LP_VALUE_RATIONAL, &v1_mpq);
    int cmp = lp_value_cmp(&v1_lp, &v2->lp_value);
    lp_value_destruct(&v1_lp);
    mpq_clear(v1_mpq);
    return cmp;
  } else {
    /* v1 is libpoly, v2 is rational */
    mpq_t v2_mpq;
    mpq_init(v2_mpq);
    q_get_mpq((rational_t*)&v2->q, v2_mpq);
    lp_value_t v2_lp;
    lp_value_construct_none(&v2_lp);
    lp_value_assign_raw(&v2_lp, LP_VALUE_RATIONAL, &v2_mpq);
    int cmp = lp_value_cmp(&v1->lp_value, &v2_lp);
    lp_value_destruct(&v2_lp);
    mpq_clear(v2_mpq);
    return cmp;
  }
}

static void nta_lp_value_init_from_mcsat(const mcsat_value_t* val, lp_value_t* out) {
  if (val->type == VALUE_RATIONAL) {
    lp_rational_t lp_q;
    lp_rational_construct(&lp_q);
    lp_rational_construct_from_yices_rational(&lp_q, &val->q);
    lp_value_construct(out, LP_VALUE_RATIONAL, &lp_q);
    lp_rational_destruct(&lp_q);
  } else {
    lp_value_construct_copy(out, &val->lp_value);
  }
}

static void nta_lp_value_init_from_int(lp_value_t* out, int64_t num, int64_t den) {
  lp_rational_t lp_q;
  lp_rational_construct(&lp_q);
  lp_rational_construct_from_int(&lp_q, num, den);
  lp_value_construct(out, LP_VALUE_RATIONAL, &lp_q);
  lp_rational_destruct(&lp_q);
}

static bool nta_compute_period_index_from_values(const mcsat_value_t* val_x,
                                                 const mcsat_value_t* val_pi,
                                                 int64_t* k_out) {
  if (val_x == NULL || val_pi == NULL || k_out == NULL) {
    return false;
  }

  double x = mcsat_value_to_double(val_x);
  double pi = mcsat_value_to_double(val_pi);
  if (isnan(x) || isnan(pi) || pi <= 0.0) {
    return false;
  }

  double two_pi = 2.0 * pi;
  if (two_pi <= 0.0) {
    return false;
  }

  *k_out = (int64_t) floor(x / two_pi);
  return true;
}

static bool nta_get_period_var_for_variable(const nta_info_t* nta_info, variable_db_t* var_db,
                                            variable_t var, variable_t* period_var_out) {
  if (var == variable_null || period_var_out == NULL) {
    return false;
  }
  if (nta_info == NULL || !nta_info->use_period_for_sin) {
    return false;
  }

  term_t var_term = variable_db_get_term(var_db, var);
  term_t arg_term = var_term;
  term_t inverse_term = nta_info_get_sin_inverse_term(nta_info, var_term);
  if (inverse_term != NULL_TERM) {
    arg_term = inverse_term;
  }

  term_t period_term = nta_info_get_sin_period_term(nta_info, arg_term);
  if (period_term == NULL_TERM) {
    return false;
  }

  variable_t period_var = variable_db_get_variable_if_exists(var_db, period_term);
  if (period_var == variable_null) {
    return false;
  }

  *period_var_out = period_var;
  return true;
}

static nta_notable_value_kind_t nta_var_has_notable_value_pi(na_plugin_t* na, variable_t var,
                                                             const nta_info_t* nta_info,
                                                             variable_db_t* var_db) {
  if (var == variable_null) {
    return NO_NOTABLE_VALUE;
  }
  if (nta_info == NULL || !nta_info->use_period_for_sin) {
    return NO_NOTABLE_VALUE;
  }

  const mcsat_trail_t* trail = na->ctx->trail;
  if (!trail_has_value(trail, var)) {
    return NO_NOTABLE_VALUE;
  }

  variable_t period_var = variable_null;
  if (!nta_get_period_var_for_variable(nta_info, var_db, var, &period_var)) {
    return NO_NOTABLE_VALUE;
  }

  term_t pi_term = nta_info_get_pi(nta_info);
  if (pi_term == NULL_TERM) {
    return NO_NOTABLE_VALUE;
  }

  variable_t pi_var = variable_db_get_variable_if_exists(var_db, pi_term);
  if (pi_var == variable_null || !trail_has_value(trail, pi_var)) {
    return NO_NOTABLE_VALUE;
  }

  if (!trail_has_value(trail, period_var)) {
    return NO_NOTABLE_VALUE;
  }

  const mcsat_value_t* value = trail_get_value(trail, var);
  const mcsat_value_t* period_value = trail_get_value(trail, period_var);
  const mcsat_value_t* pi_value = trail_get_value(trail, pi_var);
  if (value->type == VALUE_NONE || period_value->type == VALUE_NONE || pi_value->type == VALUE_NONE) {
    return NO_NOTABLE_VALUE;
  }

  lp_value_t lp_value, lp_period, lp_pi, lp_two, lp_half;
  lp_value_t lp_tmp, lp_base, lp_target, lp_pi_half;
  lp_value_construct_zero(&lp_value);
  lp_value_construct_zero(&lp_period);
  lp_value_construct_zero(&lp_pi);
  lp_value_construct_zero(&lp_two);
  lp_value_construct_zero(&lp_half);
  lp_value_construct_zero(&lp_tmp);
  lp_value_construct_zero(&lp_base);
  lp_value_construct_zero(&lp_target);
  lp_value_construct_zero(&lp_pi_half);

  nta_lp_value_init_from_mcsat(value, &lp_value);
  nta_lp_value_init_from_mcsat(period_value, &lp_period);
  nta_lp_value_init_from_mcsat(pi_value, &lp_pi);
  nta_lp_value_init_from_int(&lp_two, 2, 1);
  nta_lp_value_init_from_int(&lp_half, 1, 2);

  lp_value_mul(&lp_tmp, &lp_period, &lp_pi);
  lp_value_mul(&lp_base, &lp_two, &lp_tmp);

  if (lp_value_cmp(&lp_value, &lp_base) == 0) {
    lp_value_destruct(&lp_value);
    lp_value_destruct(&lp_period);
    lp_value_destruct(&lp_pi);
    lp_value_destruct(&lp_two);
    lp_value_destruct(&lp_half);
    lp_value_destruct(&lp_tmp);
    lp_value_destruct(&lp_base);
    lp_value_destruct(&lp_target);
    lp_value_destruct(&lp_pi_half);
    return IS_ZERO;
  }

  lp_value_mul(&lp_pi_half, &lp_pi, &lp_half);
  lp_value_add(&lp_target, &lp_base, &lp_pi_half);
  if (lp_value_cmp(&lp_value, &lp_target) == 0) {
    lp_value_destruct(&lp_value);
    lp_value_destruct(&lp_period);
    lp_value_destruct(&lp_pi);
    lp_value_destruct(&lp_two);
    lp_value_destruct(&lp_half);
    lp_value_destruct(&lp_tmp);
    lp_value_destruct(&lp_base);
    lp_value_destruct(&lp_target);
    lp_value_destruct(&lp_pi_half);
    return IS_PI_2;
  }

  lp_value_add(&lp_target, &lp_base, &lp_pi);
  if (lp_value_cmp(&lp_value, &lp_target) == 0) {
    lp_value_destruct(&lp_value);
    lp_value_destruct(&lp_period);
    lp_value_destruct(&lp_pi);
    lp_value_destruct(&lp_two);
    lp_value_destruct(&lp_half);
    lp_value_destruct(&lp_tmp);
    lp_value_destruct(&lp_base);
    lp_value_destruct(&lp_target);
    lp_value_destruct(&lp_pi_half);
    return IS_PI;
  }

  lp_value_add(&lp_target, &lp_base, &lp_pi);
  lp_value_add(&lp_target, &lp_target, &lp_pi_half);
  if (lp_value_cmp(&lp_value, &lp_target) == 0) {
    lp_value_destruct(&lp_value);
    lp_value_destruct(&lp_period);
    lp_value_destruct(&lp_pi);
    lp_value_destruct(&lp_two);
    lp_value_destruct(&lp_half);
    lp_value_destruct(&lp_tmp);
    lp_value_destruct(&lp_base);
    lp_value_destruct(&lp_target);
    lp_value_destruct(&lp_pi_half);
    return IS_PI_3_2;
  }

  lp_value_destruct(&lp_value);
  lp_value_destruct(&lp_period);
  lp_value_destruct(&lp_pi);
  lp_value_destruct(&lp_two);
  lp_value_destruct(&lp_half);
  lp_value_destruct(&lp_tmp);
  lp_value_destruct(&lp_base);
  lp_value_destruct(&lp_target);
  lp_value_destruct(&lp_pi_half);
  return NO_NOTABLE_VALUE;
}

static bool nta_build_notable_value_arb(const mcsat_value_t* period_value,
                                        nta_notable_value_kind_t kind, arb_t out, slong prec) {
  if (period_value == NULL || out == NULL) {
    return false;
  }

  arb_t period_arb, pi_arb, base_arb, offset_arb, tmp_arb;
  arb_init(period_arb);
  arb_init(pi_arb);
  arb_init(base_arb);
  arb_init(offset_arb);
  arb_init(tmp_arb);

  if (!mcsat_value_to_arb(period_value, period_arb, prec)) {
    arb_clear(period_arb);
    arb_clear(pi_arb);
    arb_clear(base_arb);
    arb_clear(offset_arb);
    arb_clear(tmp_arb);
    return false;
  }

  arb_const_pi(pi_arb, prec);
  arb_mul(base_arb, period_arb, pi_arb, prec);
  arb_mul_ui(base_arb, base_arb, 2, prec);

  switch (kind) {
  case IS_ZERO:
    arb_set(out, base_arb);
    break;
  case IS_PI_2:
    arb_mul_2exp_si(offset_arb, pi_arb, -1);
    arb_add(out, base_arb, offset_arb, prec);
    break;
  case IS_PI:
    arb_add(out, base_arb, pi_arb, prec);
    break;
  case IS_PI_3_2:
    arb_mul_2exp_si(offset_arb, pi_arb, -1);
    arb_add(tmp_arb, base_arb, pi_arb, prec);
    arb_add(out, tmp_arb, offset_arb, prec);
    break;
  case NO_NOTABLE_VALUE:
  default:
    arb_set(out, base_arb);
    break;
  }

  arb_clear(period_arb);
  arb_clear(pi_arb);
  arb_clear(base_arb);
  arb_clear(offset_arb);
  arb_clear(tmp_arb);
  return true;
}

/**
 * Compare an mcsat_value_t against zero.
 * Returns <0 if v < 0, 0 if v == 0, >0 if v > 0.
 */
static int mcsat_value_cmp_zero(const mcsat_value_t* v) {
  assert(v->type == VALUE_RATIONAL || v->type == VALUE_LIBPOLY);
  if (v->type == VALUE_RATIONAL) {
    return q_sgn(&v->q);
  }

  lp_rational_t zero;
  lp_rational_construct(&zero);
  int cmp = lp_value_cmp_rational(&v->lp_value, &zero);
  lp_rational_destruct(&zero);
  return cmp;
}

/**
 * Compute the position of the first non-zero digit after the decimal point
 * in the error |val_pi - pi|, using interval arithmetic.
 *
 * Returns 0 if the error is >= 1 or cannot be determined,
 * or a large value if error is exactly 0.
 */
static int compute_pi_precision_up_to_digit(const mcsat_value_t *val_pi) {
  if (val_pi == NULL) {
    return 0;
  }

  const slong max_precision = 1024;
  slong precision = 64;
  double err_hi = 0.0;

  while (precision <= max_precision) {
    arb_t pi_arb, val_pi_arb, diff_arb;
    arb_init(pi_arb);
    arb_init(val_pi_arb);
    arb_init(diff_arb);

    arb_const_pi(pi_arb, precision);
    if (!mcsat_value_to_arb(val_pi, val_pi_arb, precision)) {
      arb_clear(pi_arb);
      arb_clear(val_pi_arb);
      arb_clear(diff_arb);
      assert(false);
      return 0;
    }

    arb_sub(diff_arb, val_pi_arb, pi_arb, precision);
    arb_abs(diff_arb, diff_arb);

    mpfr_t diff_low, diff_high;
    mpfr_init2(diff_low, (mpfr_prec_t) precision);
    mpfr_init2(diff_high, (mpfr_prec_t) precision);
    arb_get_interval_mpfr(diff_low, diff_high, diff_arb);

    err_hi = mpfr_get_d(diff_high, MPFR_RNDU);

    mpfr_clear(diff_low);
    mpfr_clear(diff_high);
    arb_clear(pi_arb);
    arb_clear(val_pi_arb);
    arb_clear(diff_arb);

    if (err_hi != 0.0) {
      break;
    }

    precision += 20;
  }

  if (err_hi == 0.0) {
    return (int) precision;
  }

  // this cannot happen as we already have initial bounds on pi
  // if (err_hi >= 1.0) {
  //   return 0;
  // }

  double log10_err = -log10(err_hi);
  int digit = (int) floor(log10_err);
  if (digit < 0) {
    digit = 0;
  }
  return digit;
}

/**
 * Refine bounds on pi using interval arithmetic so that the current value
 * assigned to pi is outside the bounds. Adds bounds as refinements.
 */
static bool refine_pi_bounds(na_plugin_t* na, term_manager_t* tm, nta_info_t* nta_info,
                             variable_db_t* var_db, const mcsat_value_t* val_pi,
                             ivector_t* refinements) {
  if (na == NULL || tm == NULL || nta_info == NULL || var_db == NULL || val_pi == NULL || refinements == NULL) {
    return false;
  }

  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    FILE* out = ctx_trace_out(na->ctx);
    ctx_trace_printf(na->ctx, "refine_pi_bounds: start val_pi=");
    mcsat_value_print(val_pi, out);
    ctx_trace_printf(na->ctx, "\n");
  }

  term_t pi_term = nta_info_get_pi(nta_info);
  assert (pi_term != NULL_TERM);

  const slong max_precision = 1024;
  slong precision = 32;

  while (precision <= max_precision) {
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx, "refine_pi_bounds: precision=%ld\n", precision);
    }
    arb_t pi_arb, val_pi_arb;
    arb_init(pi_arb);
    arb_init(val_pi_arb);

    arb_const_pi(pi_arb, precision);



    if (!mcsat_value_to_arb(val_pi, val_pi_arb, precision)) {
      arb_clear(pi_arb);
      arb_clear(val_pi_arb);
      return false;
    }

    mpfr_t pi_low, pi_high, val_low, val_high;
    mpfr_init2(pi_low, (mpfr_prec_t) precision);
    mpfr_init2(pi_high, (mpfr_prec_t) precision);
    mpfr_init2(val_low, (mpfr_prec_t) precision);
    mpfr_init2(val_high, (mpfr_prec_t) precision);

    arb_get_interval_mpfr(pi_low, pi_high, pi_arb);
    arb_get_interval_mpfr(val_low, val_high, val_pi_arb);

    //print pi_arb for debugging
    // if (ctx_trace_enabled(na->ctx, "na::nta")) {
    //   ctx_trace_printf(na->ctx, "refine_pi_bounds: pi_low printed with precision =%ld\n", precision);
    //   mpfr_out_str(ctx_trace_out(na->ctx), 10, 32, pi_low, MPFR_RNDU);
    //   ctx_trace_printf(na->ctx, "\n");
    // }

    // mpfr_t pi_low2, pi_high2;
    // mpfr_init2(pi_low2, (mpfr_prec_t) precision*5);
    // mpfr_init2(pi_high2, (mpfr_prec_t) precision*5);
    // arb_get_interval_mpfr(pi_low2, pi_high2, pi_arb);
    // if (ctx_trace_enabled(na->ctx, "na::nta")) {
    //   ctx_trace_printf(na->ctx, "refine_pi_bounds: pi_low printed with precision =%ld\n", precision*5);
    //   mpfr_out_str(ctx_trace_out(na->ctx), 10, 32*5, pi_low2, MPFR_RNDU);
    //   ctx_trace_printf(na->ctx, "\n");
    // }

    // /* Ensure outward rounding for all bounds (guaranteed enclosure) */
    // mpfr_nextbelow(pi_low);
    // mpfr_nextabove(pi_high);
    // mpfr_nextbelow(val_low);
    // mpfr_nextabove(val_high);

    bool val_below_pi = (mpfr_cmp(val_high, pi_low) < 0);
    bool val_above_pi = (mpfr_cmp(val_low, pi_high) > 0);

    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx,
                       "refine_pi_bounds: val_below_pi=%s val_above_pi=%s\n",
                       val_below_pi ? "true" : "false",
                       val_above_pi ? "true" : "false");
    }

    if (val_below_pi || val_above_pi) {
      if (val_below_pi) {
        mpq_t pi_low_q_mpq;
        mpq_init(pi_low_q_mpq);
        mpfr_get_q(pi_low_q_mpq, pi_low);
        mpq_canonicalize(pi_low_q_mpq);

        // //print pi_low_q_mpq for debugging
        // if (ctx_trace_enabled(na->ctx, "na::nta")) {
        //   ctx_trace_printf(na->ctx, "refine_pi_bounds: pi_low_q_mpq=");
        //   mpq_out_str(ctx_trace_out(na->ctx), 10, pi_low_q_mpq);
        //   ctx_trace_printf(na->ctx, "\n");
        // }

        rational_t pi_low_q;
        q_init(&pi_low_q);
        q_set_mpq(&pi_low_q, pi_low_q_mpq);
        mpq_clear(pi_low_q_mpq);


        // print rational_t pi_low_q for debugging
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx, "refine_pi_bounds: pi_low_q=");
          q_print(ctx_trace_out(na->ctx),&pi_low_q);
          ctx_trace_printf(na->ctx, "\n");
        }



        term_t pi_low_term = mk_arith_constant(tm, &pi_low_q);
        q_clear(&pi_low_q);

        term_t lower_bound = _o_yices_arith_geq_atom(pi_term, pi_low_term);
        ivector_push(refinements, lower_bound);
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx, "refine_pi_bounds: adding lower bound: ");
          ctx_trace_term(na->ctx, lower_bound);
          // print polarity the term
          ctx_trace_printf(na->ctx, "\n");
          bool is_pos = is_pos_term(lower_bound);
          bool is_neg = is_neg_term(lower_bound);
          // print polarity info
          ctx_trace_printf(na->ctx, "refine_pi_bounds: lower_bound is_pos=%s is_neg=%s\n",
                           is_pos ? "true" : "false",
                           is_neg ? "true" : "false");    
        }
          
      } else {
        mpq_t pi_high_q_mpq;
        mpq_init(pi_high_q_mpq);
        mpfr_get_q(pi_high_q_mpq, pi_high);
        mpq_canonicalize(pi_high_q_mpq);

        rational_t pi_high_q;
        q_init(&pi_high_q);
        q_set_mpq(&pi_high_q, pi_high_q_mpq);
        mpq_clear(pi_high_q_mpq);

        term_t pi_high_term = mk_arith_constant(tm, &pi_high_q);
        q_clear(&pi_high_q);

        term_t upper_bound = _o_yices_arith_geq_atom(pi_high_term, pi_term);
        ivector_push(refinements, upper_bound);
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx, "refine_pi_bounds: adding upper bound: ");
          ctx_trace_term(na->ctx, upper_bound);
        }
      }

      mpfr_clear(pi_low);
      mpfr_clear(pi_high);
      mpfr_clear(val_low);
      mpfr_clear(val_high);
      arb_clear(pi_arb);
      arb_clear(val_pi_arb);
      return true;
    }

    mpfr_clear(pi_low);
    mpfr_clear(pi_high);
    mpfr_clear(val_low);
    mpfr_clear(val_high);
    arb_clear(pi_arb);
    arb_clear(val_pi_arb);

    precision += 8;
  }

  return false;
}

/**
 * Convert an mcsat_value_t to an ARB number (with upward rounding for safety).
 * Returns true on success, false if the value cannot be converted.
 * Note: this does not provide abritrary precision; it is limited by double precision (see lp_value_to_double)
 */
    // Note: this does not provide abritrary precision for LP_VALUE_ALGEBRAIC
    //  but it's limited by double precision (see lp_value_to_double)
static bool mcsat_value_to_arb(const mcsat_value_t *value, arb_t result, slong prec) {
  if (value->type == VALUE_RATIONAL) {
    // Convert rational to ARB
    // Get GMP mpq pointer
    rational_t *q = (rational_t*) &value->q;
    mpq_t gmp_q;
    mpq_init(gmp_q);
    q_get_mpq(q, gmp_q);
    
    // Get numerator and denominator from GMP
    mpz_ptr num = mpq_numref(gmp_q);
    mpz_ptr den = mpq_denref(gmp_q);
    
    // Convert to FLINT types and set in ARB
    fmpz_t fmpz_num, fmpz_den;
    fmpz_init(fmpz_num);
    fmpz_init(fmpz_den);
    
    fmpz_set_mpz(fmpz_num, num);
    fmpz_set_mpz(fmpz_den, den);
    
    // Set result = numerator / denominator in ARB
    arb_set_fmpz(result, fmpz_num);
    if (!fmpz_is_one(fmpz_den)) {
      arb_t denom_arb;
      arb_init(denom_arb);
      arb_set_fmpz(denom_arb, fmpz_den);
      arb_div(result, result, denom_arb, prec);
      arb_clear(denom_arb);
    }
    
    fmpz_clear(fmpz_num);
    fmpz_clear(fmpz_den);
    mpq_clear(gmp_q);
    return true;
  } else if (value->type == VALUE_LIBPOLY) {
    /* Convert libpoly value to ARB. For algebraic numbers, use safe
     * lower/upper double bounds. For other numeric types, use exact
     * conversion via GMP/ARB.
     */
    lp_value_t* lp_val = (lp_value_t*) &value->lp_value;

    switch (lp_val->type) {
    case LP_VALUE_INTEGER: {
      fmpz_t fmpz_num;
      fmpz_init(fmpz_num);
      fmpz_set_mpz(fmpz_num, &lp_val->value.z);
      arb_set_fmpz(result, fmpz_num);
      fmpz_clear(fmpz_num);
      return true;
    }

    case LP_VALUE_RATIONAL: {
      mpq_t q;
      q[0] = lp_val->value.q;
      mpz_ptr num = mpq_numref(q);
      mpz_ptr den = mpq_denref(q);

      fmpz_t fmpz_num, fmpz_den;
      fmpz_init(fmpz_num);
      fmpz_init(fmpz_den);

      fmpz_set_mpz(fmpz_num, num);
      fmpz_set_mpz(fmpz_den, den);

      arb_set_fmpz(result, fmpz_num);
      if (!fmpz_is_one(fmpz_den)) {
        arb_t denom_arb;
        arb_init(denom_arb);
        arb_set_fmpz(denom_arb, fmpz_den);
        arb_div(result, result, denom_arb, prec);
        arb_clear(denom_arb);
      }

      fmpz_clear(fmpz_num);
      fmpz_clear(fmpz_den);
      return true;
    }

    case LP_VALUE_DYADIC_RATIONAL: {
      lp_integer_t num;
      lp_integer_t den;
      lp_integer_construct(&num);
      lp_integer_construct(&den);
      lp_dyadic_rational_get_num(&lp_val->value.dy_q, &num);
      lp_dyadic_rational_get_den(&lp_val->value.dy_q, &den);

      fmpz_t fmpz_num, fmpz_den;
      fmpz_init(fmpz_num);
      fmpz_init(fmpz_den);
      fmpz_set_mpz(fmpz_num, &num);
      fmpz_set_mpz(fmpz_den, &den);

      arb_set_fmpz(result, fmpz_num);
      if (!fmpz_is_one(fmpz_den)) {
        arb_t denom_arb;
        arb_init(denom_arb);
        arb_set_fmpz(denom_arb, fmpz_den);
        arb_div(result, result, denom_arb, prec);
        arb_clear(denom_arb);
      }

      fmpz_clear(fmpz_num);
      fmpz_clear(fmpz_den);
      lp_integer_destruct(&num);
      lp_integer_destruct(&den);
      return true;
    }

    case LP_VALUE_ALGEBRAIC: {
      /* Convert libpoly algebraic value to ARB using safe lower/upper double bounds
       * provided by libpoly: lp_value_to_double_safe_from_below and
       * lp_value_to_double_safe_from_above. We build an MPFR interval with
       * directed rounding and feed it to ARB.
       * Note: here we do not have arbitrary precision but only double precision.
       */
      double lo = lp_value_to_double_safe_from_below(lp_val);
      double hi = lp_value_to_double_safe_from_above(lp_val);
      if (isnan(lo) || isnan(hi)) return false;

      mpfr_t low_mpfr, high_mpfr;
      mpfr_init2(low_mpfr, (mpfr_prec_t) prec);
      mpfr_init2(high_mpfr, (mpfr_prec_t) prec);

      /* Set with directed rounding to ensure safe bounds */
      mpfr_set_d(low_mpfr, lo, MPFR_RNDD);
      mpfr_set_d(high_mpfr, hi, MPFR_RNDU);

      arb_set_interval_mpfr(result, low_mpfr, high_mpfr, prec);

      mpfr_clear(low_mpfr);
      mpfr_clear(high_mpfr);
      return true;
    }

    case LP_VALUE_PLUS_INFINITY:
    case LP_VALUE_MINUS_INFINITY: {
      mpfr_t low_mpfr, high_mpfr;
      mpfr_init2(low_mpfr, (mpfr_prec_t) prec);
      mpfr_init2(high_mpfr, (mpfr_prec_t) prec);
      if (lp_val->type == LP_VALUE_PLUS_INFINITY) {
        mpfr_set_inf(low_mpfr, 1);
        mpfr_set_inf(high_mpfr, 1);
      } else {
        mpfr_set_inf(low_mpfr, -1);
        mpfr_set_inf(high_mpfr, -1);
      }
      arb_set_interval_mpfr(result, low_mpfr, high_mpfr, prec);
      mpfr_clear(low_mpfr);
      mpfr_clear(high_mpfr);
      return true;
    }

    case LP_VALUE_NONE:
    default:
      assert(false);
      return false;
    }
  }
  
  assert(false);
  return false;
}

/**
 * Compute Taylor series as a Yices arithmetic term (no binomial expansion):
 *  sum_{k=0..degree} a_k * (t - c)^k
 * Where each power (t-c)^k is built by repeated multiplication using rba_buffer_mul_term_power.
 * Center is one of: 0, pi/2, pi, or 3*pi/2, and sin_c/cos_c are computed exactly.
 */
term_t compute_taylor_approximation_of_sin(na_plugin_t *na, term_manager_t *tm, nta_info_t *nta_info, term_t t, taylor_center_kind_t center_kind, int degree) {
  if (na != NULL && ctx_trace_enabled(na->ctx, "na::nta")) {
    ctx_trace_printf(na->ctx, "compute_taylor_approximation_of_sin: t=");
    ctx_trace_term(na->ctx, t);
    ctx_trace_printf(na->ctx,
                     "t=%d, center=%d degree=%d\n",
                     t, center_kind, degree);
  }
  // Ensure pi term exists in nta_info
  term_t pi_term = nta_info_get_pi(nta_info);
  assert(pi_term != NULL_TERM);

  term_t cterm;  // center term

  int sin_c_val, cos_c_val;

  /* Compute center term and exact sin/cos values based on enum */
  switch (center_kind) {
  case TAYLOR_CENTER_ZERO: {
    // c = 0
    cterm = _o_yices_int32(0);
    sin_c_val = 0;
    cos_c_val = 1;
    break;
  }
  case TAYLOR_CENTER_PI_2: {
    // c = pi / 2
    term_t half = _o_yices_rational32(1, 2);
    cterm = _o_yices_mul(half, pi_term);
    sin_c_val = 1;
    cos_c_val = 0;
    break;
  }
  case TAYLOR_CENTER_PI: {
    // c = pi
    cterm = pi_term;
    sin_c_val = 0;
    cos_c_val = -1;
    break;
  }
  case TAYLOR_CENTER_PI_3_2: {
    // c = 3*pi/2
    term_t three_halves = _o_yices_rational32(3, 2);
    cterm = _o_yices_mul(three_halves, pi_term);
    sin_c_val = -1;
    cos_c_val = 0;
    break;
  }
  case TAYLOR_CENTER_2_PI: {
    // c = 0
    cterm = _o_yices_mul(_o_yices_int32(2), pi_term);
    sin_c_val = 0;
    cos_c_val = 1;
    break;
  }
  default:
    assert(false);
    return NULL_TERM;
  }

  // Precompute factorial terms
  term_t *fact_term = (term_t*) malloc((degree + 1) * sizeof(term_t));
  if (fact_term == NULL) return NULL_TERM;
  fact_term[0] = _o_yices_int32(1);
  for (int i = 1; i <= degree; ++i) {
    term_t i_term = _o_yices_int32(i);
    fact_term[i] = _o_yices_mul(fact_term[i - 1], i_term);
  }

  // build t - c term
  term_t t_minus_c = _o_yices_sub(t, cterm);

  // build the polynomial buffer: sum_k a_k * (t-c)^k
  term_table_t *tbl = term_manager_get_terms(tm);
  rba_buffer_t *b = term_manager_get_arith_buffer(tm);
  reset_rba_buffer(b);

  for (int k = 0; k <= degree; ++k) {
    // Compute a_k as rational: num / fact[k]
    rational_t num_rat, fact_rat_k, a_k;
    q_init(&num_rat);
    q_init(&fact_rat_k);
    q_init(&a_k);
    
    // Compute num_val
    int num_val = (k % 4 == 0) ? sin_c_val : (k % 4 == 1) ? cos_c_val : (k % 4 == 2) ? -sin_c_val : -cos_c_val;
    q_set_int32(&num_rat, num_val, 1);
    
    // Get rational from fact_term[k]
    rational_t *fact_rat_ptr = rational_term_desc(tbl, fact_term[k]);
    q_set(&fact_rat_k, fact_rat_ptr);
    
    q_set(&a_k, &num_rat);
    q_div(&a_k, &fact_rat_k);
    
    q_clear(&num_rat);
    q_clear(&fact_rat_k);

    if (k == 0) {
      rba_buffer_add_const(b, &a_k);
    } else {
      // Create a copy of buffer with just the coefficient
      rba_buffer_t aux;
      init_rba_buffer(&aux, term_manager_get_pprods(tm));
      rba_buffer_add_const(&aux, &a_k);
      // Multiply by (t_minus_c)^k
      rba_buffer_mul_term_power(&aux, tbl, t_minus_c, (uint32_t) k);
      // Add the result to main buffer
      rba_buffer_add_buffer(b, &aux);
      delete_rba_buffer(&aux);
    }

    q_clear(&a_k);
  }

  free(fact_term);

  // convert buffer into term
  term_t poly_term = mk_arith_term(tm, b);

  // print t, center_kind, and degree for debugging

  assert(poly_term != NULL_TERM);
  if (poly_term != NULL_TERM) {
    nta_info_set_last_taylor_degree(nta_info, t, center_kind, degree);
  }

  return poly_term;
}

/**
 * Compute the sine approximation of a value.
 */
mcsat_value_t compute_sin_approximation(const mcsat_value_t *value, slong prec) {
  mcsat_value_t result;
  
  // Convert value to ARB
  arb_t x_arb;
  arb_init(x_arb);
  if (!mcsat_value_to_arb(value, x_arb, prec)) {
    arb_clear(x_arb);
    result.type = VALUE_NONE;
    return result;
  }
  
  // Compute sin(x) with ARB
  arb_t sin_x_arb;
  arb_init(sin_x_arb);
  arb_sin(sin_x_arb, x_arb, prec);
  
  // Get double approximation from ARB midpoint
  arb_t mid;
  arb_init(mid);
  arb_get_mid_arb(mid, sin_x_arb);
  double sin_x = arf_get_d(arb_midref(mid), ARF_RND_NEAR);
  arb_clear(mid);
  
  arb_clear(x_arb);
  arb_clear(sin_x_arb);
  
  // Convert back to lp_value
  lp_rational_t sin_rational;
  lp_rational_construct_from_double(&sin_rational, sin_x);
  lp_value_construct(&result.lp_value, LP_VALUE_RATIONAL, &sin_rational);
  lp_rational_destruct(&sin_rational);
  result.type = VALUE_LIBPOLY;    

  
  return result;
}

/**
 * Forward declaration for recursive evaluation.
 */
static bool nta_compute_safe_range_internal(na_plugin_t* na,
                                       term_manager_t *tm, 
                                       term_t term, 
                                       const mcsat_model_t *model, 
                                       const nta_info_t *nta_info,
                                       variable_db_t *var_db,
                                       nta_value* result,
                                       ivector_t* incomplete_vars,
                                       slong prec);

/* Forward declaration for power-product evaluation */
static bool nta_compute_safe_range_pprod(na_plugin_t* na,
                                    term_manager_t *tm,
                                    pprod_t *p,
                                    const mcsat_model_t *model,
                                    const nta_info_t *nta_info,
                                    variable_db_t *var_db,
                                    nta_value* result,
                                    ivector_t* incomplete_vars,
                                    slong prec);

/**
 * Compute safe range for a constant term.
 */
static bool nta_compute_safe_range_constant(term_t term, term_table_t *tbl, nta_value* result, slong prec) {
  if (term_kind(tbl, term) != ARITH_CONSTANT) return false;
  
  rational_t *q = rational_term_desc(tbl, term);
  
  // Create mcsat_value_t from rational
  mcsat_value_t val;
  val.type = VALUE_RATIONAL;
  q_init(&val.q);
  q_set(&val.q, q);
  
  nta_value_init_mcsat(result, &val);
  
  mcsat_value_destruct(&val);
  return true;
}

/**
 * Compute safe range for a variable with special handling of sin and pi abstraction.
 */
static bool nta_compute_safe_range_variable(na_plugin_t* na,
                                       variable_t var,
                                       const mcsat_model_t *model,
                                       variable_db_t *var_db,
                                       const nta_info_t *nta_info,
                                       term_manager_t *tm,
                                       term_table_t *tbl,
                                       nta_value* result,
                                       ivector_t* incomplete_vars,
                                       slong prec) {
  // Get the term corresponding to this variable
  term_t var_term = variable_db_get_term(var_db, var);

  /* If this variable corresponds to pi in nta_info, return pi constant as ARB */
  term_t pi_term = nta_info_get_pi(nta_info);
  if (pi_term != NULL_TERM && var_term == pi_term) {
    if (trace_enabled(var_db->tracer, "na::nta")) {
      mcsat_trace_printf(var_db->tracer,
                         "nta_compute_safe_range_variable: switching to ARB (pi constant) for term %d\n",
                         var_term);
    }
    result->type = NTA_VALUE_ARB;
    arb_init(result->arb_val);
    arb_const_pi(result->arb_val, prec);
    goto result_found;
  }

  bool use_standard = false;

  // Check if this variable is an abstraction of sin(x)
  term_t sin_inverse_term = nta_info_get_sin_inverse_term(nta_info, var_term);
  if (sin_inverse_term != NULL_TERM) {
    variable_t inverse_var = variable_db_get_variable_if_exists(var_db, sin_inverse_term);
    if (inverse_var != variable_null && !trail_has_value(na->ctx->trail, inverse_var)) {
      if (trace_enabled(var_db->tracer, "na::nta")) {
        mcsat_trace_printf(var_db->tracer,
                           "nta_compute_safe_range_variable: missing inverse var for term %d, falling back to standard\n",
                           var_term);
      }
      nta_record_incomplete_var(incomplete_vars, inverse_var);
      use_standard = true;
    } else if (inverse_var == variable_null) {
      if (trace_enabled(var_db->tracer, "na::nta")) {
        mcsat_trace_printf(var_db->tracer,
                           "nta_compute_safe_range_variable: inverse_var == variable_null for term %d, falling back to standard\n",
                           var_term);
      }
      use_standard = true;
    } else if (nta_info->use_period_for_sin) {
      term_t period_term = nta_info_get_sin_period_term(nta_info, sin_inverse_term);
      if (period_term == NULL_TERM) {
        if (trace_enabled(var_db->tracer, "na::nta")) {
          mcsat_trace_printf(var_db->tracer,
                             "nta_compute_safe_range_variable: missing period term for term %d, falling back to standard\n",
                             var_term);
        }
        use_standard = true;
      } else {
        variable_t period_var = variable_db_get_variable_if_exists(var_db, period_term);
        if (period_var != variable_null && !trail_has_value(na->ctx->trail, period_var)) {
          if (trace_enabled(var_db->tracer, "na::nta")) {
            mcsat_trace_printf(var_db->tracer,
                               "nta_compute_safe_range_variable: missing period var for term %d, falling back to standard\n",
                               var_term);
          }
          nta_record_incomplete_var(incomplete_vars, period_var);
          use_standard = true;
        } else if (period_var == variable_null) {
          if (trace_enabled(var_db->tracer, "na::nta")) {
            mcsat_trace_printf(var_db->tracer,
                               "nta_compute_safe_range_variable: period_var == variable_null for term %d, falling back to standard\n",
                               var_term);
          }
          use_standard = true;
        }
      }
    }

    if (!use_standard) {
      nta_notable_value_kind_t notable = nta_var_has_notable_value_pi(na, inverse_var, nta_info, var_db);
      if (notable != NO_NOTABLE_VALUE) {
        result->type = NTA_VALUE_ARB;
        arb_init(result->arb_val);
        switch (notable) {
        case IS_ZERO:
        case IS_PI:
          arb_zero(result->arb_val);
          break;
        case IS_PI_2:
          arb_one(result->arb_val);
          break;
        case IS_PI_3_2:
          arb_set_si(result->arb_val, -1);
          break;
        case NO_NOTABLE_VALUE:
        default:
          assert(false);
        }
        goto result_found;
      }
      nta_value inv_value;
      if (nta_compute_safe_range_variable(na, inverse_var, model, var_db, nta_info, tm, tbl, &inv_value, incomplete_vars, prec)) {
        arb_t inv_arb;
        arb_init(inv_arb);
        if (!nta_value_to_arb(&inv_value, inv_arb, prec)) {
          arb_clear(inv_arb);
          nta_value_clear(&inv_value);
          assert(false);
          use_standard = true;
        } else {
          if (trace_enabled(var_db->tracer, "na::nta")) {
            mcsat_trace_printf(var_db->tracer,
                                "nta_compute_safe_range_variable: switching to ARB (sin) for term %d\n",
                                var_term);
          }
          result->type = NTA_VALUE_ARB;
          arb_init(result->arb_val);
          arb_sin(result->arb_val, inv_arb, prec);
          arb_clear(inv_arb);
          nta_value_clear(&inv_value);
          goto result_found;
        }
      } else {
        use_standard = true;
      }
    }
  }

  // Check if this variable is an abstraction of exp(x)
  term_t exp_inverse_term = nta_info_get_exp_inverse_term(nta_info, var_term);
  if (!use_standard && exp_inverse_term != NULL_TERM) {
    variable_t inverse_var = variable_db_get_variable_if_exists(var_db, exp_inverse_term);
    if (inverse_var != variable_null && !trail_has_value(na->ctx->trail, inverse_var)) {
      if (trace_enabled(var_db->tracer, "na::nta")) {
        mcsat_trace_printf(var_db->tracer,
                           "nta_compute_safe_range_variable: missing inverse var for exp term %d, falling back to standard\n",
                           var_term);
      }
      nta_record_incomplete_var(incomplete_vars, inverse_var);
      use_standard = true;
    } else if (inverse_var == variable_null) {
      if (trace_enabled(var_db->tracer, "na::nta")) {
        mcsat_trace_printf(var_db->tracer,
                           "nta_compute_safe_range_variable: inverse_var == variable_null for exp term %d, falling back to standard\n",
                           var_term);
      }
      use_standard = true;
    } else {
      nta_value inv_value;
      if (nta_compute_safe_range_variable(na, inverse_var, model, var_db, nta_info, tm, tbl, &inv_value, incomplete_vars, prec)) {
        arb_t inv_arb;
        arb_init(inv_arb);
        if (!nta_value_to_arb(&inv_value, inv_arb, prec)) {
          arb_clear(inv_arb);
          nta_value_clear(&inv_value);
          assert(false);
          use_standard = true;
        } else {
          if (trace_enabled(var_db->tracer, "na::nta")) {
            mcsat_trace_printf(var_db->tracer,
                                "nta_compute_safe_range_variable: switching to ARB (exp) for term %d\n",
                                var_term);
          }
          result->type = NTA_VALUE_ARB;
          arb_init(result->arb_val);
          arb_exp(result->arb_val, inv_arb, prec);
          arb_clear(inv_arb);
          nta_value_clear(&inv_value);
          goto result_found;
        }
      } else {
        use_standard = true;
      }
    }
  }

  // Check if this variable is an abstraction of a complex argument
  if (!use_standard && sin_inverse_term == NULL_TERM) { // this if is superflous?
    term_t arg_term = nta_info_get_inverse_arg_term(nta_info, var_term);
    if (arg_term != NULL_TERM) {
      if (trace_enabled(var_db->tracer, "na::nta")) {
        FILE* out = trace_out(var_db->tracer);
        mcsat_trace_printf(var_db->tracer,
                           "nta_compute_safe_range_variable: var_term = ");
        print_term_name(out, tbl, var_term);
        mcsat_trace_printf(var_db->tracer, " (arg_term = ");
        print_term_name(out, tbl, arg_term);
        mcsat_trace_printf(var_db->tracer, ")\n");
      }

      nta_value arg_value;
      if (nta_compute_safe_range(na, arg_term, model, nta_info, var_db, &arg_value, incomplete_vars, prec)) {
        if (arg_value.type == NTA_VALUE_MCSAT) {
          nta_value_init_mcsat(result, &arg_value.mcsat_val);
        } else {
          result->type = NTA_VALUE_ARB;
          arb_init(result->arb_val);
          arb_set(result->arb_val, arg_value.arb_val);
        }
        nta_value_clear(&arg_value);
        goto result_found;
      }
      use_standard = true;
    }
  }

  // Standard variable: return its value from the trail
  if (!trail_has_value(na->ctx->trail, var)) {
    nta_record_incomplete_var(incomplete_vars, var);
    return false;
  }

  const mcsat_value_t *value = trail_get_value(na->ctx->trail, var);
  if (value->type == VALUE_NONE) {
    nta_record_incomplete_var(incomplete_vars, var);
    return false;
  }

  nta_notable_value_kind_t notable = nta_var_has_notable_value_pi(na, var, nta_info, var_db);
  if (notable != NO_NOTABLE_VALUE) {
    variable_t period_var = variable_null;
    if (nta_get_period_var_for_variable(nta_info, var_db, var, &period_var) &&
        trail_has_value(na->ctx->trail, period_var)) {
      const mcsat_value_t* period_value = trail_get_value(na->ctx->trail, period_var);
      if (period_value->type != VALUE_NONE) {
        result->type = NTA_VALUE_ARB;
        arb_init(result->arb_val);
        if (nta_build_notable_value_arb(period_value, notable, result->arb_val, prec)) {
          goto result_found;
        }
        arb_clear(result->arb_val);
      }
    }
  }

  if (trace_enabled(var_db->tracer, "na::nta")) {
    FILE* out = trace_out(var_db->tracer);
    mcsat_trace_printf(var_db->tracer,
                       "nta_compute_safe_range_variable: standard var_term=%d value=",
                       var_term);
    mcsat_value_print(value, out);
    mcsat_trace_printf(var_db->tracer, "\n");
  }
  nta_value_init_mcsat(result, value);

  result_found : 
    // print result
    if (trace_enabled(var_db->tracer, "na::nta")) {
      FILE* out = trace_out(var_db->tracer);
      mcsat_trace_printf(var_db->tracer,
                         "nta_compute_safe_range_variable: result for variable "
                         );
      variable_db_print_variable(na->ctx->var_db, var, ctx_trace_out(na->ctx));
      mcsat_trace_printf(var_db->tracer, " is ");
      // print `result`
      nta_value_print(na, result, out, prec);
      mcsat_trace_printf(var_db->tracer, "\n");
    }
    return true;
}

/**
 * Compute safe range for an arithmetic polynomial.
 */
static bool nta_compute_safe_range_poly(na_plugin_t* na,
                                   term_t term,
                                   term_manager_t *tm,
                                   const mcsat_model_t *model,
                                   const nta_info_t *nta_info,
                                   variable_db_t *var_db,
                                   nta_value* result,
                                   ivector_t* incomplete_vars,
                                   slong prec) {
  term_table_t *tbl = term_manager_get_terms(tm);
  polynomial_t *poly = poly_term_desc(tbl, term);
  
  // Initialize two results: one for mcsat, one for arb
  mcsat_value_t result_mcsat;
  result_mcsat.type = VALUE_RATIONAL;
  q_init(&result_mcsat.q);
  q_set_int32(&result_mcsat.q, 0, 1);  // Initialize to 0
  
  arb_t result_arb;
  arb_init(result_arb);
  arb_zero(result_arb);
  bool result_arb_used = false;
  
  const int32_t const_idx = 0;
  
  // Iterate through all monomials in the polynomial
  for (uint32_t i = 0; i < poly->nterms; i++) {
    monomial_t *mono = poly->mono + i;
    
    int32_t product = mono->var;
    rational_t *coeff = &mono->coeff;
    
    // if (ctx_trace_enabled(na->ctx, "na::nta")) {
    //   ctx_trace_printf(na->ctx, "nta_compute_safe_range_poly: product = %d\n", product);
    // }
    
    // Create coefficient as mcsat_value_t
    mcsat_value_t coeff_mcsat;
    coeff_mcsat.type = VALUE_RATIONAL;
    q_init(&coeff_mcsat.q);
    q_set(&coeff_mcsat.q, coeff);
    
    if (product == const_idx) {
      if (ctx_trace_enabled(na->ctx, "na::nta")) {
        ctx_trace_printf(na->ctx, "is const_idx\n");   
      } 
      // Constant term - add coefficient
      if (result_mcsat.type == VALUE_RATIONAL) {
        q_add(&result_mcsat.q, coeff);
      } else {
        lp_value_t lp_coeff, lp_result, lp_sum;
        lp_value_construct_zero(&lp_coeff);
        lp_value_construct_zero(&lp_result);
        lp_value_construct_zero(&lp_sum);

        if (coeff_mcsat.type == VALUE_RATIONAL) {
          lp_rational_t lp_q;
          lp_rational_construct(&lp_q);
          lp_rational_construct_from_yices_rational(&lp_q, &coeff_mcsat.q);
          lp_value_construct(&lp_coeff, LP_VALUE_RATIONAL, &lp_q);
          lp_rational_destruct(&lp_q);
        } else {
          lp_value_construct_copy(&lp_coeff, &coeff_mcsat.lp_value);
        }

        if (result_mcsat.type == VALUE_RATIONAL) {
          lp_rational_t lp_q;
          lp_rational_construct(&lp_q);
          lp_rational_construct_from_yices_rational(&lp_q, &result_mcsat.q);
          lp_value_construct(&lp_result, LP_VALUE_RATIONAL, &lp_q);
          lp_rational_destruct(&lp_q);
        } else {
          lp_value_construct_copy(&lp_result, &result_mcsat.lp_value);
        }
        lp_value_add(&lp_sum, &lp_result, &lp_coeff);
        mcsat_value_destruct(&result_mcsat);
        result_mcsat.type = VALUE_LIBPOLY;
        lp_value_construct_copy(&result_mcsat.lp_value, &lp_sum);
        lp_value_destruct(&lp_coeff);
        lp_value_destruct(&lp_result);
        lp_value_destruct(&lp_sum);
      }
    } else if (term_kind(tm->terms, product) == POWER_PRODUCT) {
      // if (ctx_trace_enabled(na->ctx, "na::nta")) {
      //   ctx_trace_printf(na->ctx, "is POWER_PRODUCT\n");
      //   ctx_trace_printf(na->ctx, "(of type %d)\n", term_kind(na->ctx->terms, product));
      //   ctx_trace_term(na->ctx, product);
      // }
      // product is a term index - get the actual pprod structure
      pprod_t *pp = pprod_term_desc(tbl, product);
      // if (ctx_trace_enabled(na->ctx, "na::nta")) {
      //   ctx_trace_printf(na->ctx, "Power-product details:\n");
      //   print_pprod(ctx_trace_out(na->ctx), pp);
      // }

      nta_value pp_value;
      // Compute the value of the power-product
      if (!nta_compute_safe_range_pprod(na, tm, pp, model, nta_info, var_db, &pp_value, incomplete_vars, prec)) {
        mcsat_value_destruct(&coeff_mcsat);
        mcsat_value_destruct(&result_mcsat);
        arb_clear(result_arb);
        return false;
      }

      // Multiply coefficient * power-product value and add to result
      if (pp_value.type == NTA_VALUE_MCSAT) {
        // Multiply coeff * pp_value
        mcsat_value_t mono_val;
        if (coeff_mcsat.type == VALUE_RATIONAL && pp_value.mcsat_val.type == VALUE_RATIONAL) {
          mono_val.type = VALUE_RATIONAL;
          q_init(&mono_val.q);
          q_set(&mono_val.q, &coeff_mcsat.q);
          q_mul(&mono_val.q, &pp_value.mcsat_val.q);
        } else {
          lp_value_t lp_coeff, lp_pp, lp_product;
          lp_value_construct_zero(&lp_coeff);
          lp_value_construct_zero(&lp_pp);
          lp_value_construct_zero(&lp_product);
          
          if (coeff_mcsat.type == VALUE_RATIONAL) {
            lp_rational_t lp_q;
            lp_rational_construct(&lp_q);
            lp_rational_construct_from_yices_rational(&lp_q, &coeff_mcsat.q);
            lp_value_construct(&lp_coeff, LP_VALUE_RATIONAL, &lp_q);
            lp_rational_destruct(&lp_q);
          } else {
            lp_value_construct_copy(&lp_coeff, &coeff_mcsat.lp_value);
          }
          
          if (pp_value.mcsat_val.type == VALUE_RATIONAL) {
            lp_rational_t lp_q;
            lp_rational_construct(&lp_q);
            lp_rational_construct_from_yices_rational(&lp_q, &pp_value.mcsat_val.q);
            lp_value_construct(&lp_pp, LP_VALUE_RATIONAL, &lp_q);
            lp_rational_destruct(&lp_q);
          } else {
            lp_value_construct_copy(&lp_pp, &pp_value.mcsat_val.lp_value);
          }
          
          lp_value_mul(&lp_product, &lp_coeff, &lp_pp);
          mono_val.type = VALUE_LIBPOLY;
          lp_value_construct_copy(&mono_val.lp_value, &lp_product);
          lp_value_destruct(&lp_coeff);
          lp_value_destruct(&lp_pp);
          lp_value_destruct(&lp_product);
        }
        
        // Add to result_mcsat
        if (result_mcsat.type == VALUE_RATIONAL && mono_val.type == VALUE_RATIONAL) {
          q_add(&result_mcsat.q, &mono_val.q);
        } else {
          lp_value_t lp_result, lp_mono, lp_sum;
          lp_value_construct_zero(&lp_result);
          lp_value_construct_zero(&lp_mono);
          lp_value_construct_zero(&lp_sum);
          
          if (result_mcsat.type == VALUE_RATIONAL) {
            lp_rational_t lp_q;
            lp_rational_construct(&lp_q);
            lp_rational_construct_from_yices_rational(&lp_q, &result_mcsat.q);
            lp_value_construct(&lp_result, LP_VALUE_RATIONAL, &lp_q);
            lp_rational_destruct(&lp_q);
          } else {
            lp_value_construct_copy(&lp_result, &result_mcsat.lp_value);
          }
          
          if (mono_val.type == VALUE_RATIONAL) {
            lp_rational_t lp_q;
            lp_rational_construct(&lp_q);
            lp_rational_construct_from_yices_rational(&lp_q, &mono_val.q);
            lp_value_construct(&lp_mono, LP_VALUE_RATIONAL, &lp_q);
            lp_rational_destruct(&lp_q);
          } else {
            lp_value_construct_copy(&lp_mono, &mono_val.lp_value);
          }
          
          lp_value_add(&lp_sum, &lp_result, &lp_mono);
          mcsat_value_destruct(&result_mcsat);
          result_mcsat.type = VALUE_LIBPOLY;
          lp_value_construct_copy(&result_mcsat.lp_value, &lp_sum);
          lp_value_destruct(&lp_result);
          lp_value_destruct(&lp_mono);
          lp_value_destruct(&lp_sum);
        }
        mcsat_value_destruct(&mono_val);
      } else {
        // pp_value is ARB - accumulate separately in result_arb
        if (!result_arb_used && ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx, "nta_compute_safe_range_poly: switching to ARB (pprod)\n");
        }
        result_arb_used = true;

        // Convert coeff to arb and compute coeff * pp_value
        arb_t coeff_arb, mono_arb;
        arb_init(coeff_arb);
        arb_init(mono_arb);
        if (!mcsat_value_to_arb(&coeff_mcsat, coeff_arb, prec)) {
          nta_value_clear(&pp_value);
          mcsat_value_destruct(&coeff_mcsat);
          mcsat_value_destruct(&result_mcsat);
          arb_clear(result_arb);
          arb_clear(coeff_arb);
          arb_clear(mono_arb);
          return false;
        }
        arb_mul(mono_arb, coeff_arb, pp_value.arb_val, prec);
        arb_add(result_arb, result_arb, mono_arb, prec);
        arb_clear(coeff_arb);
        arb_clear(mono_arb);
      }

      nta_value_clear(&pp_value);
    }
    else{
      // if (ctx_trace_enabled(na->ctx, "na::nta")) {
      //   ctx_trace_printf(na->ctx, "is var\n");
      //   ctx_trace_printf(na->ctx, "(of type %d)\n", term_kind(na->ctx->terms, product));
      //   ctx_trace_term(na->ctx, product);
      // }
      // Variable
      nta_value var_value;

      /* compute the value of the variable term */
      if (!nta_compute_safe_range_internal(na, tm, product, model, nta_info, var_db, &var_value, incomplete_vars, prec)) {
        mcsat_value_destruct(&coeff_mcsat);
        mcsat_value_destruct(&result_mcsat);
        arb_clear(result_arb);
        return false;
      }

      /* multiply coefficient * variable value and add to result */
      if (var_value.type == NTA_VALUE_MCSAT) {
        // Multiply coeff * var_value
        mcsat_value_t mono_val2;
        if (coeff_mcsat.type == VALUE_RATIONAL && var_value.mcsat_val.type == VALUE_RATIONAL) {
          mono_val2.type = VALUE_RATIONAL;
          q_init(&mono_val2.q);
          q_set(&mono_val2.q, &coeff_mcsat.q);
          q_mul(&mono_val2.q, &var_value.mcsat_val.q);
        } else {
          lp_value_t lp_coeff, lp_var, lp_product;
          lp_value_construct_zero(&lp_coeff);
          lp_value_construct_zero(&lp_var);
          lp_value_construct_zero(&lp_product);
          
          if (coeff_mcsat.type == VALUE_RATIONAL) {
            lp_rational_t lp_q;
            lp_rational_construct(&lp_q);
            lp_rational_construct_from_yices_rational(&lp_q, &coeff_mcsat.q);
            lp_value_construct(&lp_coeff, LP_VALUE_RATIONAL, &lp_q);
            lp_rational_destruct(&lp_q);
          } else {
            lp_value_construct_copy(&lp_coeff, &coeff_mcsat.lp_value);
          }
          
          if (var_value.mcsat_val.type == VALUE_RATIONAL) {
            lp_rational_t lp_q;
            lp_rational_construct(&lp_q);
            lp_rational_construct_from_yices_rational(&lp_q, &var_value.mcsat_val.q);
            lp_value_construct(&lp_var, LP_VALUE_RATIONAL, &lp_q);
            lp_rational_destruct(&lp_q);
          } else {
            lp_value_construct_copy(&lp_var, &var_value.mcsat_val.lp_value);
          }
          
          lp_value_mul(&lp_product, &lp_coeff, &lp_var);
          mono_val2.type = VALUE_LIBPOLY;
          lp_value_construct_copy(&mono_val2.lp_value, &lp_product);
          lp_value_destruct(&lp_coeff);
          lp_value_destruct(&lp_var);
          lp_value_destruct(&lp_product);
        }
        
        // Add to result_mcsat
        if (result_mcsat.type == VALUE_RATIONAL && mono_val2.type == VALUE_RATIONAL) {
          q_add(&result_mcsat.q, &mono_val2.q);
        } else {
          lp_value_t lp_result, lp_mono, lp_sum;
          lp_value_construct_zero(&lp_result);
          lp_value_construct_zero(&lp_mono);
          lp_value_construct_zero(&lp_sum);
          
          if (result_mcsat.type == VALUE_RATIONAL) {
            lp_rational_t lp_q;
            lp_rational_construct(&lp_q);
            lp_rational_construct_from_yices_rational(&lp_q, &result_mcsat.q);
            lp_value_construct(&lp_result, LP_VALUE_RATIONAL, &lp_q);
            lp_rational_destruct(&lp_q);
          } else {
            lp_value_construct_copy(&lp_result, &result_mcsat.lp_value);
          }
          
          if (mono_val2.type == VALUE_RATIONAL) {
            lp_rational_t lp_q;
            lp_rational_construct(&lp_q);
            lp_rational_construct_from_yices_rational(&lp_q, &mono_val2.q);
            lp_value_construct(&lp_mono, LP_VALUE_RATIONAL, &lp_q);
            lp_rational_destruct(&lp_q);
          } else {
            lp_value_construct_copy(&lp_mono, &mono_val2.lp_value);
          }
          
          lp_value_add(&lp_sum, &lp_result, &lp_mono);
          mcsat_value_destruct(&result_mcsat);
          result_mcsat.type = VALUE_LIBPOLY;
          lp_value_construct_copy(&result_mcsat.lp_value, &lp_sum);
          lp_value_destruct(&lp_result);
          lp_value_destruct(&lp_mono);
          lp_value_destruct(&lp_sum);
        }
        mcsat_value_destruct(&mono_val2);
      } else {
        // var_value is ARB - accumulate separately in result_arb
        if (!result_arb_used && ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx, "nta_compute_safe_range_poly: switching to ARB (var)\n");
        }
        result_arb_used = true;

        // Convert coeff to arb and compute coeff * var_value
        arb_t coeff_arb, mono_arb;
        arb_init(coeff_arb);
        arb_init(mono_arb);
        if (!mcsat_value_to_arb(&coeff_mcsat, coeff_arb, prec)) {
          nta_value_clear(&var_value);
          mcsat_value_destruct(&coeff_mcsat);
          mcsat_value_destruct(&result_mcsat);
          arb_clear(result_arb);
          arb_clear(coeff_arb);
          arb_clear(mono_arb);
          return false;
        }
        arb_mul(mono_arb, coeff_arb, var_value.arb_val, prec);
        arb_add(result_arb, result_arb, mono_arb, prec);
        arb_clear(coeff_arb);
        arb_clear(mono_arb);
      }

      nta_value_clear(&var_value);
    }
    
    mcsat_value_destruct(&coeff_mcsat);
  }
  
  // Return appropriate result
  if (!result_arb_used) {
    // Only mcsat values were used
    nta_value_init_mcsat(result, &result_mcsat);
  } else {
    // Combine mcsat accumulator with arb accumulator at the end
    arb_t result_mcsat_arb;
    arb_init(result_mcsat_arb);
    if (!mcsat_value_to_arb(&result_mcsat, result_mcsat_arb, prec)) {
      mcsat_value_destruct(&result_mcsat);
      arb_clear(result_arb);
      arb_clear(result_mcsat_arb);
      return false;
    }
    arb_add(result_arb, result_arb, result_mcsat_arb, prec);
    result->type = NTA_VALUE_ARB;
    arb_init(result->arb_val);
    arb_set(result->arb_val, result_arb);
    arb_clear(result_mcsat_arb);
  }
  
  mcsat_value_destruct(&result_mcsat);
  arb_clear(result_arb);
  return true;
}

/**
 * Compute safe range for a power-product p (p = x1^d1 * ... * xn^dn)
 */
static bool nta_compute_safe_range_pprod(na_plugin_t* na,
                                    term_manager_t *tm,
                                    pprod_t *p,
                                    const mcsat_model_t *model,
                                    const nta_info_t *nta_info,
                                    variable_db_t *var_db,
                                    nta_value* result,
                                    ivector_t* incomplete_vars,
                                    slong prec) {
  //term_table_t *tbl = term_manager_get_terms(tm);
  // if (ctx_trace_enabled(na->ctx, "na::nta")) {
  //   ctx_trace_printf(na->ctx, "entering compute safe range pprod\n"); 
  // }
  if (pp_is_empty(p)) {
    mcsat_value_t one_val;
    one_val.type = VALUE_RATIONAL;
    q_init(&one_val.q);
    q_set_int32(&one_val.q, 1, 1);
    nta_value_init_mcsat(result, &one_val);
    mcsat_value_destruct(&one_val);
    return true;
  }

  if (pp_is_var(p)) {
    int32_t v = var_of_pp(p);
    return nta_compute_safe_range_internal(na, tm, v, model, nta_info, var_db, result, incomplete_vars, prec);
  }
  
  // Keep two accumulators: one for mcsat_value_t and one for arb_t
  mcsat_value_t acc_mcsat;
  acc_mcsat.type = VALUE_RATIONAL;
  q_init(&acc_mcsat.q);
  q_set_int32(&acc_mcsat.q, 1, 1);  // Start with 1
  
  arb_t acc_arb;
  arb_init(acc_arb);
  arb_one(acc_arb);  // multiplicative identity
  bool acc_arb_used = false;  // Track if we've ever used arb accumulator

  // printing p
  // if (ctx_trace_enabled(na->ctx, "na::nta")) {
  //   ctx_trace_printf(na->ctx, "pprod len: %u\n", p->len); 
  //   for (uint32_t i = 0; i < p->len; i++) {
  //     ctx_trace_printf(na->ctx, "pprod var: %d, exp: %u\n", p->prod[i].var, p->prod[i].exp); 
  //   }
  // }

  for (uint32_t i = 0; i < p->len; i++) {
    int32_t v = p->prod[i].var;
    uint32_t d = p->prod[i].exp;
    // print var and exponent
    // if (ctx_trace_enabled(na->ctx, "na::nta")) {
    //   ctx_trace_printf(na->ctx, "pprod var: %d, exp: %u\n", v, d); 
    // }

    nta_value vr;
    if (!nta_compute_safe_range_internal(na, tm, v, model, nta_info, var_db, &vr, incomplete_vars, prec)) {
      mcsat_value_destruct(&acc_mcsat);
      arb_clear(acc_arb);
      return false;
    }

    if (vr.type == NTA_VALUE_MCSAT) {
      // Raise mcsat value to power d
      if (d == 1) {
        // Multiply acc_mcsat by vr.mcsat_val
        if (vr.mcsat_val.type == VALUE_RATIONAL && acc_mcsat.type == VALUE_RATIONAL) {
          q_mul(&acc_mcsat.q, &vr.mcsat_val.q);
        } else {
          lp_value_t lp_acc, lp_vr, lp_result;
          lp_value_construct_zero(&lp_acc);
          lp_value_construct_zero(&lp_vr);
          lp_value_construct_zero(&lp_result);
          
          if (acc_mcsat.type == VALUE_RATIONAL) {
            lp_rational_t lp_q;
            lp_rational_construct(&lp_q);
            lp_rational_construct_from_yices_rational(&lp_q, &acc_mcsat.q);
            lp_value_construct(&lp_acc, LP_VALUE_RATIONAL, &lp_q);
            lp_rational_destruct(&lp_q);
          } else {
            lp_value_construct_copy(&lp_acc, &acc_mcsat.lp_value);
          }
          
          if (vr.mcsat_val.type == VALUE_RATIONAL) {
            lp_rational_t lp_q;
            lp_rational_construct(&lp_q);
            lp_rational_construct_from_yices_rational(&lp_q, &vr.mcsat_val.q);
            lp_value_construct(&lp_vr, LP_VALUE_RATIONAL, &lp_q);
            lp_rational_destruct(&lp_q);
          } else {
            lp_value_construct_copy(&lp_vr, &vr.mcsat_val.lp_value);
          }
          
          lp_value_mul(&lp_result, &lp_acc, &lp_vr);
          
          mcsat_value_destruct(&acc_mcsat);
          lp_value_destruct(&lp_acc);
          lp_value_destruct(&lp_vr);
          
          acc_mcsat.type = VALUE_LIBPOLY;
          lp_value_construct_copy(&acc_mcsat.lp_value, &lp_result);
          lp_value_destruct(&lp_result);
        }
      } else {
        // d > 1: compute power
        lp_value_t lp_vr, lp_result;
        lp_value_construct_zero(&lp_vr);
        lp_value_construct_zero(&lp_result);
        
        if (vr.mcsat_val.type == VALUE_RATIONAL) {
          lp_rational_t lp_q;
          lp_rational_construct(&lp_q);
          lp_rational_construct_from_yices_rational(&lp_q, &vr.mcsat_val.q);
          lp_value_construct(&lp_vr, LP_VALUE_RATIONAL, &lp_q);
          lp_rational_destruct(&lp_q);
        } else {
          lp_value_construct_copy(&lp_vr, &vr.mcsat_val.lp_value);
        }
        lp_value_pow(&lp_result, &lp_vr, d);
        
        lp_value_t lp_acc, lp_final;
        lp_value_construct_zero(&lp_acc);
        lp_value_construct_zero(&lp_final);
        
        if (acc_mcsat.type == VALUE_RATIONAL) {
          lp_rational_t lp_q;
          lp_rational_construct(&lp_q);
          lp_rational_construct_from_yices_rational(&lp_q, &acc_mcsat.q);
          lp_value_construct(&lp_acc, LP_VALUE_RATIONAL, &lp_q);
          lp_rational_destruct(&lp_q);
        } else {
          lp_value_construct_copy(&lp_acc, &acc_mcsat.lp_value);
        }
        lp_value_mul(&lp_final, &lp_acc, &lp_result);
        
        mcsat_value_destruct(&acc_mcsat);
        lp_value_destruct(&lp_vr);
        lp_value_destruct(&lp_result);
        lp_value_destruct(&lp_acc);
        
        acc_mcsat.type = VALUE_LIBPOLY;
        lp_value_construct_copy(&acc_mcsat.lp_value, &lp_final);
        lp_value_destruct(&lp_final);
      }
    } else {
      // vr is ARB type - accumulate separately in acc_arb
      if (!acc_arb_used && ctx_trace_enabled(na->ctx, "na::nta")) {
        ctx_trace_printf(na->ctx, "nta_compute_safe_range_pprod: switching to ARB (var)\n");
      }
      acc_arb_used = true;

      // Raise vr.arb_val to power d and multiply with acc_arb
      arb_t pw;
      arb_init(pw);
      arb_pow_ui(pw, vr.arb_val, d, prec);
      arb_mul(acc_arb, acc_arb, pw, prec);
      arb_clear(pw);
    }

    nta_value_clear(&vr);
  }

  // Return the appropriate result
  if (!acc_arb_used) {
    // Only mcsat values were used
    nta_value_init_mcsat(result, &acc_mcsat);
  } else {
    // Combine mcsat accumulator with arb accumulator at the end
    arb_t acc_mcsat_arb;
    arb_init(acc_mcsat_arb);
    if (!mcsat_value_to_arb(&acc_mcsat, acc_mcsat_arb, prec)) {
      mcsat_value_destruct(&acc_mcsat);
      arb_clear(acc_arb);
      arb_clear(acc_mcsat_arb);
      return false;
    }
    arb_mul(acc_arb, acc_arb, acc_mcsat_arb, prec);
    result->type = NTA_VALUE_ARB;
    arb_init(result->arb_val);
    arb_set(result->arb_val, acc_arb);
    arb_clear(acc_mcsat_arb);
  }

  mcsat_value_destruct(&acc_mcsat);
  arb_clear(acc_arb);
  
  // if (ctx_trace_enabled(na->ctx, "na::nta")) {
  //   ctx_trace_printf(na->ctx, "exiting compute safe range pprod\n"); 
  // }
  return true;
}

/**
 * Internal recursive function for computing safe range.
 */
static bool nta_compute_safe_range_internal(na_plugin_t* na,
                                       term_manager_t *tm, 
                                       term_t term, 
                                       const mcsat_model_t *model, 
                                       const nta_info_t *nta_info,
                                       variable_db_t *var_db,
                                       nta_value* result,
                                       ivector_t* incomplete_vars,
                                       slong prec) {
  term_table_t *tbl = term_manager_get_terms(tm);
  term_kind_t kind = term_kind(tbl, term);
  
  switch (kind) {
    case ARITH_CONSTANT:
      return nta_compute_safe_range_constant(term, tbl, result, prec);

    case UNINTERPRETED_TERM: {
      variable_t var = variable_db_get_variable_if_exists(var_db, term);
      if (var == variable_null) return false;
      return nta_compute_safe_range_variable(na, var, model, var_db, nta_info, tm, tbl, result, incomplete_vars, prec);
    }

    case ARITH_ABS: {
      term_t arg = arith_abs_arg(tbl, term);
      nta_value tmp;
      bool ok = nta_compute_safe_range_internal(na, tm, arg, model, nta_info, var_db, &tmp, incomplete_vars, prec);
      if (!ok) {
        return false;
      }
      /* take absolute value */
      if (tmp.type == NTA_VALUE_MCSAT) {
        if (tmp.mcsat_val.type == VALUE_RATIONAL) {
          result->type = NTA_VALUE_MCSAT;
          result->mcsat_val.type = VALUE_RATIONAL;
          q_init(&result->mcsat_val.q);
          q_set(&result->mcsat_val.q, &tmp.mcsat_val.q);
          if (q_is_neg(&result->mcsat_val.q)) {
            q_neg(&result->mcsat_val.q);
          }
        } else {
          arb_t tmp_arb;
          arb_init(tmp_arb);
          if (!mcsat_value_to_arb(&tmp.mcsat_val, tmp_arb, prec)) {
            nta_value_clear(&tmp);
            arb_clear(tmp_arb);
            return false;
          }
          result->type = NTA_VALUE_ARB;
          arb_init(result->arb_val);
          arb_abs(result->arb_val, tmp_arb);
          arb_clear(tmp_arb);
        }
      } else {
        result->type = NTA_VALUE_ARB;
        arb_init(result->arb_val);
        arb_abs(result->arb_val, tmp.arb_val);
      }
      nta_value_clear(&tmp);
      return true;
    }

    case ITE_TERM: {
      composite_term_t *ite = ite_term_desc(tbl, term);
      assert(ite->arity == 3);

      term_t cond = ite->arg[0];
      term_t then_term = ite->arg[1];
      term_t else_term = ite->arg[2];

      nta_tristate_t cond_value = nta_compute_safe_truth_value(
        na, cond, model, nta_info, var_db, incomplete_vars, prec
      );

      if (cond_value == NTA_TRUE) {
        return nta_compute_safe_range_internal(na, tm, then_term, model, nta_info, var_db, result, incomplete_vars, prec);
      } else if (cond_value == NTA_FALSE) {
        return nta_compute_safe_range_internal(na, tm, else_term, model, nta_info, var_db, result, incomplete_vars, prec);
      } else {
        nta_value then_range;
        nta_value else_range;

        if (!nta_compute_safe_range_internal(na, tm, then_term, model, nta_info, var_db, &then_range, incomplete_vars, prec)) {
          return false;
        }
        if (!nta_compute_safe_range_internal(na, tm, else_term, model, nta_info, var_db, &else_range, incomplete_vars, prec)) {
          nta_value_clear(&then_range);
          return false;
        }

        bool ok = nta_union_ranges(&then_range, &else_range, result, prec);
        nta_value_clear(&then_range);
        nta_value_clear(&else_range);
        return ok;
      }
    }

    case ARITH_POLY:
      return nta_compute_safe_range_poly(na, term, tm, model, nta_info, var_db, result, incomplete_vars, prec);

    case POWER_PRODUCT: {
      pprod_t *p = pprod_term_desc(tbl, term);
      return nta_compute_safe_range_pprod(na, tm, p, model, nta_info, var_db, result, incomplete_vars, prec);
    }

    default:
      // print term kind
      // if ctx_trace_enabled(na->ctx, "na::nta") {
      if(ctx_trace_enabled(na->ctx, "na::nta::assert")) {
        ctx_trace_printf(na->ctx, "nta_compute_safe_range_internal: unhandled term kind %d for term %d\n", kind, term);
        ctx_trace_term(na->ctx, term);
      }
      assert(false);
      exit(1);
      return false;
  }
}

/**
 * Compute a safe over-approximation of the range of an arithmetic term using ARB.
 */
bool nta_compute_safe_range(na_plugin_t* na, term_t term, 
                       const mcsat_model_t *model, 
                       const nta_info_t *nta_info,
                       variable_db_t *var_db,
                       nta_value* result,
                       ivector_t* incomplete_vars,
                       slong precision) {
  term_manager_t *tm = na->ctx->tm;
  if (tm == NULL || model == NULL || nta_info == NULL || var_db == NULL) return false;
  
  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    ctx_trace_printf(na->ctx, "computing safe range for term %d: (of type %d)", term, term_kind(na->ctx->terms, term));
    ctx_trace_term(na->ctx, term);
  }
  
  nta_value nta_result;
  bool success = nta_compute_safe_range_internal(na, tm, term, model, nta_info, var_db, &nta_result, incomplete_vars, precision);
  
  if (!success) return false;

  // Copy nta_result into caller-provided result
  if (nta_result.type == NTA_VALUE_MCSAT) {
    nta_value_init_mcsat(result, &nta_result.mcsat_val);
  } else {
    result->type = NTA_VALUE_ARB;
    arb_init(result->arb_val);
    arb_set(result->arb_val, nta_result.arb_val);
  }
  
  nta_value_clear(&nta_result);
  
  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    FILE* out = ctx_trace_out(na->ctx);
    fprintf(out, "safe range result computed for term %d: ", term);
    
    if (result->type == NTA_VALUE_ARB) {
      fprintf(out, "(arb with precision %ld) ", precision);
      arb_fprintd(out, result->arb_val, precision);
    } else if (result->type == NTA_VALUE_MCSAT) {
      fprintf(out, "(mcsat) ");
      if (result->mcsat_val.type == VALUE_RATIONAL) {
        q_print(out, &result->mcsat_val.q);
      } else if (result->mcsat_val.type == VALUE_LIBPOLY) {
        lp_value_print(&result->mcsat_val.lp_value, out);
      } else {
        fprintf(out, "<mcsat value type %d>", result->mcsat_val.type);
      }
    } else {
      fprintf(out, "<unknown nta_value type %d>", result->type);
    }
    fprintf(out, "\n");
  }
  return true;
}

/**
 * Check consistency of a fully assigned constraint variable.
 * 
 * This function verifies that:
 * 1. The constraint variable is fully assigned in the trail
 * 2. The computed safe truth value of the corresponding term
 *    matches the value assigned in the trail
 * 
 * Uses iterative precision increase to resolve the truth value:
 * starts with precision 10 and increases by 5 until a definite
 * answer (TRUE or FALSE) is obtained.
 * 
 * @param na       The NA plugin context
 * @param prop     The trail token
 * @param cstr_var The constraint variable to check
 * 
 * @return true if the constraint variable's trail value matches
 *         the computed safe truth value, false otherwise
 */
bool nta_consistency_check(na_plugin_t* na, trail_token_t* prop, variable_t cstr_var) {
  assert(na != NULL && prop != NULL);
  assert(cstr_var != variable_null);
  
  // Ensure cstr_var is fully assigned; if it is not (e.g., freshly added lemma
  // not yet propagated), defer the check and treat as consistent for now.

  assert(trail_has_value(na->ctx->trail, cstr_var));
    
  // Get the value from the trail
  const mcsat_value_t* trail_value = trail_get_value(na->ctx->trail, cstr_var);
  assert(trail_value->type == VALUE_BOOLEAN);
  bool trail_bool = trail_value->b;


  
  // Get the term corresponding to cstr_var
  term_t t = variable_db_get_term(na->ctx->var_db, cstr_var);
  term_t atom = t;
  
  term_kind_t kind = term_kind(na->ctx->terms, t);
  // print kind
  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    ctx_trace_printf(na->ctx, "\n\nnta_consistency_check: cstr_var=");
    variable_db_print_variable(na->ctx->var_db, cstr_var, ctx_trace_out(na->ctx));
    ctx_trace_printf(na->ctx, " (id=%d) checking term %d of kind %d\n", cstr_var, t, kind);
  }

  // Only check arithmetic atoms
  assert(kind == ARITH_EQ_ATOM || kind == ARITH_GE_ATOM || kind == ARITH_ROOT_ATOM ||
         kind == EQ_TERM || kind == ARITH_BINEQ_ATOM);
  
  /* Evaluate constraint value from the trail-based model when possible */
  // bool eval_has_value = false;
  // bool eval_bool = false;
  // {
  //   term_manager_t* tm = na->ctx->tm;
  //   model_t model;
  //   evaluator_t eval;
  //   value_table_t* vtbl = NULL;
  //   nta_build_eval_from_trail(na, tm, na->ctx->var_db, &model, &eval, &vtbl);

  //   value_t v = eval_in_model(&eval, t);
  //   assert(good_object(vtbl, v));
  //   if (good_object(vtbl, v)) {
  //     if (is_true(vtbl, v)) {
  //       eval_bool = true;
  //       eval_has_value = true;
  //     } else if (is_false(vtbl, v)) {
  //       eval_bool = false;
  //       eval_has_value = true;
  //     }
  //   }

  //   delete_evaluator(&eval);
  //   delete_model(&model);
  // }

  // if (ctx_trace_enabled(na->ctx, "na::nta")) {
  //   ctx_trace_printf(na->ctx, "\nnta_consistency_check: checking constraint ");
  //   ctx_trace_term(na->ctx, t);
  //   ctx_trace_printf(na->ctx, "nta_consistency_check: trail value = %s\n", trail_bool ? "true" : "false");
  //   if (eval_has_value) {
  //     ctx_trace_printf(na->ctx, "nta_consistency_check: eval value = %s (from trail)\n", eval_bool ? "true" : "false");
  //   } else {
  //     ctx_trace_printf(na->ctx, "nta_consistency_check: eval value = <unknown> (from trail)\n");
  //   }
  // }
  
  // Iteratively increase precision until we get a definite answer
  nta_tristate_t safe_value = NTA_TRUE_OR_FALSE;
  slong precision = 10;
  slong max_precision = 10000;  // Upper limit to prevent infinite loops
  if (na->nta_info->delta_mode) {
    max_precision = (slong) na->nta_info->delta * 5;
  }
  ivector_t incomplete_vars;
  init_ivector(&incomplete_vars, 4);
  

  // Check if pi variable has a value in the trail
  term_t pi_term = nta_info_get_pi(na->nta_info);
  if (pi_term != NULL_TERM) {
    variable_t pi_var = variable_db_get_variable_if_exists(na->ctx->var_db, pi_term);
    //assert(pi_var != variable_null);
    if (!trail_has_value(na->ctx->trail, pi_var)) {
      if (ctx_trace_enabled(na->ctx, "na::nta")) {
        ctx_trace_printf(na->ctx, "nta_consistency_check: pi variable not assigned, adding constraint to pi watchlist and returning true");
        if (pi_var == variable_null) {
          ctx_trace_printf(na->ctx, " (pi_var is NULL)");
        }
        ctx_trace_printf(na->ctx, "\n");
      }
      // Add to watchlist and return true
      if (ctx_trace_enabled(na->ctx, "na::nta")) {
        ctx_trace_printf(na->ctx, "\t adding cstr_var to pi watchlist.\n");
      }
      nta_info_watchlist_add(na->nta_info, pi_term, cstr_var);
      delete_ivector(&incomplete_vars);
      return true;
    }  
  }

  while (safe_value == NTA_TRUE_OR_FALSE && precision <= max_precision) {
    safe_value = nta_compute_safe_truth_value(
      na, atom,
      &na->ctx->trail->model,
      na->nta_info,
      na->ctx->var_db,
      &incomplete_vars,
      precision
    );
    
    // If we got a definite answer, break; otherwise increase precision
    if (safe_value != NTA_TRUE_OR_FALSE) {
      break;
    }
    precision += 5;
  }
  
  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    const char* safe_value_str = (safe_value == NTA_TRUE) ? "TRUE" : 
                                   (safe_value == NTA_FALSE) ? "FALSE" : "TRUE_OR_FALSE";
    ctx_trace_printf(na->ctx, "nta_consistency_check: computed safe value = %s (precision = %ld)\n", 
                     safe_value_str, precision);
  }

  bool result;
  
  // TODO_NTA shall we change something here?
  // If we couldn't determine a precise truth value even at max precision, return false
  if (safe_value == NTA_TRUE_OR_FALSE) {
    if (na->nta_info->delta_mode) {
      if (ctx_trace_enabled(na->ctx, "na::nta")) {
        ctx_trace_printf(na->ctx, "\nnta_consistency_check: cstr_var=");
        variable_db_print_variable(na->ctx->var_db, cstr_var, ctx_trace_out(na->ctx));
        ctx_trace_printf(na->ctx, "\nnta_consistency_check: CONSISTENT (delta mode, max precision reached)\n");
      }
      if(!na->nta_info->delta_used){
        //printf("delta mode used with delta %d\n", na->nta_info->delta);
      }
      na->nta_info->delta_used = true;
      int_hset_add(&na->nta_info->delta_used_constraints, (uint32_t) cstr_var);
      result = true;
    } else {
      if (ctx_trace_enabled(na->ctx, "na::nta")) {
        ctx_trace_printf(na->ctx, "\nnta_consistency_check: cstr_var=");
        variable_db_print_variable(na->ctx->var_db, cstr_var, ctx_trace_out(na->ctx));
        ctx_trace_printf(na->ctx, "\nnta_consistency_check: INCONSISTENT (could not determine precise value)\n");
      }
      result = false;
    }
  }
  // safe_value == NTA_TRUE => trail_bool == true
  else if (safe_value == NTA_TRUE) {
    bool consistent = (trail_bool == true);
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx, "\nnta_consistency_check: cstr_var=");
      variable_db_print_variable(na->ctx->var_db, cstr_var, ctx_trace_out(na->ctx));
      ctx_trace_printf(na->ctx, "nta_consistency_check: %s (nta IA=TRUE, trail=%s)\n", 
                       consistent ? "CONSISTENT" : "INCONSISTENT",
                       trail_bool ? "true" : "false");
    }
    result = consistent;
  }
  // safe_value == NTA_FALSE => trail_bool == false
  else {
    assert(safe_value == NTA_FALSE);
    bool consistent = (trail_bool == false);
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx, "nta_consistency_check for cstr_var: ");
      variable_db_print_variable(na->ctx->var_db, cstr_var, ctx_trace_out(na->ctx));
      ctx_trace_printf(na->ctx, "\n\t %s (nta IA=FALSE, trail=%s)\n", 
                       consistent ? "CONSISTENT" : "INCONSISTENT",
                       trail_bool ? "true" : "false");
    }
    result = consistent;
  }


  if (result == true && incomplete_vars.size > 0) {
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx, "\t check passed because some variable had no value in the trail =");
    }
    for (uint32_t i = 0; i < incomplete_vars.size; i++) {
      variable_t var = incomplete_vars.data[i];
      term_t var_term = variable_db_get_term(na->ctx->var_db, var);
      if (ctx_trace_enabled(na->ctx, "na::nta")) {
        ctx_trace_printf(na->ctx, "\t adding cstr_var to variable term name =");
        ctx_trace_term(na->ctx, var_term);
        ctx_trace_printf(na->ctx, " watchlist.\n");
      }
      nta_info_watchlist_add(na->nta_info, var_term, cstr_var);
    }
  }
  delete_ivector(&incomplete_vars);

  return result;
}

bool delta_used_in_trail(const mcsat_trail_t* trail) {
  if (trail == NULL || trail->nta_info == NULL) {
    return false;
  }

  int_hset_t* delta_set = (int_hset_t*) &trail->nta_info->delta_used_constraints;
  if (int_hset_is_empty(delta_set)) {
    return false;
  }

  for (uint32_t i = 0; i < trail->elements.size; i++) {
    variable_t var = trail->elements.data[i];
    if (int_hset_member(delta_set, (uint32_t) var)) {
      return true;
    }
  }

  return false;
}

/* Build a model/evaluator from the current trail for term evaluation. */
static void nta_build_eval_from_trail(const na_plugin_t* na, term_manager_t* tm,
                                      variable_db_t* var_db, model_t* model,
                                      evaluator_t* eval, value_table_t** vtbl_out) {
  assert(na != NULL && tm != NULL && var_db != NULL && model != NULL);
  assert(eval != NULL && vtbl_out != NULL);

  const mcsat_trail_t* trail = na->ctx->trail;
  type_table_t* types = na->ctx->types;

  init_model(model, tm->terms, false);
  value_table_t* vtbl = model_get_vtbl(model);
  *vtbl_out = vtbl;

  for (uint32_t i = 0; i < trail->elements.size; ++i) {
    variable_t x_var = trail->elements.data[i];
    term_t x_term = variable_db_get_term(var_db, x_var);
    term_kind_t x_kind = term_kind(tm->terms, x_term);

    if (x_kind == UNINTERPRETED_TERM && term_type_kind(tm->terms, x_term) != FUNCTION_TYPE) {
      type_t x_type = term_type(tm->terms, x_term);
      const mcsat_value_t* x_value_mcsat = trail_get_value(trail, x_var);
      value_t x_value = mcsat_value_to_value(x_value_mcsat, types, x_type, vtbl);
      model_map_term(model, x_term, x_value);
    }
  }

  init_evaluator(eval, model);
}

/**
 * Refine NTA abstraction for a constraint by generating refined Taylor lemmas.
 * 
 * For each sin variable in the constraint, generates a refined Taylor approximation
 * that separates the abstract value from the true sin value.
 * 
 * @param na        The NA plugin
 * @param cstr_var  The constraint variable to refine
 * @param refinements Output vector to store generated refinement terms
 */
variable_t nta_refine_abstraction(na_plugin_t* na, variable_t cstr_var,
                                  ivector_t* refinements,
                                  ivector_t* refinement_literals) {
  assert(na != NULL);
  assert(cstr_var != variable_null);
  assert(refinements != NULL);
  assert(refinement_literals != NULL);
  
  variable_t conflict_var = variable_null;  // Track the selected sin variable used for refinement
  variable_t best_y_var = variable_null;
  term_t best_y = NULL_TERM;
  term_t best_x = NULL_TERM;
  const mcsat_value_t* best_val_x = NULL;
  const mcsat_value_t* best_val_sin_x = NULL;
  int best_start_degree = 0;
  bool has_candidate = false;
  variable_t best_exp_y_var = variable_null;
  term_t best_exp_y = NULL_TERM;
  term_t best_exp_x = NULL_TERM;
  const mcsat_value_t* best_exp_val_x = NULL;
  const mcsat_value_t* best_val_exp_x = NULL;
  double best_exp_distance = 0.0;
  bool has_exp_candidate = false;
  
  // Get the watch list manager and check if this constraint has a variable list
  watch_list_manager_t* wlm = &na->wlm;
  if (!watch_list_manager_has_constraint(wlm, cstr_var)) {
    assert(false);
    //return variable_null;  // No variable list for this constraint
  }
  
  // Get the list of variables in the constraint
  variable_list_ref_t list_ref = watch_list_manager_get_list_of(wlm, cstr_var);
  variable_t* var_list = watch_list_manager_get_list(wlm, list_ref);
  
  // Access the trail and nta_info
  const mcsat_trail_t* trail = na->ctx->trail;
  nta_info_t* nta_info = na->nta_info;
  term_manager_t* tm = na->ctx->tm;
  term_table_t *tbl = term_manager_get_terms(tm);
  variable_db_t* var_db = na->ctx->var_db;
  term_t pi_term = nta_info_get_pi(nta_info);
  variable_t pi_var = variable_null;
  const mcsat_value_t* val_pi = NULL;
  int pi_precision_up_to_digit = 0;

  if(pi_term != NULL_TERM)  {
    pi_var = variable_db_get_variable_if_exists(var_db, pi_term);
    if (pi_var != variable_null && trail_has_value(trail, pi_var)) {
      val_pi = trail_get_value(trail, pi_var);
      pi_precision_up_to_digit = compute_pi_precision_up_to_digit(val_pi);
    }
  }
  /* Build a model/evaluator once from the current trail for term evaluation */
  model_t model;
  evaluator_t eval;
  value_table_t* vtbl = NULL;
  nta_build_eval_from_trail(na, tm, var_db, &model, &eval, &vtbl);
  
  int64_t best_k = 0;
  bool best_k_valid = false;

  // Iterate through all variables in the constraint
  for (uint32_t i = 0; var_list[i] != variable_null; i++) {
    variable_t y_var = var_list[i];
    term_t y = variable_db_get_term(var_db, y_var);

    // print variable 
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      FILE* out = ctx_trace_out(na->ctx);
      ctx_trace_printf(na->ctx, "nta_refine_abstraction: checking variable %d (", y);
      print_term_name(out, tbl, y);
      ctx_trace_printf(na->ctx, ")\n");
    }
    
    // Check if y_var is a sin variable (key in inverse_sin_map)
    int_hmap_pair_t* find_sin = int_hmap_find(&nta_info->inverse_sin_map, y);
    if (find_sin != NULL) {
      // Get x (the preimage of y in sin)
      term_t x = find_sin->val;

      // Get x_var
      variable_t x_var = variable_db_get_variable_if_exists(var_db, x);
      if (x_var == variable_null) {
        assert(false);
      }
      
      // Get the values from the trail
      if(!trail_has_value(trail, x_var)){
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          FILE* out = ctx_trace_out(na->ctx);
          ctx_trace_printf(na->ctx, "nta_refine_abstraction: skipping variable %d (", y);
          print_term_name(out, tbl, y);
          ctx_trace_printf(na->ctx, ") because x_var %d has no value in trail\n", x_var);
        }
        continue; // x_var is not assigned yet
      }
      assert(trail_has_value(trail, y_var));
      
      const mcsat_value_t* val_x = trail_get_value(trail, x_var);
      const mcsat_value_t* val_sin_x = trail_get_value(trail, y_var);


    term_t period_term = NULL_TERM;

    bool period_has_value = false;
    //bool eval_needs_reset = false;
    if (nta_info->use_period_for_sin) {
      period_term = nta_info_get_sin_period_term(nta_info, x);
      if (period_term != NULL_TERM && term_kind(tbl, period_term) == UNINTERPRETED_TERM) {
        variable_t period_var = variable_db_get_variable_if_exists(var_db, period_term);
        if (period_var != variable_null) {
          period_has_value = trail_has_value(trail, period_var);
        }
      }
    }

    bool pi_has_value = false;
    if (pi_term != NULL_TERM && term_kind(tbl, pi_term) == UNINTERPRETED_TERM) {
      variable_t pi_var = variable_db_get_variable_if_exists(var_db, pi_term);
      if (pi_var != variable_null) {
        pi_has_value = trail_has_value(trail, pi_var);
      }
    }

    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx,
                        "nta_refine_abstraction: x_var=%d period_term_has_value=%s pi_has_value=%s\n",
                        x_var,
                        period_has_value ? "true" : "false",
                        pi_has_value ? "true" : "false");
    }

    // if (!period_has_value) {
    //   assert(period_term != NULL_TERM && term_kind(tbl, period_term) == UNINTERPRETED_TERM);
    //   double x_double = mcsat_value_to_double(val_x);
    //   double two_pi = 2.0 * M_PI;
    //   int64_t period_i = (int64_t) floor(x_double / two_pi);

    //   rational_t period_q;
    //   q_init(&period_q);
    //   q_set64(&period_q, period_i);

    //   mcsat_value_t period_val;
    //   period_val.type = VALUE_RATIONAL;
    //   q_init(&period_val.q);
    //   q_set(&period_val.q, &period_q);

    //   type_t period_type = term_type(tbl, period_term);
    //   value_t period_value = mcsat_value_to_value(&period_val, na->ctx->types, period_type, vtbl);
    //   model_map_term(&model, period_term, period_value);
    //   eval_needs_reset = true;

    //   mcsat_value_destruct(&period_val);
    //   q_clear(&period_q);
    //   period_has_value = true;
    // }

    // if (!pi_has_value) {
    //   assert(pi_term != NULL_TERM && term_kind(tbl, pi_term) == UNINTERPRETED_TERM);
    //   rational_t pi_q;
    //   q_init(&pi_q);
    //   q_set_double(&pi_q, M_PI);

    //   mcsat_value_t pi_val; 
    //   pi_val.type = VALUE_RATIONAL;
    //   q_init(&pi_val.q);
    //   q_set(&pi_val.q, &pi_q);

    //   type_t pi_type = term_type(tbl, pi_term);
    //   value_t pi_value = mcsat_value_to_value(&pi_val, na->ctx->types, pi_type, vtbl);
    //   model_map_term(&model, pi_term, pi_value);
    //   eval_needs_reset = true;

    //   mcsat_value_destruct(&pi_val);
    //   q_clear(&pi_q);
    //   pi_has_value = true;
    // }
    
    // if (ctx_trace_enabled(na->ctx, "na::nta")) {
    //   ctx_trace_printf(na->ctx,
    //                     "nta_refine_abstraction: x_var=%d period_term_has_value=%s pi_has_value=%s\n",
    //                     x_var,
    //                     period_has_value ? "true" : "false",
    //                     pi_has_value ? "true" : "false");
    // }

    // if (eval_needs_reset) {
    //   reset_evaluator(&eval);
    // }

    


      int cmp = nta_compare_sin(val_x, val_sin_x);
      // this should only happen when val_x == val_sin_x == 0
      if (cmp == 0) { 
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx,
                           "nta_refine_abstraction: skipping variable %d because val_sin_x equals sin(val_x)\n",
                           y_var);
          ctx_trace_printf(na->ctx,
                           "  val_x = ");
          mcsat_value_print(val_x, ctx_trace_out(na->ctx));
          ctx_trace_printf(na->ctx,
                           "  val_sin_x = ");
          mcsat_value_print(val_sin_x, ctx_trace_out(na->ctx));
        }

        // Either one of the variables does not have a value in the trail, or both are assigned to zero
        //assert(!trail_has_value(trail, x_var) || !trail_has_value(trail, y_var) || (mcsat_value_is_zero(val_x) && mcsat_value_is_zero(val_sin_x)));
        continue;
      }

    taylor_center_kind_t center = find_closest_taylor_center(val_x);
    nta_taylor_polarity_kind_t polarity = cmp > 0 ? NTA_TAYLOR_POLARITY_UPPER : NTA_TAYLOR_POLARITY_LOWER;

      if (pi_term == NULL_TERM) {
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx,
                           "nta_refine_abstraction: skipping variable %d because pi_term is NULL\n",
                           y_var);
        }
        continue;
      }

    term_t arg_term = x;
    int64_t k = 0;
    bool k_valid = false;
    if (nta_info->use_period_for_sin) {
      if (period_term == NULL_TERM) {
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx,
                           "nta_refine_abstraction: skipping variable %d because period_term is NULL\n",
                           y_var);
        }
        continue;
      }
      term_t two_pi = _o_yices_mul(_o_yices_rational32(2, 1), pi_term);
      term_t two_pi_period = _o_yices_mul(two_pi, period_term);
      arg_term = _o_yices_sub(x, two_pi_period);
    } else {
      if (val_pi == NULL) {
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx,
                           "nta_refine_abstraction: skipping variable %d because pi has no value\n",
                           y_var);
        }
        continue;
      }
      if (!nta_compute_period_index_from_values(val_x, val_pi, &k)) {
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx,
                           "nta_refine_abstraction: skipping variable %d because period index could not be computed\n",
                           y_var);
        }
        continue;
      }
      k_valid = true;
      term_t two_pi = _o_yices_mul(_o_yices_rational32(2, 1), pi_term);
      term_t k_term = _o_yices_int64(k);
      term_t two_pi_k = _o_yices_mul(two_pi, k_term);
      arg_term = _o_yices_sub(x, two_pi_k);
    }

      int start_degree = next_taylor_degree_for_sin(nta_info, arg_term, center, polarity);

      if (!has_candidate || start_degree < best_start_degree) {
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx,
                           "nta_refine_abstraction: selecting candidate variable %d with start_degree=%d\n",
                           y_var, start_degree);
        }
        has_candidate = true;
        best_start_degree = start_degree;
        best_y_var = y_var;
        best_y = y;
        best_x = x;
        best_val_x = val_x;
        best_val_sin_x = val_sin_x;
        best_k = k;
        best_k_valid = k_valid;
      } else {
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx,
                           "nta_refine_abstraction: skipping variable %d because start_degree=%d >= best_start_degree=%d\n",
                           y_var, start_degree, best_start_degree);
        }
      }
      continue;
    }

    // Check if y_var is an exp variable (key in inverse_exp_map)
    int_hmap_pair_t* find_exp = int_hmap_find(&nta_info->inverse_exp_map, y);
    if (find_exp != NULL) {
      term_t x = find_exp->val;
      variable_t x_var = variable_db_get_variable_if_exists(var_db, x);
      if (x_var == variable_null) {
        assert(false);
      }

      if (!trail_has_value(trail, x_var)) {
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          FILE* out = ctx_trace_out(na->ctx);
          ctx_trace_printf(na->ctx, "nta_refine_abstraction: skipping exp variable %d (", y);
          print_term_name(out, tbl, y);
          ctx_trace_printf(na->ctx, ") because x_var %d has no value in trail\n", x_var);
        }
        continue;
      }
      assert(trail_has_value(trail, y_var));

      const mcsat_value_t* val_x = trail_get_value(trail, x_var);
      const mcsat_value_t* val_exp_x = trail_get_value(trail, y_var);
      int cmp = nta_compare_exp(val_x, val_exp_x);
      if (cmp == 0) {
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx,
                           "nta_refine_abstraction: skipping exp variable %d because val_exp_x equals exp(val_x)\n",
                           y_var);
        }
        continue;
      }

      double distance = nta_exp_distance(val_x, val_exp_x);
      if (!has_exp_candidate || distance > best_exp_distance) {
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx,
                           "nta_refine_abstraction: selecting exp candidate variable %d with distance=%.17g\n",
                           y_var, distance);
        }
        has_exp_candidate = true;
        best_exp_distance = distance;
        best_exp_y_var = y_var;
        best_exp_y = y;
        best_exp_x = x;
        best_exp_val_x = val_x;
        best_val_exp_x = val_exp_x;
      } else {
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx,
                           "nta_refine_abstraction: skipping exp variable %d because distance=%.17g <= best_exp_distance=%.17g\n",
                           y_var, distance, best_exp_distance);
        }
      }
      continue;
    }

    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      FILE* out = ctx_trace_out(na->ctx);
      ctx_trace_printf(na->ctx, "nta_refine_abstraction: skipping variable %d (", y);
      print_term_name(out, tbl, y);
      ctx_trace_printf(na->ctx, ") because it is not a sin/exp variable\n");
    }
  }

  //assert(pi_var != variable_null);
  

  bool choose_pi = false;
  if (val_pi != NULL) {
    if (!has_candidate) {
      choose_pi = true;
    } else if (best_start_degree > 3 * pi_precision_up_to_digit) {
      choose_pi = true;
    }
  }

  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    ctx_trace_printf(na->ctx,
                     "nta_refine_abstraction: pi_precision_up_to_digit=%d best_start_degree=%d choose_pi=%s\n",
                     pi_precision_up_to_digit,
                     has_candidate ? best_start_degree : -1,
                     choose_pi ? "true" : "false");
  }
  //choose_pi = false;
  bool choose_exp = false;
  if (has_exp_candidate && (has_candidate || choose_pi)) {
    static double exp_choice_seed = 0.6180339887498949;
    choose_exp = drand(&exp_choice_seed) < 0.5;
  } else if (has_exp_candidate) {
    choose_exp = true;
  }

  if (choose_exp) {
    // term_t exp_lemmas[2];
    // term_t exp_main_literals[2];
    term_t exp_taylor_lemma = NULL_TERM;
    int cmp = nta_compare_exp(best_exp_val_x, best_val_exp_x);
    bool ok = false;
    if (cmp != 0) {
      bool want_upper = (cmp > 0);
      if (want_upper) {
        // ok = refine_approximation_of_exp_with_pade(na, tm, best_exp_x, best_exp_y,
        //                                            best_exp_val_x, want_upper,
        //                                            exp_lemmas, exp_main_literals);
        term_t exp_linear_lemma = NULL_TERM;
        term_t exp_linear_literal = NULL_TERM;
        ok = refine_approximation_of_exp_linear(na, tm, best_exp_x, best_exp_y,
                                                best_exp_val_x, best_val_exp_x,
                                                want_upper, &exp_linear_lemma, &exp_linear_literal);
        if (ok) {
          if (exp_linear_lemma != NULL_TERM) {
            ivector_push(refinements, exp_linear_lemma);
          }
          if (exp_linear_literal != NULL_TERM) {
            ivector_push(refinement_literals, exp_linear_literal);
          }
        }
      } else {
        ok = refine_approximation_of_exp_with_taylor(na, tm, best_exp_x, best_exp_y,
                                                     best_exp_val_x, want_upper,
                                                     &exp_taylor_lemma);
        if (ok && exp_taylor_lemma != NULL_TERM) {
          ivector_push(refinements, exp_taylor_lemma);
          ivector_push(refinement_literals, exp_taylor_lemma);
        }
      }
    } else if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx,
                       "nta_refine_abstraction: skipping exp refinement because val_exp_x equals exp(val_x)\n");
    }
    if (ok) {
      conflict_var = best_exp_y_var;
    } else if (has_candidate || choose_pi) {
      choose_exp = false;
    }
  }

  if (!choose_exp) {
    if (choose_pi) {
    uint32_t refinements_start = refinements->size;
      bool ok = refine_pi_bounds(na, tm, nta_info, var_db, val_pi, refinements);
      if (ok) {
      for (uint32_t i = refinements_start; i < refinements->size; i++) {
        ivector_push(refinement_literals, refinements->data[i]);
      }
        conflict_var = pi_var;
      } else {
        choose_pi = false;
        if (ctx_trace_enabled(na->ctx, "na::nta")) {
          ctx_trace_printf(na->ctx, "nta_refine_abstraction: failed to refine pi bounds, falling back to candidate\n");
        }
      }
    }

    if (!choose_pi) {
      assert(has_candidate);
    if(!has_candidate){
      exit(1);
    }
    term_t arg_term_override = NULL_TERM;
    if (!nta_info->use_period_for_sin && best_k_valid) {
      term_t two_pi = _o_yices_mul(_o_yices_rational32(2, 1), pi_term);
      term_t k_term = _o_yices_int64(best_k);
      term_t two_pi_k = _o_yices_mul(two_pi, k_term);
      arg_term_override = _o_yices_sub(best_x, two_pi_k);
    }

    term_t refinement_literal = NULL_TERM;
    term_t refinement = refine_taylor_approximation_of_sin(
      na, tm, best_x, best_y,
      best_val_x, best_val_sin_x,
      arg_term_override,
      &refinement_literal,
      nta_info, var_db,
      &na->lp_data, &eval, vtbl
    );

    // TODO_NTA this might lead to getting stuck, we should increase the degree increment limit after we fallback to pi refinement
    // Reached increment limit, fallback to pi refinement for now
    if(refinement == NULL_TERM){
      choose_pi = true; 
    }

    if (refinement != NULL_TERM) {
      if (!nta_info->use_period_for_sin && best_k_valid) {
        




        // term_t two_pi = _o_yices_mul(_o_yices_rational32(2, 1), pi_term);
        // term_t k_term = _o_yices_int64(best_k);
        // term_t two_pi_k = _o_yices_mul(two_pi, k_term);
        // term_t two_pi_kp1 = _o_yices_add(two_pi_k, two_pi);
        // term_t guard_lo = _o_yices_arith_lt_atom(best_x, two_pi_k);
        // term_t guard_hi = _o_yices_arith_geq_atom(best_x, two_pi_kp1);
        // term_t disjuncts[3] = { guard_lo, guard_hi, refinement };
        // refinement = _o_yices_or(3, disjuncts);
      }
      if (ctx_trace_enabled(na->ctx, "na::nta")) {
        ctx_trace_printf(na->ctx, "nta_refine_abstraction: generated refinement for variable %d: ", best_y);
        ctx_trace_term(na->ctx, refinement);
      }
      ivector_push(refinements, refinement);
      if (refinement_literal != NULL_TERM) {
        ivector_push(refinement_literals, refinement_literal);
      }
      conflict_var = best_y_var;
    }
    }
  }

  delete_evaluator(&eval);
  delete_model(&model);

  // ivector_push(refinements, yices_false());
  // if (ctx_trace_enabled(na->ctx, "na::nta")) {
  //   ctx_trace_printf(na->ctx, "nta_refine_abstraction: generated refinement lemma ");
  //   ctx_trace_term(na->ctx, yices_false());
  // }
  
  

  // check that at least one refinement was generated
  assert(refinements->size > 0);
  if(!(refinements->size > 0)){
    // kill run in release mode
    exit(1);
  }

  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    ctx_trace_printf(na->ctx, "nta_refine_abstraction: refinements list (size=%u):\n", refinements->size);
    for (uint32_t i = 0; i < refinements->size; i++) {
      ctx_trace_printf(na->ctx, "  refinement[%u]=", i);
      ctx_trace_term(na->ctx, refinements->data[i]);
    }
  }

  return conflict_var;
}


/**
 * Convert a polynomial term to libpoly form with a specified top variable.
 * This ensures that root isolation works on the correct variable.
 * For now, we just return the polynomial as-is since libpoly should handle
 * multi-variate polynomials correctly when the assignment has all needed values.
 * 
 * @param lp_data   The libpoly data structure
 * @param p_term    The polynomial term
 * @param tbl       The term table
 * @param top_term  The desired top variable term (ignored for now)
 * @param c         The scalar (usually 1)
 * 
 * @return The libpoly polynomial
 */
static lp_polynomial_t* lp_polynomial_from_term_with_top_var(lp_data_t *lp_data, term_t p_term,
                                                              term_table_t *tbl, term_t top_term,
                                                              lp_integer_t *c) {
  lp_polynomial_t* p = lp_polynomial_from_term(lp_data, p_term, tbl, c);
  if (p == NULL || top_term == NULL_TERM) {
    return p;
  }

  if (!lp_data_variable_has_term(lp_data, top_term)) {
    lp_data_add_lp_variable(lp_data, tbl, top_term);
  }
  lp_variable_t top_lp_var = lp_data_get_lp_variable_from_term(lp_data, top_term);
  lp_variable_t current_top = lp_polynomial_top_variable(p);
  if (current_top == top_lp_var) {
    return p;
  }

  lp_variable_list_t poly_vars;
  lp_variable_list_construct(&poly_vars);
  lp_polynomial_get_variables(p, &poly_vars);
  lp_variable_list_order(&poly_vars, lp_data->lp_var_order);

  size_t list_size = lp_variable_list_size(&poly_vars);
  lp_variable_t* vars = safe_malloc(sizeof(lp_variable_t) * list_size);
  lp_variable_list_copy_into(&poly_vars, vars);

  lp_variable_order_t* new_order = lp_variable_order_new();
  lp_variable_order_attach(new_order);

  for (size_t i = 0; i < list_size; i++) {
    lp_variable_t var = vars[i];
    if (var != top_lp_var) {
      lp_variable_order_push(new_order, var);
    }
  }
  if (!lp_variable_order_contains(new_order, top_lp_var)) {
    lp_variable_order_push(new_order, top_lp_var);
  }

  lp_polynomial_context_t* new_ctx = lp_polynomial_context_new(
    lp_data->lp_ctx->K,
    lp_data->lp_ctx->var_db,
    new_order
  );
  lp_polynomial_context_attach(new_ctx);
  lp_polynomial_set_context(p, new_ctx);
  lp_polynomial_set_external(p);
  lp_polynomial_ensure_order(p);

  lp_polynomial_context_detach(new_ctx);
  lp_variable_order_detach(new_order);
  lp_variable_list_destruct(&poly_vars);
  safe_free(vars);

  return p;
}

/**
 * Compute the k-th root of a polynomial using libpoly's root isolation.
 * Uses ARB for safe arithmetic.
 * 
 * @param na       The NA plugin context
 * @param tm       The term manager
 * @param p_term   The polynomial term
 * @param x_term   The root variable (for variable ordering)
 * @param k        The root index (k-th root counting from -infinity, 0-indexed)
 * @param model    The MCSAT model
 * @param nta_info The NTA info structure
 * @param var_db   The variable database
 * @param result   Output: the k-th root as mcsat_value_t
 * @param prec     The precision
 * 
 * @return true if computation succeeded, false otherwise
 */
static bool nta_compute_kth_root_of_poly(na_plugin_t* na,
                                         term_manager_t *tm,
                                         term_t p_term,
                                         term_t x_term,
                                         uint32_t k,
                                         const mcsat_model_t *model,
                                         const nta_info_t *nta_info,
                                         variable_db_t *var_db,
                                         mcsat_value_t *result,
                                         slong prec) {
  assert(tm != NULL);
  
  term_table_t *tbl = term_manager_get_terms(tm);
  
  /* Convert p_term to a libpoly polynomial with x_term as top variable */
  lp_data_t *lp_data = &na->lp_data;
  const lp_int_ring_t* K = lp_data->lp_ctx->K;
  
  lp_integer_t lp_one;
  lp_integer_construct_from_int(K, &lp_one, 1);
  
  lp_polynomial_t* p = lp_polynomial_from_term_with_top_var(lp_data, p_term, tbl, x_term, &lp_one);
  lp_integer_destruct(&lp_one);
  
  if (p == NULL) {
    assert(false);
    return false;
  }
  
  /* Get the degree to allocate root array */
  size_t p_deg = lp_polynomial_degree(p);
  assert(p_deg >= 0);
  if (p_deg == 0) {
    lp_polynomial_delete(p);
    return false;  /* Constant polynomial has no roots */
  }
  
  /* Isolate all real roots of the polynomial */
  lp_value_t* roots = safe_malloc(sizeof(lp_value_t) * p_deg);
  size_t num_roots = 0;
  bool assignment_ok = true;

  // Build libpoly assignment for all variables in p_term except x_term
  lp_variable_list_t lp_vars;
  lp_variable_list_construct(&lp_vars);
  lp_polynomial_get_variables(p, &lp_vars);

  size_t lp_vars_size = lp_variable_list_size(&lp_vars);
  lp_variable_t* lp_vars_arr = safe_malloc(sizeof(lp_variable_t) * lp_vars_size);
  lp_variable_list_copy_into(&lp_vars, lp_vars_arr);

  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    ctx_trace_printf(na->ctx, "nta_compute_kth_root_of_poly: polynomial variables = [");
    for (size_t i = 0; i < lp_vars_size; i++) {
      const char* name = lp_variable_db_get_name(lp_data->lp_var_db, lp_vars_arr[i]);
      ctx_trace_printf(na->ctx, "%s%s", (i == 0) ? "" : ", ", name != NULL ? name : "<null>");
    }
    ctx_trace_printf(na->ctx, "]\n");
  }

  for (size_t i = 0; i < lp_vars_size; i++) {
    lp_variable_t lp_var = lp_vars_arr[i];
    term_t vterm = lp_data_get_term_from_lp_variable(lp_data, lp_var);
    if (vterm == x_term) {
      continue;
    }

    variable_t var = variable_db_get_variable_if_exists(var_db, vterm);
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx, "nta_compute_kth_root_of_poly: var=");
      ctx_trace_term(na->ctx, vterm);
      ctx_trace_printf(na->ctx, " (var_id=%d) trail_has_value=%s\n",
                       var,
                       (var != variable_null && trail_has_value(na->ctx->trail, var)) ? "true" : "false");
    }
    if (var == variable_null || !trail_has_value(na->ctx->trail, var)) {
      assignment_ok = false;
      break;
    }

    const mcsat_value_t* trail_val = trail_get_value(na->ctx->trail, var);
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx, "nta_compute_kth_root_of_poly: value for ");
      ctx_trace_term(na->ctx, vterm);
      ctx_trace_printf(na->ctx, " = ");
      mcsat_value_print(trail_val, ctx_trace_out(na->ctx));
      ctx_trace_printf(na->ctx, "\n");
    }

    mcsat_value_t tmp_val;
    const mcsat_value_t* lp_val = ensure_lp_value(trail_val, &tmp_val);
    lp_assignment_set_value(lp_data->lp_assignment, lp_var, &lp_val->lp_value);
    if (lp_val != trail_val) {
      lp_value_destruct(&tmp_val.lp_value);
    }
  }

  lp_variable_list_destruct(&lp_vars);
  safe_free(lp_vars_arr);

  if (!assignment_ok) {
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx, "nta_compute_kth_root_of_poly: missing assignment for some non-top variable\n");
    }
    lp_polynomial_delete(p);
    safe_free(roots);
    return false;
  }
  
  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    lp_variable_t top_var = lp_polynomial_top_variable(p);
    const char* top_name = (top_var != lp_variable_null)
                              ? lp_variable_db_get_name(lp_data->lp_var_db, top_var)
                              : "<null>";
    int is_univar = lp_polynomial_is_univariate_m(p, lp_data->lp_assignment);
    int is_assigned = lp_polynomial_is_assigned(p, lp_data->lp_assignment);
    ctx_trace_printf(na->ctx,
                     "nta_compute_kth_root_of_poly: before root isolation, polynomial degree = %zu, top=%s, univariate_m=%s, assigned=%s\n",
                     lp_polynomial_degree(p),
                     top_name,
                     is_univar ? "true" : "false",
                     is_assigned ? "true" : "false");
  }
  
  lp_polynomial_roots_isolate(p, lp_data->lp_assignment, roots, &num_roots);
  lp_polynomial_delete(p);

  // print num_roots
  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    ctx_trace_printf(na->ctx, "nta_compute_kth_root_of_poly: isolated %zu real roots for polynomial term %d\n", num_roots, p_term);
    for (size_t i = 0; i < num_roots; i++) {
      ctx_trace_printf(na->ctx, "  root %zu: ", i);
      lp_value_print(&roots[i], ctx_trace_out(na->ctx));
      ctx_trace_printf(na->ctx, "\n");
    }
  }
  
  if (num_roots == 0 || k >= num_roots) {
    /* k-th root doesn't exist */
    for (size_t i = 0; i < num_roots; i++) {
      lp_value_destruct(roots + i);
    }
    safe_free(roots);
    return false;
  }
  
  /* Get the k-th root (k is 0-indexed) */
  lp_value_t* kth_root = roots + k;
  
  /* Copy the lp_value into result as mcsat_value_t */
  result->type = VALUE_LIBPOLY;
  lp_value_construct_copy(&result->lp_value, kth_root);
  
  /* Clean up */
  for (size_t i = 0; i < num_roots; i++) {
    lp_value_destruct(roots + i);
  }
  safe_free(roots);
  
  return true;
}

/**
 * Handle ARITH_ROOT_ATOM constraints: x ~ root_k(p) where ~ is a relation.
 * Uses safe interval arithmetic to determine if the constraint holds.
 * 
 * @param na        The NA plugin context
 * @param root_atom The root atom descriptor
 * @param model     The MCSAT model
 * @param nta_info  The NTA info structure
 * @param var_db    The variable database
 * @param prec      The precision
 * 
 * @return NTA_TRUE, NTA_FALSE, or NTA_TRUE_OR_FALSE
 */
static nta_tristate_t nta_compute_safe_range_arith_root(na_plugin_t* na,
                                                        term_t atom,
                                                        const root_atom_t *root_atom,
                                                        const mcsat_model_t *model,
                                                        const nta_info_t *nta_info,
                                                        variable_db_t *var_db,
                                                        ivector_t* incomplete_vars,
                                                        slong precision,
                                                        bool* trivial_true) {
  term_manager_t *tm = na->ctx->tm;

  if (trivial_true != NULL) {
    *trivial_true = false;
  }
  
  /* Extract fields from root atom */
  term_t x_term = root_atom->x;
  term_t p_term = root_atom->p;
  uint32_t k = root_atom->k;
  root_atom_rel_t rel = root_atom->r;

  // if (ctx_trace_enabled(na->ctx, "na::nta") && cstr_var != variable_null) {
  //   uint32_t cstr_level = 0;
  //   const mcsat_value_t* assumed = na_plugin_constraint_evaluate(na, cstr_var, &cstr_level);
  //   if (assumed != NULL) {
  //     ctx_trace_printf(na->ctx,
  //                      "nta_compute_safe_range_arith_root: assumed constraint value for cstr_var=%d is %s at level=%u\n",
  //                      cstr_var,
  //                      (assumed->type == VALUE_BOOLEAN && assumed->b) ? "true" :
  //                      (assumed->type == VALUE_BOOLEAN && !assumed->b) ? "false" : "<non-boolean>",
  //                      cstr_level);
  //   } else {
  //     ctx_trace_printf(na->ctx,
  //                      "nta_compute_safe_range_arith_root: assumed constraint value for cstr_var=%d is <unknown>\n",
  //                      cstr_var);
  //   }
  // }
  
  // print p_term 
  if(ctx_trace_enabled(na->ctx, "na::nta")) {
    const char* rel_str = (rel == ROOT_ATOM_LT) ? "<" : 
                          (rel == ROOT_ATOM_LEQ) ? "<=" :
                          (rel == ROOT_ATOM_EQ) ? "=" :
                          (rel == ROOT_ATOM_NEQ) ? "!=" :
                          (rel == ROOT_ATOM_GT) ? ">" : 
                          (rel == ROOT_ATOM_GEQ) ? ">=" : "?";
    ctx_trace_printf(na->ctx, "nta_compute_safe_range_arith_root: computing safe range for root atom: x_term=%d %s root_%d(", 
                     x_term, rel_str, k);
    ctx_trace_term(na->ctx, p_term);
    ctx_trace_printf(na->ctx, ")\n");
  }
  
  /* Compute the k-th root of p */
  mcsat_value_t root_value;
  if (!nta_compute_kth_root_of_poly(na, tm, p_term, x_term, k, model, nta_info, var_db, &root_value, precision)) {
    // if (ctx_trace_enabled(na->ctx, "na::nta")) {
    //   term_manager_t* tm_eval = na->ctx->tm;
    //   model_t model_eval;
    //   evaluator_t eval;
    //   value_table_t* vtbl = NULL;
    //   nta_build_eval_from_trail(na, tm_eval, na->ctx->var_db, &model_eval, &eval, &vtbl);

    //   value_t v = eval_in_model(&eval, atom);
    //   if (good_object(vtbl, v)) {
    //     if (is_true(vtbl, v)) {
    //       ctx_trace_printf(na->ctx,
    //                        "nta_compute_safe_range_arith_root: eval_in_model(atom) = true (no real roots)\n");
    //     } else if (is_false(vtbl, v)) {
    //       ctx_trace_printf(na->ctx,
    //                        "nta_compute_safe_range_arith_root: eval_in_model(atom) = false (no real roots)\n");
    //     } else {
    //       ctx_trace_printf(na->ctx,
    //                        "nta_compute_safe_range_arith_root: eval_in_model(atom) = <non-boolean> (no real roots)\n");
    //     }
    //   } else {
    //     ctx_trace_printf(na->ctx,
    //                      "nta_compute_safe_range_arith_root: eval_in_model(atom) = <unknown> (no real roots)\n");
    //   }

    //   delete_evaluator(&eval);
    //   delete_model(&model_eval);
    // }
    if (trivial_true != NULL) {
      *trivial_true = true;
    }
    return NTA_TRUE;
  }
  
  /* Compute the value of x */
  nta_value x_value;
  if (!nta_compute_safe_range(na, x_term, model, nta_info, var_db, &x_value, incomplete_vars, precision)) {
    mcsat_value_destruct(&root_value);
    assert(false);
    return NTA_TRUE_OR_FALSE;
  }

  nta_tristate_t result = NTA_TRUE_OR_FALSE;

  if (x_value.type == NTA_VALUE_ARB) {
    /* ARB path: convert both values to ARB and use interval comparison */
    arb_t root_value_arb;
    arb_init(root_value_arb);
    if (!mcsat_value_to_arb(&root_value, root_value_arb, precision)) {
      mcsat_value_destruct(&root_value);
      nta_value_clear(&x_value);
      arb_clear(root_value_arb);
      assert(false);
      return NTA_TRUE_OR_FALSE;
    }

    arb_t x_value_arb;
    arb_init(x_value_arb);
    if (!nta_value_to_arb(&x_value, x_value_arb, precision)) {
      nta_value_clear(&x_value);
      mcsat_value_destruct(&root_value);
      arb_clear(x_value_arb);
      arb_clear(root_value_arb);
      assert(false);
      return NTA_TRUE_OR_FALSE;
    }
    
    /* Extract interval endpoints */
    mpfr_t x_low, x_high, root_low, root_high;
    mpfr_init2(x_low, (mpfr_prec_t) precision);
    mpfr_init2(x_high, (mpfr_prec_t) precision);
    mpfr_init2(root_low, (mpfr_prec_t) precision);
    mpfr_init2(root_high, (mpfr_prec_t) precision);
    
    arb_get_interval_mpfr(x_low, x_high, x_value_arb);
    arb_get_interval_mpfr(root_low, root_high, root_value_arb);

    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      FILE* out = ctx_trace_out(na->ctx);
      ctx_trace_printf(na->ctx, "nta_compute_safe_range_arith_root: x_value_arb=");
      arb_fprintd(out, x_value_arb, precision);
      ctx_trace_printf(na->ctx, " root_value_arb=");
      arb_fprintd(out, root_value_arb, precision);
      ctx_trace_printf(na->ctx, "\n");
    }
    
    /* Compare based on the relation */
    int cmp_low = mpfr_cmp(x_low, root_high);    /* x_low vs root_high */
    int cmp_high = mpfr_cmp(x_high, root_low);   /* x_high vs root_low */

    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx,
                       "nta_compute_safe_range_arith_root: cmp_low=%d cmp_high=%d\n",
                       cmp_low, cmp_high);
    }
    
    

    if (rel == ROOT_ATOM_LT) {
      /* x < root_k(p): true if x_high < root_low, false if x_low >= root_high */
      if (cmp_high < 0) {
        result = NTA_TRUE;
      } else if (cmp_low >= 0) {
        result = NTA_FALSE;
      }
    } else if (rel == ROOT_ATOM_LEQ) {
      /* x <= root_k(p): true if x_high <= root_low, false if x_low > root_high */
      if (cmp_high <= 0) {
        result = NTA_TRUE;
      } else if (cmp_low > 0) {
        result = NTA_FALSE;
      }
    } else if (rel == ROOT_ATOM_EQ) {
      /* x == root_k(p): true if they are equal, false if disjoint */
      if (mpfr_cmp(x_low, x_high) == 0 &&
          mpfr_cmp(root_low, root_high) == 0 &&
          mpfr_cmp(x_low, root_low) == 0) {
        result = NTA_TRUE;
      } else if (cmp_high < 0 || cmp_low > 0) {
        result = NTA_FALSE;
      }
    } else if (rel == ROOT_ATOM_GT) {
      /* x > root_k(p): true if x_low > root_high, false if x_high <= root_low */
      if (cmp_low > 0) {
        result = NTA_TRUE;
      } else if (cmp_high <= 0) {
        result = NTA_FALSE;
      }
    } else if (rel == ROOT_ATOM_GEQ) {
      /* x >= root_k(p): true if x_low >= root_high, false if x_high < root_low */
      if (cmp_low >= 0) {
        result = NTA_TRUE;
      } else if (cmp_high < 0) {
        result = NTA_FALSE;
      }
    } else if (rel == ROOT_ATOM_NEQ) {
      /* x != root_k(p): negation of equality */
      if (mpfr_cmp(x_low, x_high) == 0 &&
          mpfr_cmp(root_low, root_high) == 0 &&
          mpfr_cmp(x_low, root_low) == 0) {
        result = NTA_FALSE;
      } else if (cmp_high < 0 || cmp_low > 0) {
        result = NTA_TRUE;
      }
    }
    
    mpfr_clear(x_low);
    mpfr_clear(x_high);
    mpfr_clear(root_low);
    mpfr_clear(root_high);
    arb_clear(x_value_arb);
    arb_clear(root_value_arb);
    nta_value_clear(&x_value);
    mcsat_value_destruct(&root_value);
  } else {
    /* MCSAT path: evaluate the root constraint using libpoly's exact arithmetic */
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      FILE* out = ctx_trace_out(na->ctx);
      ctx_trace_printf(na->ctx, "nta_compute_safe_range_arith_root: x_value=");
      if (x_value.type == NTA_VALUE_MCSAT) {
        mcsat_value_print(&x_value.mcsat_val, out);
      } else {
        ctx_trace_printf(na->ctx, "<arb>");
      }
      ctx_trace_printf(na->ctx, " root_value=");
      mcsat_value_print(&root_value, out);
      ctx_trace_printf(na->ctx, "\n");
    }

    int cmp = mcsat_value_cmp(&x_value.mcsat_val, &root_value);
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx, "nta_compute_safe_range_arith_root: cmp(x_value, root_value)=%d\n", cmp);
    }

    switch (rel) {
      case ROOT_ATOM_LT:
        result = (cmp < 0) ? NTA_TRUE : NTA_FALSE;
        break;
      case ROOT_ATOM_LEQ:
        result = (cmp <= 0) ? NTA_TRUE : NTA_FALSE;
        break;
      case ROOT_ATOM_EQ:
        result = (cmp == 0) ? NTA_TRUE : NTA_FALSE;
        break;
      case ROOT_ATOM_GT:
        result = (cmp > 0) ? NTA_TRUE : NTA_FALSE;
        break;
      case ROOT_ATOM_GEQ:
        result = (cmp >= 0) ? NTA_TRUE : NTA_FALSE;
        break;
      case ROOT_ATOM_NEQ:
        result = (cmp != 0) ? NTA_TRUE : NTA_FALSE;
        break;
      default:
        assert(false);
        result = NTA_TRUE_OR_FALSE;
        break;
    }

    nta_value_clear(&x_value);
    mcsat_value_destruct(&root_value);
  }
  
  return result;
}

/**
 * Compute a safe truth value for a Boolean atom.
 * Supported kinds: ARITH_EQ_ATOM (p == 0), ARITH_GE_ATOM (p >= 0), ARITH_ROOT_ATOM, and their negations.
 * Returns NTA_TRUE, NTA_FALSE, or NTA_TRUE_OR_FALSE.
 */
nta_tristate_t nta_compute_safe_truth_value(na_plugin_t* na, term_t atom,
                                           const mcsat_model_t *model,
                                           const nta_info_t *nta_info,
                                           variable_db_t *var_db,
                                           ivector_t* incomplete_vars,
                                           slong precision) {
  term_manager_t *tm = na->ctx->tm;
  assert(model != NULL && nta_info != NULL && var_db != NULL);

  term_table_t *tbl = term_manager_get_terms(tm);

  bool negative_polarity = is_neg_term(atom);

  term_kind_t kind = term_kind(tbl, atom);

  nta_tristate_t out = NTA_TRUE_OR_FALSE;
  bool handled = false;
  
  /* Handle ARITH_ROOT_ATOM separately */
  if (kind == ARITH_ROOT_ATOM) {
    root_atom_t *root_atom = arith_root_atom_desc(tbl, atom);
    bool trivial_true = false;
    out = nta_compute_safe_range_arith_root(
      na, atom, root_atom, model, nta_info, var_db, incomplete_vars, precision, &trivial_true
    );

    if (trivial_true) {
      out = NTA_TRUE;
    }
    handled = true;
  }

  if (!handled && kind == UNINTERPRETED_TERM && is_boolean_term(tbl, atom)) {
    variable_t var = variable_db_get_variable_if_exists(var_db, atom);
    assert(var != variable_null);
    if (!trail_has_value(na->ctx->trail, var)) {
      assert(false);
      return NTA_TRUE_OR_FALSE;
    }
    const mcsat_value_t *value = trail_get_value(na->ctx->trail, var);
    assert(value->type == VALUE_BOOLEAN);
    out = value->b ? NTA_TRUE : NTA_FALSE;
    handled = true;
  }

  if (!handled && kind == ITE_TERM && is_boolean_term(tbl, atom)) {
    composite_term_t *ite = ite_term_desc(tbl, atom);
    assert(ite->arity == 3);

    term_t cond = ite->arg[0];
    term_t then_term = ite->arg[1];
    term_t else_term = ite->arg[2];

    nta_tristate_t cond_value = nta_compute_safe_truth_value(
      na, cond, model, nta_info, var_db, incomplete_vars, precision
    );

    if (cond_value == NTA_TRUE) {
      out = nta_compute_safe_truth_value(na, then_term, model, nta_info, var_db, incomplete_vars, precision);
    } else if (cond_value == NTA_FALSE) {
      out = nta_compute_safe_truth_value(na, else_term, model, nta_info, var_db, incomplete_vars, precision);
    } else {
      nta_tristate_t then_value = nta_compute_safe_truth_value(
        na, then_term, model, nta_info, var_db, incomplete_vars, precision
      );
      nta_tristate_t else_value = nta_compute_safe_truth_value(
        na, else_term, model, nta_info, var_db, incomplete_vars, precision
      );
      if (then_value == NTA_TRUE && else_value == NTA_TRUE) {
        out = NTA_TRUE;
      } else if (then_value == NTA_FALSE && else_value == NTA_FALSE) {
        out = NTA_FALSE;
      } else {
        out = NTA_TRUE_OR_FALSE;
      }
    }
    handled = true;
  }

  if (!handled && kind == OR_TERM) {
    composite_term_t *or_term = or_term_desc(tbl, atom);
    assert(or_term->arity > 0);

    bool saw_unknown = false;
    for (uint32_t i = 0; i < or_term->arity; i++) {
      term_t arg = or_term->arg[i];
      nta_tristate_t arg_value = nta_compute_safe_truth_value(
        na, arg, model, nta_info, var_db, incomplete_vars, precision
      );
      if (arg_value == NTA_TRUE) {
        out = NTA_TRUE;
        handled = true;
        break;
      }
      if (arg_value == NTA_TRUE_OR_FALSE) {
        saw_unknown = true;
      }
    }

    if (!handled) {
      out = saw_unknown ? NTA_TRUE_OR_FALSE : NTA_FALSE;
      handled = true;
    }
  }

  if (handled) {
    if (negative_polarity) {
      if (out == NTA_TRUE) {
        out = NTA_FALSE;
      } else if (out == NTA_FALSE) {
        out = NTA_TRUE;
      }
    }
    return out;
  }
  
  assert(kind == ARITH_EQ_ATOM || kind == ARITH_GE_ATOM || kind == EQ_TERM || kind == ARITH_BINEQ_ATOM);

  term_t arg = NULL_TERM;
  if (kind == EQ_TERM) {
    composite_term_t *eq = eq_term_desc(tbl, atom);
    assert(eq->arity == 2);
    term_t left = eq->arg[0];
    term_t right = eq->arg[1];
    type_t left_type = term_type(tbl, left);
    type_t right_type = term_type(tbl, right);
    if(!is_arithmetic_type(left_type) || !is_arithmetic_type(right_type)){
      return NTA_TRUE; // not our business, 
    }
    arg = _o_yices_sub(left, right);
  } else if (kind == ARITH_BINEQ_ATOM) {
    composite_term_t *eq = arith_bineq_atom_desc(tbl, atom);
    assert(eq->arity == 2);
    term_t left = eq->arg[0];
    term_t right = eq->arg[1];
    type_t left_type = term_type(tbl, left);
    type_t right_type = term_type(tbl, right);
    bool arith_types = is_arithmetic_type(left_type) && is_arithmetic_type(right_type);
    assert(arith_types);
    if (!arith_types) {
      return NTA_TRUE; // not our business
    }
    arg = _o_yices_sub(left, right);
  } else { // kind == ARITH_EQ_ATOM || kind == ARITH_GE_ATOM 
    arg = arith_atom_arg(tbl, atom);
  }

  nta_value range;
  if (!nta_compute_safe_range(na, arg, model, nta_info, var_db, &range, incomplete_vars, precision)) {
    return NTA_TRUE_OR_FALSE;
  }

  if (range.type == NTA_VALUE_ARB) {
    arb_t range_arb;
    arb_init(range_arb);
    if (!nta_value_to_arb(&range, range_arb, precision)) {
      nta_value_clear(&range);
      arb_clear(range_arb);
      return NTA_TRUE_OR_FALSE;
    }

    /* Extract interval endpoints as MPFR to test signs precisely */
    mpfr_t low, high;
    mpfr_init2(low, (mpfr_prec_t) precision);
    mpfr_init2(high, (mpfr_prec_t) precision);

    /* arb_get_interval_mpfr(low_mpfr, high_mpfr, result_arb) */
    arb_get_interval_mpfr(low, high, range_arb);

    int cmp_low = mpfr_cmp_si(low, 0);
    int cmp_high = mpfr_cmp_si(high, 0);

    if (kind == ARITH_EQ_ATOM || kind == EQ_TERM || kind == ARITH_BINEQ_ATOM) {
      /* EXACT zero */
      if (mpfr_zero_p(low) && mpfr_zero_p(high)) {
        out = NTA_TRUE;
      } else if (cmp_high < 0 || cmp_low > 0) {
        /* range does not include zero */
        out = NTA_FALSE;
      }
    } else if (kind == ARITH_GE_ATOM) {
      if (cmp_low >= 0) {
        /* entirely non-negative */
        out = NTA_TRUE;
      } else if (cmp_high < 0) {
        /* entirely negative */
        out = NTA_FALSE;
      }
    } else {
      assert(false);
      return -1;
    }

    mpfr_clear(low);
    mpfr_clear(high);
    arb_clear(range_arb);
    nta_value_clear(&range);
  } else {
    /* Exact mcsat_value: compare to zero directly */
    int cmp = mcsat_value_cmp_zero(&range.mcsat_val);
    nta_value_clear(&range);

    if (kind == ARITH_EQ_ATOM || kind == EQ_TERM || kind == ARITH_BINEQ_ATOM) {
      out = (cmp == 0) ? NTA_TRUE : NTA_FALSE;
    } else if (kind == ARITH_GE_ATOM) {
      out = (cmp >= 0) ? NTA_TRUE : NTA_FALSE;
    } else {
      assert(false);
      return -1;
    }
  }

  // If the atom is negated, flip the truth values
  if (negative_polarity) {
    if (out == NTA_TRUE) {
      out = NTA_FALSE;
    } else if (out == NTA_FALSE) {
      out = NTA_TRUE;
    }
    // NTA_TRUE_OR_FALSE remains unchanged
  }

  return out;
}

/**
 * Compare val_sin_x with sin(val_x) using rigorous ARB arithmetic.
 * 
 * Uses incrementally more precise computations to determine the comparison result.
 * 
 * @param val_x     The x value
 * @param val_sin_x The value to compare with sin(val_x)
 * 
 * @return Positive if val_sin_x > sin(val_x), negative if val_sin_x < sin(val_x),
 *         0 if val_sin_x == sin(val_x). If comparison cannot be determined precisely,
 *         uses the last computed comparison at highest precision.
 */
static int nta_compare_sin(const mcsat_value_t *val_x, const mcsat_value_t *val_sin_x) {
  assert(val_x != NULL && val_sin_x != NULL);
  
  slong precision = 10;
  const slong max_precision = 10000;
  int last_cmp = 0;  // Last comparison result
  
  while (precision <= max_precision) {
    /* Convert val_x to ARB and compute sin(val_x) */
    arb_t val_x_arb, val_sin_x_arb, sin_val_x_arb;
    arb_init(val_x_arb);
    arb_init(sin_val_x_arb);
    arb_init(val_sin_x_arb);
    
    if (!mcsat_value_to_arb(val_x, val_x_arb, precision)) {
      arb_clear(val_x_arb);
      arb_clear(sin_val_x_arb);
      arb_clear(val_sin_x_arb);
      assert(false);  // Unable to compare
    }
    
    if (!mcsat_value_to_arb(val_sin_x, val_sin_x_arb, precision)) {
      arb_clear(val_x_arb);
      arb_clear(sin_val_x_arb);
      arb_clear(val_sin_x_arb);
      assert(false);  // Unable to compare
    }
    
    /* Compute sin(x) with current precision */
    arb_sin(sin_val_x_arb, val_x_arb, precision);
    
    /* Compare val_sin_x with sin(val_x) */
    mpfr_t sin_val_x_low, sin_val_x_high, val_sin_x_low, val_sin_x_high;
    mpfr_init2(sin_val_x_low, (mpfr_prec_t) precision);
    mpfr_init2(sin_val_x_high, (mpfr_prec_t) precision);
    mpfr_init2(val_sin_x_low, (mpfr_prec_t) precision);
    mpfr_init2(val_sin_x_high, (mpfr_prec_t) precision);
    
    arb_get_interval_mpfr(sin_val_x_low, sin_val_x_high, sin_val_x_arb);
    arb_get_interval_mpfr(val_sin_x_low, val_sin_x_high, val_sin_x_arb);
    
    /* Check if intervals are disjoint */
    int cmp_val_sin_x_high_vs_sin_x_low = mpfr_cmp(val_sin_x_high, sin_val_x_low);
    int cmp_val_sin_x_low_vs_sin_x_high = mpfr_cmp(val_sin_x_low, sin_val_x_high);
    
    if (cmp_val_sin_x_high_vs_sin_x_low < 0) {
      /* val_sin_x entirely below sin(x) */
      last_cmp = -1;
      mpfr_clear(sin_val_x_low);
      mpfr_clear(sin_val_x_high);
      mpfr_clear(val_sin_x_low);
      mpfr_clear(val_sin_x_high);
      arb_clear(val_x_arb);
      arb_clear(sin_val_x_arb);
      arb_clear(val_sin_x_arb);
      break;
    } else if (cmp_val_sin_x_low_vs_sin_x_high > 0) {
      /* val_sin_x entirely above sin(x) */
      last_cmp = 1;
      mpfr_clear(sin_val_x_low);
      mpfr_clear(sin_val_x_high);
      mpfr_clear(val_sin_x_low);
      mpfr_clear(val_sin_x_high);
      arb_clear(val_x_arb);
      arb_clear(sin_val_x_arb);
      arb_clear(val_sin_x_arb);
      break;
    } else if (mpfr_cmp(val_sin_x_low, val_sin_x_high) == 0 &&
               mpfr_cmp(sin_val_x_low, sin_val_x_high) == 0 &&
               mpfr_cmp(val_sin_x_low, sin_val_x_low) == 0) {
      /* Intervals are equal singletons */
      last_cmp = 0;
      mpfr_clear(sin_val_x_low);
      mpfr_clear(sin_val_x_high);
      mpfr_clear(val_sin_x_low);
      mpfr_clear(val_sin_x_high);
      arb_clear(val_x_arb);
      arb_clear(sin_val_x_arb);
      arb_clear(val_sin_x_arb);
      break;
    }
    
    mpfr_clear(sin_val_x_low);
    mpfr_clear(sin_val_x_high);
    mpfr_clear(val_sin_x_low);
    mpfr_clear(val_sin_x_high);
    arb_clear(val_x_arb);
    arb_clear(sin_val_x_arb);
    arb_clear(val_sin_x_arb);
    
    /* If not determined, increase precision */
    precision += 5;
  }
  
  return last_cmp;
}

/**
 * Compare val_exp_x with exp(val_x) using rigorous ARB arithmetic.
 *
 * @return Positive if val_exp_x > exp(val_x), negative if val_exp_x < exp(val_x),
 *         0 if val_exp_x == exp(val_x).
 */
static int nta_compare_exp(const mcsat_value_t *val_x, const mcsat_value_t *val_exp_x) {
  assert(val_x != NULL && val_exp_x != NULL);

  slong precision = 10;
  const slong max_precision = 10000;
  int last_cmp = 0;

  while (precision <= max_precision) {
    arb_t val_x_arb, val_exp_x_arb, exp_val_x_arb;
    arb_init(val_x_arb);
    arb_init(exp_val_x_arb);
    arb_init(val_exp_x_arb);

    if (!mcsat_value_to_arb(val_x, val_x_arb, precision)) {
      arb_clear(val_x_arb);
      arb_clear(exp_val_x_arb);
      arb_clear(val_exp_x_arb);
      assert(false);
    }

    if (!mcsat_value_to_arb(val_exp_x, val_exp_x_arb, precision)) {
      arb_clear(val_x_arb);
      arb_clear(exp_val_x_arb);
      arb_clear(val_exp_x_arb);
      assert(false);
    }

    arb_exp(exp_val_x_arb, val_x_arb, precision);

    mpfr_t exp_val_x_low, exp_val_x_high, val_exp_x_low, val_exp_x_high;
    mpfr_init2(exp_val_x_low, (mpfr_prec_t) precision);
    mpfr_init2(exp_val_x_high, (mpfr_prec_t) precision);
    mpfr_init2(val_exp_x_low, (mpfr_prec_t) precision);
    mpfr_init2(val_exp_x_high, (mpfr_prec_t) precision);

    arb_get_interval_mpfr(exp_val_x_low, exp_val_x_high, exp_val_x_arb);
    arb_get_interval_mpfr(val_exp_x_low, val_exp_x_high, val_exp_x_arb);

    int cmp_val_exp_x_high_vs_exp_x_low = mpfr_cmp(val_exp_x_high, exp_val_x_low);
    int cmp_val_exp_x_low_vs_exp_x_high = mpfr_cmp(val_exp_x_low, exp_val_x_high);

    if (cmp_val_exp_x_high_vs_exp_x_low < 0) {
      last_cmp = -1;
      mpfr_clear(exp_val_x_low);
      mpfr_clear(exp_val_x_high);
      mpfr_clear(val_exp_x_low);
      mpfr_clear(val_exp_x_high);
      arb_clear(val_x_arb);
      arb_clear(exp_val_x_arb);
      arb_clear(val_exp_x_arb);
      break;
    } else if (cmp_val_exp_x_low_vs_exp_x_high > 0) {
      last_cmp = 1;
      mpfr_clear(exp_val_x_low);
      mpfr_clear(exp_val_x_high);
      mpfr_clear(val_exp_x_low);
      mpfr_clear(val_exp_x_high);
      arb_clear(val_x_arb);
      arb_clear(exp_val_x_arb);
      arb_clear(val_exp_x_arb);
      break;
    } else if (mpfr_cmp(val_exp_x_low, val_exp_x_high) == 0 &&
               mpfr_cmp(exp_val_x_low, exp_val_x_high) == 0 &&
               mpfr_cmp(val_exp_x_low, exp_val_x_low) == 0) {
      last_cmp = 0;
      mpfr_clear(exp_val_x_low);
      mpfr_clear(exp_val_x_high);
      mpfr_clear(val_exp_x_low);
      mpfr_clear(val_exp_x_high);
      arb_clear(val_x_arb);
      arb_clear(exp_val_x_arb);
      arb_clear(val_exp_x_arb);
      break;
    }

    mpfr_clear(exp_val_x_low);
    mpfr_clear(exp_val_x_high);
    mpfr_clear(val_exp_x_low);
    mpfr_clear(val_exp_x_high);
    arb_clear(val_x_arb);
    arb_clear(exp_val_x_arb);
    arb_clear(val_exp_x_arb);

    precision += 5;
  }

  return last_cmp;
}

static double nta_exp_distance(const mcsat_value_t *val_x, const mcsat_value_t *val_exp_x) {
  slong prec = 128;
  arb_t x_arb, exp_x_arb, exp_val_x_arb;
  arb_init(x_arb);
  arb_init(exp_x_arb);
  arb_init(exp_val_x_arb);

  if (!mcsat_value_to_arb(val_x, x_arb, prec) ||
      !mcsat_value_to_arb(val_exp_x, exp_x_arb, prec)) {
    arb_clear(x_arb);
    arb_clear(exp_x_arb);
    arb_clear(exp_val_x_arb);
    return 0.0;
  }

  arb_exp(exp_val_x_arb, x_arb, prec);
  arb_sub(exp_val_x_arb, exp_val_x_arb, exp_x_arb, prec);
  arb_abs(exp_val_x_arb, exp_val_x_arb);

  mpfr_t mid;
  mpfr_init2(mid, (mpfr_prec_t) prec);
  arf_get_mpfr(mid, arb_midref(exp_val_x_arb), MPFR_RNDN);
  double d = mpfr_get_d(mid, MPFR_RNDN);

  mpfr_clear(mid);
  arb_clear(x_arb);
  arb_clear(exp_x_arb);
  arb_clear(exp_val_x_arb);
  return d;
}

static term_t nta_term_from_mpfr(term_manager_t* tm, const mpfr_t v) {
  rational_t q;
  mpq_t mpq;
  q_init(&q);
  mpq_init(mpq);
  mpfr_get_q(mpq, v);
  q_set_mpq(&q, mpq);
  term_t result = mk_arith_constant(tm, &q);
  mpq_clear(mpq);
  q_clear(&q);
  return result;
}

// static void nta_mcsat_value_from_mpfr(term_manager_t* tm, const mpfr_t v, mcsat_value_t* out) {
//   term_t term = nta_term_from_mpfr(tm, v);
//   mcsat_value_construct_from_constant_term(out, term_manager_get_terms(tm), term);
// }

static void nta_build_pade_exp_terms(term_t x, term_t c_term, int n, term_t* n_term, term_t* d_term) {
  assert(n_term != NULL && d_term != NULL);
  term_t delta = _o_yices_sub(x, c_term);

  if (n == 1) {
    term_t two = _o_yices_int32(2);
    *n_term = _o_yices_add(two, delta);
    *d_term = _o_yices_sub(two, delta);
    return;
  }

  if (n == 2) {
    term_t six = _o_yices_int32(6);
    term_t three = _o_yices_int32(3);
    term_t half = _o_yices_rational32(1, 2);
    term_t delta_sq = _o_yices_mul(delta, delta);
    term_t three_delta = _o_yices_mul(three, delta);
    term_t half_delta_sq = _o_yices_mul(half, delta_sq);

    *n_term = _o_yices_add(six, _o_yices_add(three_delta, half_delta_sq));
    //*d_term = _o_yices_add(six, _o_yices_add(_o_yices_neg(three_delta), half_delta_sq));
    *d_term = _o_yices_add(six, _o_yices_sub( half_delta_sq, three_delta));
    return;
  }

  assert(false);
}

term_t compute_taylor_approximation_of_exp(na_plugin_t *na, term_manager_t *tm, term_t t, const mcsat_value_t *center, int degree) {
  assert(na != NULL && tm != NULL);
  assert(center != NULL);
  if (degree < 0) {
    return NULL_TERM;
  }

  term_t one_term = _o_yices_rational32(1, 1);
  term_t exp_c_term = NULL_TERM;

  term_t center_term = mcsat_value_to_term(center, tm);
  if (center_term == NULL_TERM) {
    return NULL_TERM;
  }

  if (mcsat_value_is_zero(center)) {
    exp_c_term = one_term;
  } else {
    slong prec = 20;
    arb_t c_arb, exp_arb;
    arb_init(c_arb);
    arb_init(exp_arb);
    if (!mcsat_value_to_arb(center, c_arb, prec)) {
      arb_clear(c_arb);
      arb_clear(exp_arb);
      return NULL_TERM;
    }
    arb_exp(exp_arb, c_arb, prec);

    mpfr_t exp_low, exp_high;
    mpfr_init2(exp_low, (mpfr_prec_t) prec);
    mpfr_init2(exp_high, (mpfr_prec_t) prec);
    arb_get_interval_mpfr(exp_low, exp_high, exp_arb);
    exp_c_term = nta_term_from_mpfr(tm, exp_low);

    mpfr_clear(exp_low);
    mpfr_clear(exp_high);
    arb_clear(c_arb);
    arb_clear(exp_arb);
  }

  term_t delta = _o_yices_sub(t, center_term);
  term_t sum = exp_c_term;
  term_t delta_pow = delta;
  int32_t factorial = 1;

  for (int d = 1; d <= degree; d++) {
    factorial *= d;
    term_t coeff = _o_yices_mul(exp_c_term, _o_yices_rational32(1, factorial));
    term_t term_d = _o_yices_mul(coeff, delta_pow);
    sum = _o_yices_add(sum, term_d);
    if (d < degree) {
      delta_pow = _o_yices_mul(delta_pow, delta);
    }
  }

  return sum;
}

bool refine_approximation_of_exp_with_pade(na_plugin_t *na, term_manager_t *tm, term_t x, term_t exp_x,
                                           const mcsat_value_t *val_x, bool want_upper,
                                           term_t lemmas_out[2], term_t main_literals_out[2]) {
  assert(na != NULL && tm != NULL);
  assert(x != NULL_TERM && exp_x != NULL_TERM);
  assert(val_x != NULL);
  assert(lemmas_out != NULL);
  assert(main_literals_out != NULL);

  if (!mcsat_value_is_zero(val_x)) {
    exit(1);
  }

  for (int i = 0; i < 2; i++) {
    lemmas_out[i] = NULL_TERM;
    main_literals_out[i] = NULL_TERM;
  }

  term_t c_term = mcsat_value_to_term(val_x, tm);
  if (c_term == NULL_TERM) {
    return false;
  }

  slong prec = 200;
  arb_t x_arb, exp_arb;
  arb_init(x_arb);
  arb_init(exp_arb);
  if (!mcsat_value_to_arb(val_x, x_arb, prec)) {
    arb_clear(x_arb);
    arb_clear(exp_arb);
    return false;
  }
  arb_exp(exp_arb, x_arb, prec);

  mpfr_t exp_low, exp_high;
  mpfr_init2(exp_low, (mpfr_prec_t) prec);
  mpfr_init2(exp_high, (mpfr_prec_t) prec);
  arb_get_interval_mpfr(exp_low, exp_high, exp_arb);

  term_t exp_c_low = nta_term_from_mpfr(tm, exp_low);
  term_t exp_c_high = nta_term_from_mpfr(tm, exp_high);
  // trace exp_c_low and exp_c_high
  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    ctx_trace_printf(na->ctx, "refine_approximation_of_exp_with_pade: exp_c_low=");
    ctx_trace_term(na->ctx, exp_c_low);
    ctx_trace_printf(na->ctx, "refine_approximation_of_exp_with_pade: exp_c_high=");
    ctx_trace_term(na->ctx, exp_c_high);
  }

  mpfr_clear(exp_low);
  mpfr_clear(exp_high);
  arb_clear(x_arb);
  arb_clear(exp_arb);

  term_t n1_term = NULL_TERM;
  term_t d1_term = NULL_TERM;
  term_t n2_term = NULL_TERM;
  term_t d2_term = NULL_TERM;
  nta_build_pade_exp_terms(x, c_term, 1, &n1_term, &d1_term);
  nta_build_pade_exp_terms(x, c_term, 2, &n2_term, &d2_term);

  // trace pade terms n2_term and d2_term
  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    // print c_term
    ctx_trace_printf(na->ctx, "pade: c_term=");
    ctx_trace_term(na->ctx, c_term);
    ctx_trace_printf(na->ctx, "pade: n1_term=");
    ctx_trace_term(na->ctx, n1_term);
    ctx_trace_printf(na->ctx, "pade: d1_term=");
    ctx_trace_term(na->ctx, d1_term);
    ctx_trace_printf(na->ctx, "pade: n2_term=");
    ctx_trace_term(na->ctx, n2_term);
    ctx_trace_printf(na->ctx, "pade: d2_term=");
    ctx_trace_term(na->ctx, d2_term);
  }

  term_t lhs1 = _o_yices_mul(exp_x, d1_term);
  term_t rhs1_upper = _o_yices_mul(exp_c_high, n1_term);
  term_t rhs1_lower = _o_yices_mul(exp_c_low, n1_term);

  term_t lhs2 = _o_yices_mul(exp_x, d2_term);
  term_t rhs2_upper = _o_yices_mul(exp_c_high, n2_term);
  term_t rhs2_lower = _o_yices_mul(exp_c_low, n2_term);

  term_t c_plus_two = _o_yices_add(c_term, _o_yices_int32(2));
  term_t guard_right_terms[2] = {
    _o_yices_arith_geq_atom(x, c_term),
    _o_yices_arith_lt_atom(x, c_plus_two)
  };
  term_t guard_right = _o_yices_and(2, guard_right_terms);
  term_t guard_left = _o_yices_arith_leq_atom(x, c_term);
  term_t guard_right_geq = _o_yices_arith_geq_atom(x, c_term);

  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    ctx_trace_printf(na->ctx, "refine_approximation_of_exp_with_pade: want_upper=%s\n", want_upper ? "true" : "false");
  }

  if (want_upper) {
    term_t upper1 = _o_yices_arith_leq_atom(lhs1, rhs1_upper);
    term_t upper2 = _o_yices_arith_leq_atom(lhs2, rhs2_upper);

    // Upper bounds: right side for n=1, left side for n=2.
    lemmas_out[0] = _o_yices_implies(guard_right, upper1);
    lemmas_out[1] = _o_yices_implies(guard_left, upper2);

    main_literals_out[0] = upper1;
    main_literals_out[1] = upper2;
  } else {
    term_t lower1 = _o_yices_arith_geq_atom(lhs1, rhs1_lower);
    term_t lower2 = _o_yices_arith_geq_atom(lhs2, rhs2_lower);

    // Lower bounds: left side for n=1, right side for n=2.
    lemmas_out[0] = _o_yices_implies(guard_left, lower1);
    lemmas_out[1] = _o_yices_implies(guard_right_geq, lower2);

    main_literals_out[0] = lower1;
    main_literals_out[1] = lower2;
  }

  return true;
}

bool refine_approximation_of_exp_with_taylor(na_plugin_t *na, term_manager_t *tm, term_t x, term_t exp_x,
                                             const mcsat_value_t *val_x, bool want_upper,
                                             term_t *lemma_out) {
  assert(na != NULL && tm != NULL);
  assert(x != NULL_TERM && exp_x != NULL_TERM);
  assert(val_x != NULL);
  assert(lemma_out != NULL);

  *lemma_out = NULL_TERM;
  if (want_upper) {
    return false;
  }

  term_t poly = compute_taylor_approximation_of_exp(na, tm, x, val_x, 3);
  if (poly == NULL_TERM) {
    return false;
  }

  *lemma_out = _o_yices_arith_geq_atom(exp_x, poly);
  return true;
}

bool refine_approximation_of_exp_linear(na_plugin_t *na, term_manager_t *tm, term_t x, term_t exp_x,
                                        const mcsat_value_t *val_x, const mcsat_value_t *val_exp_x,
                                        bool want_upper, term_t *lemma_out, term_t *main_literal_out) {
  assert(na != NULL && tm != NULL);
  assert(x != NULL_TERM && exp_x != NULL_TERM);
  assert(val_x != NULL && val_exp_x != NULL);
  assert(lemma_out != NULL && main_literal_out != NULL);

  *lemma_out = NULL_TERM;
  *main_literal_out = NULL_TERM;
  if (!want_upper) {
    return false;
  }

  term_t c_term = mcsat_value_to_term(val_x, tm);
  term_t d_term = mcsat_value_to_term(val_exp_x, tm);
  if (c_term == NULL_TERM || d_term == NULL_TERM) {
    return false;
  }

  slong prec = 20;
  const slong max_prec = 2000;
  arb_t c_arb, d_arb, exp_c_arb;
  arb_init(c_arb);
  arb_init(d_arb);
  arb_init(exp_c_arb);

  bool found_exp_lower = false;
  while (prec <= max_prec) {
    if (!mcsat_value_to_arb(val_x, c_arb, prec) || !mcsat_value_to_arb(val_exp_x, d_arb, prec)) {
      break;
    }
    arb_exp(exp_c_arb, c_arb, prec);

    if (arb_gt(d_arb, exp_c_arb)) {
      found_exp_lower = true;
      break;
    }

    prec += 10;
  }

  if (!found_exp_lower) {
    arb_clear(c_arb);
    arb_clear(d_arb);
    arb_clear(exp_c_arb);
    return false;
  }

  mpfr_t exp_c_low_mpfr;
  mpfr_init2(exp_c_low_mpfr, (mpfr_prec_t) prec);
  mpfr_t exp_c_high_mpfr;
  mpfr_init2(exp_c_high_mpfr, (mpfr_prec_t) prec);
  arb_get_interval_mpfr(exp_c_low_mpfr, exp_c_high_mpfr, exp_c_arb);
  term_t exp_c_term = nta_term_from_mpfr(tm, exp_c_low_mpfr);

  term_t one_term = _o_yices_rational32(1, 1);
  term_t half_term = _o_yices_rational32(1, 2);
  term_t tangent = _o_yices_mul(exp_c_term, _o_yices_add(one_term, _o_yices_sub(x, c_term)));
  term_t offset = _o_yices_mul(_o_yices_sub(exp_c_term, d_term), half_term);
  term_t line = _o_yices_sub(tangent, offset);

  arb_t offset_arb, line_arb, exp_x_arb, x_arb, eps_arb, delta_arb, tmp_arb;
  arb_init(offset_arb);
  arb_init(line_arb);
  arb_init(exp_x_arb);
  arb_init(x_arb);
  arb_init(eps_arb);
  arb_init(delta_arb);
  arb_init(tmp_arb);

  arb_sub(offset_arb, exp_c_arb, d_arb, prec);
  arb_mul_2exp_si(offset_arb, offset_arb, -1);

  term_t left_bound = NULL_TERM;
  term_t right_bound = NULL_TERM;

  arb_set_si(eps_arb, 1);
  for (int iter = 0; iter < 100; iter++) {
    arb_add(x_arb, c_arb, eps_arb, prec);
    arb_sub(delta_arb, x_arb, c_arb, prec);
    arb_add_si(tmp_arb, delta_arb, 1, prec);
    arb_mul(line_arb, exp_c_arb, tmp_arb, prec);
    arb_sub(line_arb, line_arb, offset_arb, prec);
    arb_exp(exp_x_arb, x_arb, prec);

    if (arb_gt(line_arb, exp_x_arb)) {
      mpfr_t eps_mpfr;
      mpfr_init2(eps_mpfr, (mpfr_prec_t) prec);
      arf_get_mpfr(eps_mpfr, arb_midref(eps_arb), MPFR_RNDN);
      term_t eps_term = nta_term_from_mpfr(tm, eps_mpfr);
      right_bound = _o_yices_add(c_term, eps_term);
      mpfr_clear(eps_mpfr);
      break;
    }

    arb_mul_2exp_si(eps_arb, eps_arb, -1);
  }

  arb_set_si(eps_arb, 1);
  for (int iter = 0; iter < 60; iter++) {
    arb_sub(x_arb, c_arb, eps_arb, prec);
    arb_sub(delta_arb, x_arb, c_arb, prec);
    arb_add_si(tmp_arb, delta_arb, 1, prec);
    arb_mul(line_arb, exp_c_arb, tmp_arb, prec);
    arb_sub(line_arb, line_arb, offset_arb, prec);
    arb_exp(exp_x_arb, x_arb, prec);

    if (arb_gt(line_arb, exp_x_arb)) {
      mpfr_t eps_mpfr;
      mpfr_init2(eps_mpfr, (mpfr_prec_t) prec);
      arf_get_mpfr(eps_mpfr, arb_midref(eps_arb), MPFR_RNDN);
      term_t eps_term = nta_term_from_mpfr(tm, eps_mpfr);
      left_bound = _o_yices_sub(c_term, eps_term);
      mpfr_clear(eps_mpfr);
      break;
    }

    arb_mul_2exp_si(eps_arb, eps_arb, -1);
  }

  mpfr_clear(exp_c_low_mpfr);
  mpfr_clear(exp_c_high_mpfr);
  arb_clear(c_arb);
  arb_clear(d_arb);
  arb_clear(exp_c_arb);
  arb_clear(offset_arb);
  arb_clear(line_arb);
  arb_clear(exp_x_arb);
  arb_clear(x_arb);
  arb_clear(eps_arb);
  arb_clear(delta_arb);
  arb_clear(tmp_arb);

  if (left_bound == NULL_TERM || right_bound == NULL_TERM) {
    return false;
  }

  term_t left_guard = _o_yices_arith_lt_atom(left_bound, x);
  term_t right_guard = _o_yices_arith_lt_atom(x, right_bound);
  term_t guards[2] = { left_guard, right_guard };
  term_t guard = _o_yices_and(2, guards);

  *main_literal_out = _o_yices_arith_lt_atom(exp_x, line);
  *lemma_out = _o_yices_implies(guard, *main_literal_out);
  return true;
}

/**
 * Find the closest Taylor center among 0, pi/2, pi, and 3*pi/2 to val_x (modulo 2*pi).
 * 
 * @param val_x    The value to find the closest center for
 * @param nta_info The nta_info structure (contains pi)
 * 
 * @return The closest taylor_center_kind_t among TAYLOR_CENTER_ZERO, 
 *         TAYLOR_CENTER_PI_2, TAYLOR_CENTER_PI, TAYLOR_CENTER_PI_3_2
 */
static taylor_center_kind_t find_closest_taylor_center(const mcsat_value_t *val_x) {
  /* Convert val_x to double */
  double x = mcsat_value_to_double(val_x);
  assert(!isnan(x));
    
  /* Reduce x modulo 2*pi */
  // TODO_NTA: should we use value of pi instead?
  double two_pi = 2.0 * M_PI;
  double x_mod = fmod(x, two_pi);
  if (x_mod < 0.0) {
    x_mod += two_pi;
  }

  bool disable_0 = false;
  bool disable_pi = true;
  bool disable_2pi = false;
  
  /* Compute distances to 0, pi/2, pi, 3*pi/2, 2pi */
  double dist_to_zero = fabs(x_mod - 0); 
  double dist_to_pi_2 = fabs(x_mod - M_PI / 2.0);
  double dist_to_pi = fabs(x_mod - M_PI);
  double dist_to_pi_3_2 = fabs(x_mod - 3.0 * M_PI / 2.0);
  double dist_to_2pi = fabs(x_mod - 2.0 * M_PI);
  
  if(disable_0) {
    dist_to_zero = INFINITY;
  }
  if(disable_pi) {
    dist_to_pi = INFINITY;
  }
  if(disable_2pi) {
    dist_to_2pi = INFINITY;
  }

  /* Find the minimum distance */
  if (
      dist_to_zero <= dist_to_pi_2 
      && dist_to_zero <= dist_to_pi 
      && dist_to_zero <= dist_to_pi_3_2 
      && dist_to_zero <= dist_to_2pi) {
    return TAYLOR_CENTER_ZERO;
  } else if (
      dist_to_pi_2 <= dist_to_zero 
      && dist_to_pi_2 <= dist_to_pi 
      && dist_to_pi_2 <= dist_to_pi_3_2 
      && dist_to_pi_2 <= dist_to_2pi) {
    return TAYLOR_CENTER_PI_2;
  } else if (
      dist_to_pi <= dist_to_zero 
      && dist_to_pi <= dist_to_pi_2 
      && dist_to_pi <= dist_to_pi_3_2 
      && dist_to_pi <= dist_to_2pi) {
    return TAYLOR_CENTER_PI;
  } else if (
      dist_to_pi_3_2 <= dist_to_zero 
      && dist_to_pi_3_2 <= dist_to_pi_2 
      && dist_to_pi_3_2 <= dist_to_pi 
      && dist_to_pi_3_2 <= dist_to_2pi) {
    return TAYLOR_CENTER_PI_3_2;
  }
  else {
    return TAYLOR_CENTER_2_PI;
  }
}

/**
 * Refine Taylor approximation of sine based on comparison with val_sin_x.
 * 
 * Finds a Taylor polynomial approximation of sin(x) around the closest center
 * (0, pi/2, pi, or 3*pi/2) such that the polynomial value at val_x properly bounds
 * val_sin_x relative to sin(val_x).
 * 
 * If val_sin_x > sin(val_x): finds an upper bound polynomial
 * If val_sin_x < sin(val_x): finds a lower bound polynomial
 * 
 * @param tm        The term manager
 * @param x         The variable term representing the argument to sine
 * @param sin_x     The variable term representing sin(x)
 * @param val_x     The mcsat value of x
 * @param val_sin_x The mcsat value of sin_x
 * @param nta_info  The nta_info structure
 * @param var_db    The variable database
 * 
 * @return A term_t representing the refined Taylor polynomial approximation,
 *         or NULL_TERM if refinement fails or if val_x == sin(val_x)
 */
term_t refine_taylor_approximation_of_sin(na_plugin_t *na, term_manager_t *tm, term_t x, term_t sin_x,
                                          const mcsat_value_t *val_x, const mcsat_value_t *val_sin_x,
                                          term_t arg_term_override,
                                          term_t* conflict_literal_out,
                                          nta_info_t *nta_info, variable_db_t *var_db,
                                          lp_data_t *lp_data, evaluator_t *eval, value_table_t *vtbl) {
  assert(tm != NULL && x != NULL_TERM && sin_x != NULL_TERM);
  assert(val_x != NULL && val_sin_x != NULL && nta_info != NULL && var_db != NULL);
  assert(eval != NULL && vtbl != NULL);
  if (conflict_literal_out != NULL) {
    *conflict_literal_out = NULL_TERM;
  }
  
  /* Step 1: Compare val_sin_x with sin(val_x) */
  int cmp = nta_compare_sin(val_x, val_sin_x);
  
  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    FILE* out = ctx_trace_out(na->ctx);
    ctx_trace_printf(na->ctx, "refine_taylor_approximation_of_sin: val_x=");
    mcsat_value_print(val_x, out);
    ctx_trace_printf(na->ctx, ", val_sin_x=");
    mcsat_value_print(val_sin_x, out);
    ctx_trace_printf(na->ctx, ", cmp=%d\n", cmp);
  }
  
  /* Assert that they are not equal (otherwise, no need to call refine) */
  assert(cmp != 0);
  
  
  
  /* Adjust argument to x - 2*pi*period if period is enabled */
  term_t pi_term = nta_info_get_pi(nta_info);
  assert(pi_term != NULL_TERM);
  term_t arg_term = arg_term_override != NULL_TERM ? arg_term_override : x;
  if (arg_term_override == NULL_TERM && nta_info->use_period_for_sin) {
    term_t period_term = nta_info_get_sin_period_term(nta_info, x);
    assert(period_term != NULL_TERM);
    term_t two_pi = _o_yices_mul(_o_yices_rational32(2, 1), pi_term);
    term_t two_pi_period = _o_yices_mul(two_pi, period_term);
    arg_term = _o_yices_sub(x, two_pi_period);
  }
  

  /* Step 2: Find closest Taylor center */
  taylor_center_kind_t center = find_closest_taylor_center(val_x);

  nta_taylor_polarity_kind_t polarity = cmp > 0 ? NTA_TAYLOR_POLARITY_UPPER : NTA_TAYLOR_POLARITY_LOWER;
  int start_degree = next_taylor_degree_for_sin(nta_info, arg_term, center, polarity);

  if (ctx_trace_enabled(na->ctx, "na::nta")) {
    FILE* out = ctx_trace_out(na->ctx);
    ctx_trace_printf(na->ctx,
                     "refine_taylor_approximation_of_sin: center=%d polarity=%d start_degree=%d val_x=",
                     (int) center, (int) polarity, start_degree);
    mcsat_value_print(val_x, out);
    ctx_trace_printf(na->ctx, " val_sin_x=");
    mcsat_value_print(val_sin_x, out);
    ctx_trace_printf(na->ctx, "\n");
  }

  const int max_increment = 80;  // Maximum degrees increment to attempt 

  term_t result = NULL_TERM;
  
  for (int degree = start_degree; degree <= start_degree + max_increment;
        degree = next_taylor_degree_for_sin(nta_info, arg_term, center, polarity)) {
    /* Compute Taylor approximation of given degree */
    term_t poly_term = compute_taylor_approximation_of_sin(na, tm, nta_info, arg_term, center, degree);
    assert(poly_term != NULL_TERM);
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx, "refine_taylor_approximation_of_sin: poly_term=");
      ctx_trace_term(na->ctx, poly_term);
    }
    
    /* Evaluate polynomial using Yices model evaluation with trail assignments */
    value_t poly_value = eval_in_model(eval, poly_term);
    if (!good_object(vtbl, poly_value)) {
      if (ctx_trace_enabled(na->ctx, "na::nta")) {
        ctx_trace_printf(na->ctx, "refine_taylor_approximation_of_sin: eval failed/unknown for poly_term\n");
      }
      //assert(false);
      continue;
    }
    
    mcsat_value_t poly_val;
    mcsat_value_construct_from_value(&poly_val, vtbl, poly_value);
    
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      FILE* out = ctx_trace_out(na->ctx);
      ctx_trace_printf(na->ctx, "eval model returned ");
      if (good_object(vtbl, poly_value)) {
        if (poly_val.type == VALUE_RATIONAL || poly_val.type == VALUE_LIBPOLY) {
          double approx = mcsat_value_to_double(&poly_val);
          ctx_trace_printf(na->ctx, "%.17g", approx);
        } else {
          mcsat_value_print(&poly_val, out);
        }
      } else {
        ctx_trace_printf(na->ctx, "<invalid>");
      }
      ctx_trace_printf(na->ctx, "\n");
    }
    
    /* Check separation condition based on polarity:
     * Upper bound: poly_val < val_sin_x (poly_term - val_sin_x < 0)
     * Lower bound: poly_val > val_sin_x (poly_term - val_sin_x > 0)
     */
    term_t rhs_term = mcsat_value_to_term(val_sin_x, tm);
    assert(rhs_term != NULL_TERM);
    
    term_t diff = _o_yices_sub(poly_term, rhs_term);
    value_t diff_value = eval_in_model(eval, diff);
    
    assert(good_object(vtbl, diff_value));
    if (!good_object(vtbl, diff_value)) {
      /* Could not evaluate diff, continue */
      mcsat_value_destruct(&poly_val);
    }
    
    mcsat_value_t diff_val;
    mcsat_value_construct_from_value(&diff_val, vtbl, diff_value);
    
    // assert diff_val is not zero
    //assert(!mcsat_value_is_zero(&diff_val)); 

    /* Check sign of diff based on polarity */
    double diff_double = mcsat_value_to_double(&diff_val);
    bool holds = (polarity == NTA_TAYLOR_POLARITY_UPPER) ? (diff_double < 0) : (diff_double > 0);
    mcsat_value_destruct(&diff_val);
    // print diff_double
    if (ctx_trace_enabled(na->ctx, "na::nta")) {
      ctx_trace_printf(na->ctx, "refine_taylor_approximation_of_sin: diff_double=%.17g holds=%d\n", diff_double, (int) holds);
    }

    
    if (!holds) {
      /* value of poly_term >= val_sin_x (resp. <=), continue */
      mcsat_value_destruct(&poly_val);
      continue;
    }
    
    // This should be enforced by the way we choose upper/lower bounds
    /* Check if poly_val properly bounds sin(val_x) using safe comparison:
     * Upper bound: poly_val > sin(val_x)
     * Lower bound: poly_val < sin(val_x)
     */
    // int cmp_poly_vs_sin = nta_compare_sin(val_x, &poly_val);
    // mcsat_value_destruct(&poly_val);
    
    // bool valid_bound = (polarity == NTA_TAYLOR_POLARITY_UPPER) ? (cmp_poly_vs_sin > 0) : (cmp_poly_vs_sin < 0);
    
    // // print cmp_poly_vs_sin and valid_bound
    // if (ctx_trace_enabled(na->ctx, "na::nta")) {
    //   FILE* out = ctx_trace_out(na->ctx);
    //   ctx_trace_printf(na->ctx, "refine_taylor_approximation_of_sin: cmp_poly_vs_sin=%d valid_bound=%d\n", cmp_poly_vs_sin, (int) valid_bound);
    // }

    // if (valid_bound) {
      /* Found valid bound, return appropriate constraint:
       * Upper bound: poly_term >= sin_x
       * Lower bound: sin_x >= poly_term
       */

      term_t refinement_literal = (polarity == NTA_TAYLOR_POLARITY_UPPER)
        ? _o_yices_arith_geq_atom(poly_term, sin_x)
        : _o_yices_arith_geq_atom(sin_x, poly_term);

      if (conflict_literal_out != NULL) {
        *conflict_literal_out = refinement_literal;
      }

      term_t refinement = refinement_literal;

      if (center == TAYLOR_CENTER_ZERO || center == TAYLOR_CENTER_2_PI) {
        if (arg_term_override != NULL_TERM || nta_info->use_period_for_sin) {
          term_t two_pi_k = _o_yices_sub(x, arg_term);
          term_t guard = (center == TAYLOR_CENTER_ZERO)
            ? _o_yices_arith_geq_atom(x, two_pi_k)
            : _o_yices_arith_leq_atom(x, two_pi_k);
          refinement = _o_yices_implies(guard, refinement);
        }
      }

      return refinement;
    // }
  }
  
  /* Could not find a suitable polynomial */
  return result;
}

