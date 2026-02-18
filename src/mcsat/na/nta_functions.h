#ifndef NTA_FUNCTIONS_H
#define NTA_FUNCTIONS_H

#include <stdio.h>
#include "mcsat/value.h"
#include "mcsat/model.h"
#include "mcsat/nta_info.h"
#include "mcsat/trail.h"
#include "mcsat/na/na_plugin_internal.h"
#include "terms/polynomials.h"
#include <poly/value.h>

#include "terms/term_manager.h"
#include "terms/terms.h"
#include "model/model_eval.h"
#include "model/concrete_values.h"

/** Enum for Taylor series centers (only 4 allowed values) */
typedef enum taylor_center_kind {
  TAYLOR_CENTER_ZERO,   /* center = 0 */
  TAYLOR_CENTER_PI_2,   /* center = pi/2 */
  TAYLOR_CENTER_PI,     /* center = pi */
  TAYLOR_CENTER_PI_3_2,  /* center = 3*pi/2 */
  TAYLOR_CENTER_2_PI    /* center = 2*pi */
} taylor_center_kind_t;

/* Use ARB for rigorous interval arithmetic */
#include <flint/arb.h>

/**
 * nta_value: discriminated union holding either an mcsat_value_t or an arb_t.
 */
typedef enum {
  NTA_VALUE_MCSAT,
  NTA_VALUE_ARB
} nta_value_type_t;

typedef struct {
  nta_value_type_t type;
  union {
    mcsat_value_t mcsat_val;
    arb_struct arb_val[1];
  };
} nta_value;

/**
 * Print an nta_value to the given output stream.
 * If the value is mcsat_value_t, uses mcsat_value_print.
 * If the value is arb_t, prints the midpoint with mpfr_out_str.
 */
void nta_value_print(na_plugin_t* na, const nta_value* nv, FILE* out, slong prec);


/**
 * Compute the sine approximation of a value.
 * 
 * Given an mcsat_value_t (which could be a rational, libpoly value, etc.),
 * this function:
 * 1. Converts the value to a double-precision floating point number
 * 2. Computes sin(x) using ARB with the given precision
 * 3. Converts the result back to a rational mcsat_value_t
 * 
 * @param value  Pointer to an mcsat_value_t to approximate the sine of
 * @param prec   The precision to use for ARB computation
 * @return       An mcsat_value_t containing the rational approximation of sin(value)
 */
mcsat_value_t compute_sin_approximation(const mcsat_value_t *value, slong prec);

/**
 * Compute the Taylor series approximation of sine.
 * 
 * Computes a Taylor series expansion of sin(t) around a center point,
 * where t is a term (variable) and the expansion is centered at 'center'.
 * The result is a Yices polynomial representing the approximation.
 * 
 * 
 *   If we only consider fixed centers (0, pi/2, pi, 3*pi/2), then we can avoid approximations (we know sin_c, cos_c exactly)
 * The Taylor series for sin(x) around point c is:
 *   sin(c) + cos(c)*(x-c) - sin(c)/2!*(x-c)^2 - cos(c)/3!*(x-c)^3 + ...
 * 
 * @param t      The term (variable) representing the argument to sine
 * @param center The center point for Taylor expansion (lp_value_t)
 * @param degree The degree of the Taylor polynomial (number of terms)
 * @return       A polynomial_t* representing the Taylor approximation,
 *               or NULL if the approximation cannot be computed
 */
// Create a Taylor-series arithmetic term approximating sin(t) around `center` up to `degree`.
// Returns a `term_t` (arithmetic term) or `null_term` on error.
// The center is specified as an enum (0, pi/2, pi, or 3*pi/2), and sin_c/cos_c are computed exactly.
// The pi term is obtained from nta_info.
term_t compute_taylor_approximation_of_sin(na_plugin_t *na, term_manager_t *tm, nta_info_t *nta_info, term_t t, taylor_center_kind_t center, int degree);

/* Create a Taylor-series arithmetic term approximating exp(t) around center c up to degree. */
term_t compute_taylor_approximation_of_exp(na_plugin_t *na, term_manager_t *tm, term_t t, const mcsat_value_t *center, int degree);

/**
 * Compute a safe over-approximation of the range of an arithmetic term.
 * 
 * This function evaluates an arithmetic term using values from an mcsat model,
 * computing interval bounds using ARB (Arb Ball arithmetic) for **guaranteed**
 * rigorous interval arithmetic with proper rounding.
 * 
 * Special handling for sin abstractions:
 * - If a variable y has an assignment in the model, but y is a key in 
 *   nta_info->inverse_sin_map, then we do NOT evaluate y directly as value_y.
 *   Instead, we:
 *   1. Get the inverse sin term x (where y represents sin(x))
 *   2. Get the value of x from the model
 *   3. Compute a safe interval that contains sin(x) using ARB
 *   4. Use that interval to compute a safe range for the given term
 * 
 * @param na        The NA plugin context (contains term manager)
 * @param term      The arithmetic term to evaluate
 * @param model     The mcsat model with variable assignments
 * @param nta_info  The nta_info structure containing inverse_sin_map
 * @param var_db    The variable database (for variable lookup)
 * @param result    Output parameter: nta_value containing the safe range
 * @param incomplete_vars Output parameter: variables for which sin(x) fallback was used
 * 
 * @return true if the safe range was successfully computed, false if:
 *         - The term contains unassigned variables
 *         - The term contains variables in inverse_sin_map whose inverse 
 *           terms are unassigned
 *         - Memory allocation fails
 *         - Unsupported term kind is encountered
 * 
 * The caller must clear the result based on its tag (NTA_VALUE_MCSAT: mcsat_value_destruct; NTA_VALUE_ARB: arb_clear).
 */
bool nta_compute_safe_range(na_plugin_t* na, term_t term, 
                       const mcsat_model_t *model, 
                       const nta_info_t *nta_info,
                       variable_db_t *var_db,
                       nta_value* result,
                       ivector_t* incomplete_vars,
                       slong precision);

/* Tri-state truth value for safe truth computation */
typedef enum {
  NTA_FALSE = 0,
  NTA_TRUE = 1,
  NTA_TRUE_OR_FALSE = 2
} nta_tristate_t;

/*
 * Compute a safe truth value for a Boolean atom (ARITH_EQ_ATOM or ARITH_GE_ATOM).
 * The function computes a safe interval for the arithmetic argument using
 * `nta_compute_safe_range` and returns `NTA_TRUE`, `NTA_FALSE` or
 * `NTA_TRUE_OR_FALSE` according to the specification in the caller request.
 */
nta_tristate_t nta_compute_safe_truth_value(na_plugin_t* na, term_t atom,
                                           const mcsat_model_t *model,
                                           const nta_info_t *nta_info,
                                           variable_db_t *var_db,
                                           ivector_t* incomplete_vars,
                                           slong precision);

/**
 * Check consistency of a fully assigned constraint variable.
 * 
 * This function verifies that:
 * 1. The constraint variable is fully assigned in the trail
 * 2. The computed safe truth value of the corresponding term
 *    matches the value assigned in the trail
 * 
 * @param na       The NA plugin context
 * @param prop     The trail token
 * @param cstr_var The constraint variable to check
 * 
 * @return true if the constraint variable's trail value matches
 *         the computed safe truth value, false otherwise
 */
bool nta_consistency_check(na_plugin_t* na, trail_token_t* prop, variable_t cstr_var);

/**
 * Return true if any constraint in the trail was accepted via delta mode.
 */
bool delta_used_in_trail(const mcsat_trail_t* trail);

/**
 * Refine NTA abstraction for a constraint by generating refined Taylor lemmas.
 * 
 * For each sin variable in the constraint, generates a refined Taylor approximation
 * that separates the abstract value from the true sin value.
 * 
 * @param na        The NA plugin
 * @param cstr_var  The constraint variable to refine
 * @param refinements Output vector to store generated refinement terms
 * @return A real-valued variable (e.g., sin_x) used in refinement, or variable_null if none
 */
variable_t nta_refine_abstraction(na_plugin_t* na, variable_t cstr_var,
                                 ivector_t* refinements,
                                 ivector_t* refinement_literals);

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
 * @param val_sin_x The mcsat value of sin(x)
 * @param nta_info  The nta_info structure
 * @param var_db    The variable database
 * @param lp_data   The libpoly data
 * @param eval      The evaluator built from the trail model
 * @param vtbl      The value table associated with the evaluator model
 * 
 * @return A term_t representing the refined Taylor polynomial approximation,
 *         or NULL_TERM if refinement fails or if val_x == sin(val_x)
 */
term_t refine_taylor_approximation_of_sin(na_plugin_t *na, term_manager_t *tm, term_t x, term_t sin_x,
                                          const mcsat_value_t *val_x, const mcsat_value_t *val_sin_x,
                                          term_t arg_term_override,
                                          term_t* conflict_literal_out,
                                          nta_info_t *nta_info, variable_db_t *var_db,
                                          lp_data_t *lp_data, evaluator_t *eval, value_table_t *vtbl);

/**
 * Refine approximation of exp based on Padé approximants of degree 1 and 2.
 *
 * Produces either upper or lower bounds depending on want_upper.
 * Returns false if no lemmas are produced.
 */
bool refine_approximation_of_exp_with_pade(na_plugin_t *na, term_manager_t *tm, term_t x, term_t exp_x,
                                           const mcsat_value_t *val_x, bool want_upper,
                                           term_t lemmas_out[2], term_t main_literals_out[2]);

bool refine_approximation_of_exp_with_taylor(na_plugin_t *na, term_manager_t *tm, term_t x, term_t exp_x,
                                             const mcsat_value_t *val_x, bool want_upper,
                                             term_t *lemma_out);

bool refine_approximation_of_exp_linear(na_plugin_t *na, term_manager_t *tm, term_t x, term_t exp_x,
                                        const mcsat_value_t *val_x, const mcsat_value_t *val_exp_x,
                                        bool want_upper, term_t *lemma_out, term_t *main_literal_out);

#endif
