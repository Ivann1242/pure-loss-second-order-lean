import Mathlib

/-!
# Two-sided Stirling bounds for `log n!`

`n log n - n + log(2πn)/2 ≤ log n! ≤ n log n - n + log(2πn)/2 + 1/(12n)` for `n ≥ 1`.
-/

open Real Filter Topology
open scoped Nat

namespace QIQCOP.BE

theorem log_factorial_ge {n : ℕ} (hn : n ≠ 0) :
    n * log n - n + log (2 * π * n) / 2 ≤ log (n ! : ℝ) := by
  have h := Stirling.le_log_factorial_stirling hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [log_mul (by positivity) hn'.ne']
  linarith

lemma log_stirlingSeq_sub_le {n m : ℕ} (hn : n ≠ 0) (hnm : n ≤ m) :
    log (Stirling.stirlingSeq n) - log (Stirling.stirlingSeq m) ≤
      1 / (12 * n) - 1 / (12 * m) := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h := Stirling.log_stirlingSeq_sdiff_le m
    have hm' : (0 : ℝ) < m := by
      exact_mod_cast lt_of_lt_of_le (Nat.pos_of_ne_zero hn) hm
    have e : (1 : ℝ) / (12 * m * (m + 1)) = 1 / (12 * m) - 1 / (12 * ((m + 1 : ℕ) : ℝ)) := by
      push_cast
      field_simp
      ring
    rw [e] at h
    linarith

theorem log_stirlingSeq_le {n : ℕ} (hn : n ≠ 0) :
    log (Stirling.stirlingSeq n) ≤ log (√π) + 1 / (12 * n) := by
  have hpi : (√π) ≠ 0 := by positivity
  have hlim : Tendsto (fun m : ℕ => log (Stirling.stirlingSeq n) - log (Stirling.stirlingSeq m))
      atTop (𝓝 (log (Stirling.stirlingSeq n) - log (√π))) :=
    tendsto_const_nhds.sub
      ((continuousAt_log hpi).tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hle : ∀ᶠ m : ℕ in atTop,
      log (Stirling.stirlingSeq n) - log (Stirling.stirlingSeq m) ≤ 1 / (12 * n) := by
    filter_upwards [eventually_ge_atTop n] with m hm
    have h := log_stirlingSeq_sub_le hn hm
    have : (0 : ℝ) ≤ 1 / (12 * m) := by positivity
    linarith
  have := le_of_tendsto hlim hle
  linarith

theorem log_factorial_le {n : ℕ} (hn : n ≠ 0) :
    log (n ! : ℝ) ≤ n * log n - n + log (2 * π * n) / 2 + 1 / (12 * n) := by
  have h := log_stirlingSeq_le hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [Stirling.log_stirlingSeq_formula, log_sqrt pi_pos.le, log_div hn'.ne' (exp_pos 1).ne',
    log_exp, log_mul two_ne_zero hn'.ne'] at h
  rw [log_mul (by positivity) hn'.ne', log_mul two_ne_zero pi_pos.ne']
  linarith

end QIQCOP.BE
