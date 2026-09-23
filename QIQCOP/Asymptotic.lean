import QIQCOP.Defs

/-!
# `√n` cannot be dominated by `O(log n)`

The purely analytic core of the disproof: if an achievable lower bound has a strictly
larger `√n` coefficient than the conjectured upper bound, the two contradict each other
for large `n`, whatever the `O(log n)` constants are.
-/

open Real Filter Asymptotics

namespace QIQCOP

/-- For `δ > 0`, `δ √n ≤ K log n` fails for large `n`. -/
theorem not_eventually_sqrt_le_log {δ K : ℝ} (hδ : 0 < δ) :
    ¬ ∀ᶠ n : ℕ in atTop, δ * √(n : ℝ) ≤ K * log n := by
  intro h
  have ho := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hc : 0 < δ / (2 * (|K| + 1)) := by positivity
  have hb := ho.def hc
  obtain ⟨N, hN⟩ := (h.and (hb.and (eventually_ge_atTop 1))).exists_forall_of_atTop
  obtain ⟨h1, h2, h3⟩ := hN N le_rfl
  simp only [Function.comp_apply] at h2
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast h3
  have hs : √(N : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hlog : 0 ≤ log (N : ℝ) := Real.log_nonneg hn
  have hspos : 0 < √(N : ℝ) := Real.sqrt_pos.mpr (by linarith)
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (by positivity), ← hs] at h2
  have hK : K * log N ≤ |K| * log N := mul_le_mul_of_nonneg_right (le_abs_self K) hlog
  have hK' : |K| * log N ≤ |K| * (δ / (2 * (|K| + 1)) * √(N : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
  have key : |K| * (δ / (2 * (|K| + 1))) < δ := by
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg K]
  nlinarith

/-- **Abstract disproof.** Suppose `logM` satisfies an achievability lower bound with
dispersion `a` and a conjectured upper bound with dispersion `b`, both with `O(log n)`
remainders, where `q < 0` (i.e. `ε < 1/2`) and `0 ≤ a < b`. Contradiction. -/
theorem second_order_contradiction (logM : ℕ → ℝ) {G a b q : ℝ}
    (hq : q < 0) (ha : 0 ≤ a) (hab : a < b)
    (hach : ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, n * G + √(n * a) * q - A * log n ≤ logM n)
    (hconj : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, logM n ≤ n * G + √(n * b) * q + C * log n) :
    False := by
  obtain ⟨A, hA⟩ := hach
  obtain ⟨C, hC⟩ := hconj
  have hsab : √a < √b := Real.sqrt_lt_sqrt ha hab
  apply not_eventually_sqrt_le_log (δ := (√b - √a) * (-q)) (K := A + C)
    (mul_pos (by linarith) (by linarith))
  filter_upwards [hA, hC] with n h1 h2
  have e1 : √((n : ℝ) * a) = √(n : ℝ) * √a := Real.sqrt_mul (Nat.cast_nonneg n) a
  have e2 : √((n : ℝ) * b) = √(n : ℝ) * √b := Real.sqrt_mul (Nat.cast_nonneg n) b
  rw [e1] at h1
  rw [e2] at h2
  nlinarith

end QIQCOP
