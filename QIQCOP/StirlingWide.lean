import QIQCOP.LawCode
import QIQCOP.Majorant

/-!
# Stirling expansion in a `√(n log n)` window, and elementary asymptotic absorption lemmas

* `stirlingWide`: for `x > 0` and any `R`, uniformly over `k` with `|k - n x| ≤ R √(n log n)`,
  `log₂ C(n+k-1,k) ≥ n g(x) + (k - n x) g'(x) - B log n` for large `n`.
* `MeanAsymp.absorb`: `A √n + B log n + D ≤ δ √(n log n)` eventually.
* `MeanAsymp.sqrt_nlogn_le`: `A √(n log n) ≤ δ n` eventually.
-/

open Real Filter
open scoped Nat

namespace QIQCOP

theorem stirlingWide {x : ℝ} (hx : 0 < x) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      |(k : ℝ) - n * x| ≤ R * √((n : ℝ) * Real.log n) →
        n * g x + ((k : ℝ) - n * x) * gp x - B * Real.log n ≤ logb 2 (sectorDim n k) := by
  set C : ℝ := x + |R| + 1 with hCdef
  have hC1 : 1 ≤ C := by have := abs_nonneg R; linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC1
  have hlogC1 : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith)
  set K : ℝ := R ^ 2 / x + (1/2) * Real.log C + 2 + Real.log (1 + C) with hKdef
  have hR2 : 0 ≤ R ^ 2 / x := by positivity
  have hK : 0 ≤ K := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(1 + K) / Real.log 2, by positivity, eventually_atTop.2 ⟨3, fun n hn k hk => ?_⟩⟩
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnpos' : 0 < n := by omega
  have hlogn : 1 ≤ Real.log n := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlogn' : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hnpos; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hnl0 : 0 ≤ (n : ℝ) * Real.log n := by positivity
  have hS : √((n : ℝ) * Real.log n) ≤ n := by
    rw [Real.sqrt_le_left hnpos.le]; nlinarith
  have hRabs : R * √((n : ℝ) * Real.log n) ≤ |R| * n := by
    calc R * √((n : ℝ) * Real.log n) ≤ |R| * √((n : ℝ) * Real.log n) :=
          mul_le_mul_of_nonneg_right (le_abs_self R) (Real.sqrt_nonneg _)
      _ ≤ |R| * n := mul_le_mul_of_nonneg_left hS (abs_nonneg R)
  have hkC : (k : ℝ) ≤ C * n := by
    have := (abs_le.1 hk).2
    have : 0 ≤ (n : ℝ) := hnpos.le
    nlinarith
  have hsq2 : ((k : ℝ) - n * x) ^ 2 ≤ R ^ 2 * (n * Real.log n) := by
    have := pow_le_pow_left₀ (abs_nonneg _) hk 2
    rw [sq_abs, mul_pow, Real.sq_sqrt hnl0] at this
    exact this
  have hquad : ((k : ℝ) - n * x) ^ 2 / (n * x) ≤ R ^ 2 / x * Real.log n := by
    rw [div_le_iff₀ (by positivity)]
    have e : R ^ 2 / x * Real.log n * (n * x) = R ^ 2 * (n * Real.log n) := by
      field_simp
    rw [e]; exact hsq2
  have hlogk : Real.log k ≤ Real.log C + Real.log n := by
    rcases (Nat.cast_nonneg (α := ℝ) k).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]
      linarith
    · rw [← Real.log_mul (by linarith) hnpos.ne']
      exact Real.log_le_log h0 hkC
  have hlognk : Real.log ((n : ℝ) + k) ≤ Real.log (1 + C) + Real.log n := by
    rw [← Real.log_mul (by linarith) hnpos.ne']
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hD := sectorDim_mul n k hnpos'
  have hc : (0 : ℝ) < ((n + k).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left k n)
  have hDpos : 0 < sectorDim n k := by
    have : 0 < sectorDim n k * ((n : ℝ) + k) := by rw [hD]; positivity
    exact pos_of_mul_pos_left this (by linarith)
  have hlogD : Real.log (sectorDim n k) + Real.log ((n : ℝ) + k) =
      Real.log ((n + k).choose k : ℝ) + Real.log n := by
    rw [← Real.log_mul hDpos.ne' (by linarith), ← Real.log_mul hc.ne' hnpos.ne', hD]
  have hT := taylor_aux hnpos hk0 hx
  have hS' := log_choose_ge_aux n k
  have hK1 : (1/2) * Real.log C + 2 + Real.log (1 + C) ≤
      ((1/2) * Real.log C + 2 + Real.log (1 + C)) * Real.log n :=
    le_mul_of_one_le_right (by linarith) hlogn
  have hKexp : (1 + K) * Real.log n = Real.log n + R ^ 2 / x * Real.log n +
      ((1/2) * Real.log C + 2 + Real.log (1 + C)) * Real.log n := by rw [hKdef]; ring
  have hmain : ((n : ℝ) + k) * Real.log (1 + x) - k * Real.log x - (1 + K) * Real.log n ≤
      Real.log (sectorDim n k) := by
    rw [hKexp]
    linarith
  have hgp : Real.log (1 + 1 / x) = Real.log (x + 1) - Real.log x := by
    rw [show 1 + 1 / x = (x + 1) / x by field_simp, Real.log_div (by linarith) hx.ne']
  unfold g gp
  simp only [Real.logb]
  rw [hgp]
  have hlhs : (n : ℝ) * ((x + 1) * (Real.log (x + 1) / Real.log 2) - x * (Real.log x / Real.log 2)) +
      ((k : ℝ) - n * x) * ((Real.log (x + 1) - Real.log x) / Real.log 2) -
      (1 + K) / Real.log 2 * Real.log n =
      (((n : ℝ) + k) * Real.log (1 + x) - k * Real.log x - (1 + K) * Real.log n) / Real.log 2 := by
    rw [add_comm 1 x]
    field_simp
    ring
  rw [hlhs]
  exact div_le_div_of_nonneg_right hmain hlog2.le

namespace MeanAsymp

lemma ev_log_ge (c : ℝ) : ∀ᶠ n : ℕ in atTop, c ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c

lemma ev_log_le_mul {c : ℝ} (hc : 0 < c) : ∀ᶠ n : ℕ in atTop, Real.log n ≤ c * n := by
  have h := (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop).bound hc
  filter_upwards [h] with n hn
  simp only [Function.comp_apply, id, Real.norm_eq_abs, Nat.abs_cast] at hn
  exact (le_abs_self _).trans hn

/-- `A √(n log n) ≤ δ n` eventually. -/
lemma sqrt_nlogn_le (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, A * √((n : ℝ) * Real.log n) ≤ δ * n := by
  have hA : 0 < |A| + 1 := by positivity
  filter_upwards [ev_log_le_mul (c := (δ / (|A| + 1)) ^ 2) (by positivity), ev_log_ge 0]
    with n hn hl
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : √((n : ℝ) * Real.log n) ≤ δ / (|A| + 1) * n := by
    rw [Real.sqrt_le_left (by positivity)]
    calc (n : ℝ) * Real.log n ≤ n * ((δ / (|A| + 1)) ^ 2 * n) :=
          mul_le_mul_of_nonneg_left hn hn0
      _ = (δ / (|A| + 1) * n) ^ 2 := by ring
  calc A * √((n : ℝ) * Real.log n) ≤ (|A| + 1) * √((n : ℝ) * Real.log n) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self A]) (Real.sqrt_nonneg _)
    _ ≤ (|A| + 1) * (δ / (|A| + 1) * n) := mul_le_mul_of_nonneg_left h1 hA.le
    _ = δ * n := by field_simp

/-- `A √n + B log n + D ≤ δ √(n log n)` eventually. -/
lemma absorb (A B D : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, A * √(n : ℝ) + B * Real.log n + D ≤ δ * √((n : ℝ) * Real.log n) := by
  set A' := |A| + |D| + 1 with hA'
  set B' := |B| + 1 with hB'
  have hA0 : 0 < A' := by positivity
  have hB0 : 0 < B' := by positivity
  filter_upwards [ev_log_le_mul (c := (δ / (2 * B')) ^ 2) (by positivity),
    ev_log_ge ((2 * A' / δ) ^ 2), ev_log_ge 0, eventually_ge_atTop 1] with n hn hl hl0 hn1
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hs1 : 1 ≤ √(n : ℝ) := by
    rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hnr
  have hS : √((n : ℝ) * Real.log n) = √(n : ℝ) * √(Real.log n) := Real.sqrt_mul hn0 _
  have h1 : 2 * A' / δ ≤ √(Real.log n) := Real.le_sqrt_of_sq_le hl
  have h1' : A' * √(n : ℝ) ≤ δ / 2 * √((n : ℝ) * Real.log n) := by
    rw [hS]
    rw [div_le_iff₀ hδ] at h1
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have h2 : B' * Real.log n ≤ δ / 2 * √((n : ℝ) * Real.log n) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ B' * Real.log n),
      ← Real.sqrt_sq (by positivity : (0:ℝ) ≤ δ / 2), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have : B' ^ 2 * Real.log n ≤ (δ / 2) ^ 2 * n := by
      have := mul_le_mul_of_nonneg_left hn (sq_nonneg B')
      calc B' ^ 2 * Real.log n ≤ B' ^ 2 * ((δ / (2 * B')) ^ 2 * n) := this
        _ = (δ / 2) ^ 2 * n := by field_simp
    calc (B' * Real.log n) ^ 2 = B' ^ 2 * Real.log n * Real.log n := by ring
      _ ≤ (δ / 2) ^ 2 * n * Real.log n := mul_le_mul_of_nonneg_right this hl0
      _ = (δ / 2) ^ 2 * (n * Real.log n) := by ring
  have hA1 : A * √(n : ℝ) + D ≤ A' * √(n : ℝ) := by
    have := le_abs_self A; have := le_abs_self D
    have hs0 := Real.sqrt_nonneg (n : ℝ)
    have : |D| ≤ |D| * √(n : ℝ) := le_mul_of_one_le_right (abs_nonneg D) hs1
    have : A * √(n : ℝ) ≤ |A| * √(n : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self A) hs0
    rw [hA']; nlinarith
  have hB1 : B * Real.log n ≤ B' * Real.log n :=
    mul_le_mul_of_nonneg_right (by rw [hB']; linarith [le_abs_self B]) hl0
  linarith

/-- Normal form of the dispersion square root. -/
lemma sqrt_form {c w G n lg : ℝ} (hc : 0 ≤ c) (hw : 0 ≤ w) (hG : 0 ≤ G) :
    √(c * (w * G ^ 2) * n * lg) = G * (√c * √w * √(n * lg)) := by
  rw [show c * (w * G ^ 2) * n * lg = G ^ 2 * (c * (w * (n * lg))) by ring,
    Real.sqrt_mul (sq_nonneg G), Real.sqrt_sq hG, Real.sqrt_mul hc, Real.sqrt_mul hw]
  ring

end MeanAsymp

end QIQCOP
