import QIQCOP.Majorant

/-!
# Sharp linear majorant of the binomial upper tail

`binomGT_le_linear_sharp`: for `0 < η < 1` and all large `r`,
`Pr{Bin(ℓ, η) > r} ≤ ℓ / λ_r` for every `ℓ`, where
`λ_r = (r + (√(log r) - 1) √((1-η) r)) / η`.
-/

open MeasureTheory ProbabilityTheory Real Filter

namespace QIQCOP

namespace MajorantSharp

/-- An exponential with positive rate eventually dominates a linear function. -/
lemma exp_half_growth {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) :
    ∃ S₀ : ℝ, ∀ a : ℝ, S₀ ≤ a → a + B ≤ c * exp (a / 2 - 1 / 8) := by
  set Y : ℝ := max 1 (2 * (9 / 4 + B) / c) with hY
  refine ⟨2 * Y + 1 / 4, fun a ha => ?_⟩
  set y : ℝ := a / 2 - 1 / 8 with hy
  have hyY : Y ≤ y := by rw [hy]; linarith
  have h1 : 1 ≤ y := (le_max_left _ _).trans hyY
  have h2 : 2 * (9 / 4 + B) / c ≤ y := (le_max_right _ _).trans hyY
  rw [div_le_iff₀ hc] at h2
  have hy0 : 0 ≤ y := by linarith
  have h3 : y ^ 2 / 2 ≤ exp y := by
    have := Real.quadratic_le_exp_of_nonneg hy0; linarith
  have ea : a = 2 * y + 1 / 4 := by rw [hy]; ring
  have h4 : a + B ≤ (9 / 4 + B) * y := by
    rw [ea]; nlinarith [mul_le_mul_of_nonneg_left h1 hB]
  have h5 : (9 / 4 + B) * y ≤ c * (y ^ 2 / 2) := by
    nlinarith [mul_le_mul_of_nonneg_right h2 hy0]
  calc a + B ≤ c * (y ^ 2 / 2) := h4.trans h5
    _ ≤ c * exp y := mul_le_mul_of_nonneg_left h3 hc.le

end MajorantSharp

open Majorant MajorantSharp

/-- **Sharp majorant.** For `0 < η < 1` there is `r₀` such that for all `r ≥ r₀` and all `ℓ`,
`Pr{Bin(ℓ,η) > r} ≤ ℓ / λ_r`, `λ_r := (r + (√(log r) - 1) √((1-η) r)) / η`. -/
theorem binomGT_le_linear_sharp {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ∀ ℓ : ℕ,
      binomGT ℓ η r ≤ (ℓ : ℝ) / ((r + (√(Real.log r) - 1) * √((1 - η) * r)) / η) := by
  obtain ⟨C, hC⟩ := binomBE hη0 hη1
  have hη' : 0 < 1 - η := by linarith
  have hlog4 : 0 ≤ Real.log (4 / η) :=
    Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
  set K : ℝ := 2 * √(Real.log (4 / η)) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hKexp : 2 * exp (-K ^ 2 / 4) = η / 2 := by
    rw [hKdef, mul_pow, Real.sq_sqrt hlog4,
      show -(2 ^ 2 * Real.log (4 / η)) / 4 = -Real.log (4 / η) by ring, exp_neg,
      exp_log (by positivity)]
    field_simp; ring
  obtain ⟨S₀, hS₀⟩ := exp_half_growth (c := (√(2 * π))⁻¹ * (1 / 2)) (by positivity)
    (B := K + |C|) (by positivity)
  have htend : Tendsto (fun r : ℕ => √(Real.log r)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.1 (htend.eventually_ge_atTop (max S₀ 1))
  refine ⟨max r₀ 1, fun r hr ℓ => ?_⟩
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  have haS := hr₀ r ((le_max_left _ _).trans hr)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hrR
  have hasq : √(Real.log r) ^ 2 = Real.log r := Real.sq_sqrt hlogr
  set a : ℝ := √(Real.log r) with ha
  have ha1 : 1 ≤ a := (le_max_right _ _).trans haS
  have haS0 : S₀ ≤ a := (le_max_left _ _).trans haS
  set s : ℝ := a - 1 with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  set D : ℝ := s * √((1 - η) * r) with hD
  have hD0 : 0 ≤ D := by positivity
  have hsq : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr0
  have hsqr : √(r : ℝ) * √(r : ℝ) = r := Real.mul_self_sqrt hr0.le
  have hDr : D ≤ r := by
    have h1 : s ≤ √(r : ℝ) := by
      have : a ≤ √(r : ℝ) := Real.sqrt_le_sqrt (by
        have := Real.log_le_sub_one_of_pos hr0; linarith)
      rw [hs]; linarith
    have h2 : √((1 - η) * r) ≤ √(r : ℝ) :=
      Real.sqrt_le_sqrt (mul_le_of_le_one_left hr0.le (by linarith))
    calc D ≤ √(r : ℝ) * √(r : ℝ) := mul_le_mul h1 h2 (Real.sqrt_nonneg _) hsq.le
      _ = r := hsqr
  have hlam0 : 0 < (r + D) / η := by positivity
  rcases le_or_gt ℓ r with hℓr | hℓr
  · exact (binomGT_le_zero_of_le hη0.le hη1.le hℓr).trans (by positivity)
  rcases le_or_gt ((r + D) / η) ℓ with hbig | hsmall
  · exact (binomGT_le_one hη0.le hη1.le ℓ r).trans ((one_le_div hlam0).2 hbig)
  have hℓR : (r : ℝ) ≤ ℓ := by exact_mod_cast hℓr.le
  have hG0 := binomGT_nonneg hη0.le hη1.le ℓ r
  rw [le_div_iff₀ hlam0, ← mul_div_assoc, div_le_iff₀ hη0]
  rcases le_or_gt (K * √(r : ℝ)) (r - η * ℓ) with hfar | hnear
  · have h1 := binomGT_le_chernoff hη0 hη1 hℓr hr1 hK0 hfar
    rw [hKexp] at h1
    have h2 : binomGT ℓ η r * (r + D) ≤ η / 2 * (r + D) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 := mul_le_mul_of_nonneg_left hℓR hη0.le
    have h4 : η / 2 * (r + D) ≤ η * r := by nlinarith only [hDr, hη0]
    linarith only [h2, h3, h4]
  · set L : ℕ := ⌈(r + D) / η⌉₊ with hL
    have hLge : (r + D) / η ≤ (L : ℝ) := Nat.le_ceil _
    have hLlt : (L : ℝ) < (r + D) / η + 1 := Nat.ceil_lt_add_one hlam0.le
    have hℓL : ℓ ≤ L := by exact_mod_cast (hsmall.le.trans hLge)
    have hL1 : 1 ≤ L := by omega
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
    have hηL : (r : ℝ) + D ≤ η * L := by
      rw [div_le_iff₀ hη0] at hLge; linarith
    have hηL2 : η * L < r + D + η := by
      have := mul_lt_mul_of_pos_left hLlt hη0
      rw [mul_add, mul_div_cancel₀ _ hη0.ne'] at this
      linarith
    have hLr : (r : ℝ) ≤ L := by exact_mod_cast (hℓr.le.trans hℓL)
    have hmono := binomGT_mono hη0.le hη1.le r hℓL
    have hGL : binomGT L η r = 1 - binomLT L η (r + 1) := rfl
    have hBE := (abs_le.1 (hC L hL1 (r + 1))).1
    have hσ0 : 0 < √((L : ℝ) * (η * (1 - η))) := Real.sqrt_pos.2 (by positivity)
    have hσD : D ≤ s * √((L : ℝ) * (η * (1 - η))) := by
      have hrηL : (r : ℝ) ≤ η * L := by linarith
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hs0
      calc (1 - η) * (r : ℝ) ≤ (1 - η) * (η * L) := mul_le_mul_of_nonneg_left hrηL hη'.le
        _ = (L : ℝ) * (η * (1 - η)) := by ring
    have hz : -s ≤ (((r + 1 : ℕ) : ℝ) - η * L) / √((L : ℝ) * (η * (1 - η))) := by
      rw [le_div_iff₀ hσ0]; push_cast; linarith
    have hΦ1 := Φ_strictMono.monotone hz
    have hΦ2 := SecondOrderLog.Φ_sub_ge (a := -s - 1 / 2) (b := -s) (K := s + 1 / 2)
      (by linarith) (by
        intro x hx; rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
    have hΦ3 := SecondOrderLog.Φ_pos (-s - 1 / 2)
    have hCL : C / √(L : ℝ) ≤ |C| / √(r : ℝ) :=
      calc C / √(L : ℝ) ≤ |C| / √(L : ℝ) :=
            div_le_div_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
        _ ≤ |C| / √(r : ℝ) :=
            div_le_div_of_nonneg_left (abs_nonneg C) hsq (Real.sqrt_le_sqrt hLr)
    have hgrow := hS₀ a haS0
    have hsqexp : √(r : ℝ) = exp (a ^ 2 / 2) := by
      rw [hasq, ← exp_half_log hr0]
    have hexp : exp (-(s + 1 / 2) ^ 2 / 2) * √(r : ℝ) = exp (a / 2 - 1 / 8) := by
      rw [hsqexp, ← exp_add]; congr 1; rw [hs]; ring
    have hkey : (s + K + |C|) / √(r : ℝ) ≤
        (√(2 * π))⁻¹ * exp (-(s + 1 / 2) ^ 2 / 2) * (1 / 2) := by
      rw [div_le_iff₀ hsq]
      have e : (√(2 * π))⁻¹ * exp (-(s + 1 / 2) ^ 2 / 2) * (1 / 2) * √(r : ℝ) =
          (√(2 * π))⁻¹ * (1 / 2) * (exp (-(s + 1 / 2) ^ 2 / 2) * √(r : ℝ)) := by ring
      rw [e, hexp]
      have : s + K + |C| ≤ a + (K + |C|) := by rw [hs]; linarith
      linarith
    have hθ : binomGT ℓ η r ≤ 1 - (s + K) / √(r : ℝ) := by
      have e : (s + K + |C|) / √(r : ℝ) = (s + K) / √(r : ℝ) + |C| / √(r : ℝ) := by ring
      have e2 : -s - (-s - 1 / 2) = (1 / 2 : ℝ) := by ring
      rw [e2] at hΦ2
      linarith
    have hθr : (s + K) / √(r : ℝ) * r = (s + K) * √(r : ℝ) := by
      calc (s + K) / √(r : ℝ) * r = (s + K) / √(r : ℝ) * (√(r : ℝ) * √(r : ℝ)) := by rw [hsqr]
        _ = (s + K) * √(r : ℝ) := by field_simp
    have hθ0 : 0 ≤ (s + K) / √(r : ℝ) := by positivity
    have hDs : D ≤ s * √(r : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (mul_le_of_le_one_left hr0.le (by linarith))) hs0
    have h2 : binomGT ℓ η r * (r + D) ≤ (1 - (s + K) / √(r : ℝ)) * (r + D) :=
      mul_le_mul_of_nonneg_right hθ (by positivity)
    have h3 := mul_nonneg hθ0 hD0
    have e3 : (1 - (s + K) / √(r : ℝ)) * (r + D) =
        r + D - (s + K) / √(r : ℝ) * r - (s + K) / √(r : ℝ) * D := by ring
    rw [e3, hθr] at h2
    have e4 : (s + K) * √(r : ℝ) = s * √(r : ℝ) + K * √(r : ℝ) := by ring
    linarith only [h2, h3, hDs, hnear, e4]

end QIQCOP
