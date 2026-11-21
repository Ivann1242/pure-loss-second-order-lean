import QIQCOP.LogConv
import QIQCOP.BerryEsseen

/-!
# Linear majorant of the binomial upper tail and a moderate-deviation lower-tail bound

* `binomGT_le_linear`: for `0 < η < 1`, `0 < κ < 1` and all large `r`,
  `Pr{Bin(ℓ, η) > r} ≤ ℓ / λ_r` for every `ℓ`, where
  `λ_r = (r + √((1-κ) log r) √((1-η) r)) / η`.
* `binomLT_moderate`: `Pr{Bin(ℓ, η) < t} ≤ C'/√ℓ` whenever
  `t ≤ η ℓ - √((1+κ) log ℓ) √(ℓ η (1-η))`.
* `Majorant.sqrt_log_mul_sqrt_le`, `Majorant.eventually_mul_sqrt_log_mul_sqrt_le`,
  `Majorant.add_sqrt_log_mono`, `Majorant.add_sqrt_log_mono_nat`: elementary facts on
  `r ↦ r + √((1-κ) log r) √((1-η) r)`.
-/

open MeasureTheory ProbabilityTheory Real Filter

namespace QIQCOP

namespace Majorant

/-! ### Elementary real-analysis helpers -/

lemma exp_half_log {x : ℝ} (hx : 0 < x) : exp (Real.log x / 2) = √x := by
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq hx.le (exp_pos _).le, ← exp_add, add_halves,
    exp_log hx]

/-- Gaussian Chernoff bound: `Φ(-s) ≤ exp(-s²/2)` for `s ≥ 0`. -/
lemma Φ_neg_le_exp {s : ℝ} (hs : 0 ≤ s) : Φ (-s) ≤ exp (-s ^ 2 / 2) := by
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (t := -s) (-s)
    (by linarith) (integrable_exp_mul_gaussianReal (-s))
  rw [mgf_id_gaussianReal] at h
  have e : exp (- -s * -s) * exp (0 * -s + ((1 : NNReal) : ℝ) * (-s) ^ 2 / 2) =
      exp (-s ^ 2 / 2) := by
    rw [← exp_add]; congr 1; simp only [NNReal.coe_one]; ring
  rw [Φ_eq]
  calc (gaussianReal 0 1).real (Set.Iic (-s)) = (gaussianReal 0 1).real {ω | id ω ≤ -s} := rfl
    _ ≤ _ := h
    _ = _ := e

/-- A super-exponential eventually dominates a linear function. -/
lemma exp_growth {κ' c B : ℝ} (hκ : 0 < κ') (hc : 0 < c) (hB : 0 ≤ B) :
    ∃ S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s → s + B ≤ c * exp (κ' * s ^ 2 - s - 1 / 2) := by
  refine ⟨max 1 (max (3 / κ') (2 * (1 + B) / c)), fun s hs => ?_⟩
  have h1 : 1 ≤ s := (le_max_left _ _).trans hs
  have h2 : 3 / κ' ≤ s := ((le_max_left _ _).trans (le_max_right _ _)).trans hs
  have h3 : 2 * (1 + B) / c ≤ s := ((le_max_right _ _).trans (le_max_right _ _)).trans hs
  rw [div_le_iff₀ hκ] at h2
  rw [div_le_iff₀ hc] at h3
  have hs0 : 0 ≤ s := by linarith
  have h4 : s ≤ κ' * s ^ 2 - s - 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right h2 hs0]
  have h5 : s ^ 2 / 2 ≤ exp s := by
    have := Real.quadratic_le_exp_of_nonneg hs0; linarith
  have h6 : exp s ≤ exp (κ' * s ^ 2 - s - 1 / 2) := exp_le_exp.2 h4
  have h7 : s + B ≤ c * (s ^ 2 / 2) := by
    nlinarith [mul_le_mul_of_nonneg_right h3 hs0, mul_le_mul_of_nonneg_left h1 hB]
  calc s + B ≤ c * (s ^ 2 / 2) := h7
    _ ≤ c * exp (κ' * s ^ 2 - s - 1 / 2) :=
        mul_le_mul_of_nonneg_left (h5.trans h6) hc.le

/-! ### Goal C: the function `r ↦ r + √((1-κ) log r) √((1-η) r)` -/

/-- `√((1-κ) log r) √((1-η) r) ≤ r` for every natural `r`. -/
lemma sqrt_log_mul_sqrt_le {η κ : ℝ} (hη0 : 0 ≤ η) (hκ0 : 0 ≤ κ) (r : ℕ) :
    √((1 - κ) * Real.log r) * √((1 - η) * r) ≤ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog : 0 ≤ Real.log r := Real.log_nonneg hrR
  have hlog2 : Real.log r ≤ r := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < r); linarith
  have h1 : √((1 - κ) * Real.log r) ≤ √(r : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
  have h2 : √((1 - η) * r) ≤ √(r : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
  calc √((1 - κ) * Real.log r) * √((1 - η) * r) ≤ √(r : ℝ) * √(r : ℝ) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = r := Real.mul_self_sqrt (by linarith)

/-- For every constant `c ≥ 0`, eventually `c · √((1-κ) log r) √((1-η) r) ≤ r`. -/
lemma eventually_mul_sqrt_log_mul_sqrt_le {η κ : ℝ} (hη0 : 0 ≤ η) (hκ0 : 0 ≤ κ) {c : ℝ}
    (hc : 0 ≤ c) :
    ∀ᶠ r : ℕ in atTop, c * (√((1 - κ) * Real.log r) * √((1 - η) * r)) ≤ r := by
  filter_upwards [SecondOrderLog.eventually_sqrt_ge (2 * c ^ 2), eventually_ge_atTop 1]
    with r hr hr1
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hlog : 0 ≤ Real.log r := Real.log_nonneg hrR
  have hsq : 0 < √(r : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsqr : √(r : ℝ) * √(r : ℝ) = r := Real.mul_self_sqrt hr0
  have hlog2 : Real.log r ≤ 2 * √(r : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos hsq
    rw [Real.log_sqrt hr0] at h1
    linarith
  have h2 : √((1 - η) * r) ≤ √(r : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
  have h3 : c * √((1 - κ) * Real.log r) ≤ √(r : ℝ) := by
    rw [Real.le_sqrt (by positivity) hr0, mul_pow]
    rcases le_or_gt ((1 - κ) * Real.log r) 0 with hneg | hpos
    · rw [Real.sqrt_eq_zero_of_nonpos hneg]; simp
    rw [Real.sq_sqrt hpos.le]
    have h4 : (1 - κ) * Real.log r ≤ 2 * √(r : ℝ) := by nlinarith
    calc c ^ 2 * ((1 - κ) * Real.log r) ≤ c ^ 2 * (2 * √(r : ℝ)) :=
          mul_le_mul_of_nonneg_left h4 (sq_nonneg c)
      _ = 2 * c ^ 2 * √(r : ℝ) := by ring
      _ ≤ √(r : ℝ) * √(r : ℝ) := mul_le_mul_of_nonneg_right hr hsq.le
      _ = r := hsqr
  calc c * (√((1 - κ) * Real.log r) * √((1 - η) * r))
      = c * √((1 - κ) * Real.log r) * √((1 - η) * r) := by ring
    _ ≤ √(r : ℝ) * √(r : ℝ) :=
        mul_le_mul h3 h2 (Real.sqrt_nonneg _) hsq.le
    _ = r := hsqr

/-- Monotonicity of `x ↦ x + √((1-κ) log x) √((1-η) x)` on `[1, ∞)`. -/
lemma add_sqrt_log_mono {η κ : ℝ} (hη1 : η ≤ 1) (hκ1 : κ ≤ 1) {x y : ℝ} (hx : 1 ≤ x)
    (hxy : x ≤ y) :
    x + √((1 - κ) * Real.log x) * √((1 - η) * x) ≤
      y + √((1 - κ) * Real.log y) * √((1 - η) * y) :=
  add_le_add hxy (mul_le_mul
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hxy)
      (by linarith)))
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hxy (by linarith)))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Monotonicity of `r ↦ r + √((1-κ) log r) √((1-η) r)` on the naturals. -/
lemma add_sqrt_log_mono_nat {η κ : ℝ} (hη1 : η ≤ 1) (hκ1 : κ ≤ 1) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    (r₁ : ℝ) + √((1 - κ) * Real.log r₁) * √((1 - η) * r₁) ≤
      r₂ + √((1 - κ) * Real.log r₂) * √((1 - η) * r₂) := by
  rcases Nat.eq_zero_or_pos r₁ with rfl | hr
  · simp only [Nat.cast_zero, Real.log_zero, mul_zero, Real.sqrt_zero, add_zero]
    positivity
  · exact add_sqrt_log_mono hη1 hκ1 (by exact_mod_cast hr) (by exact_mod_cast h)

/-! ### Binomial tail helpers -/

lemma binomGT_le_zero_of_le {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {ℓ r : ℕ} (h : ℓ ≤ r) :
    binomGT ℓ η r ≤ 0 := by
  have h1 := binomGT_mono hη0 hη1 r h
  have h2 : binomGT r η r = 0 := by
    unfold binomGT binomLT; rw [sum_binomPMF]; ring
  linarith

/-- Chernoff bound for the upper tail when `r` is at least `K √r` above the mean. -/
lemma binomGT_le_chernoff {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) {ℓ r : ℕ} (hrℓ : r < ℓ)
    (hr : 1 ≤ r) {K : ℝ} (hK : 0 ≤ K) (ha : K * √(r : ℝ) ≤ r - η * ℓ) :
    binomGT ℓ η r ≤ 2 * exp (-K ^ 2 / 4) := by
  set a : ℝ := r - η * ℓ with hadef
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  have ha1 : a ≤ r := by rw [hadef]; nlinarith
  have hsum : binomGT ℓ η r = ∑ k ∈ Finset.Ico (r + 1) (ℓ + 1), binomPMF ℓ η k := by
    have := binomLT_add_tail ℓ η (t := r + 1) (by omega)
    unfold binomGT; linarith
  have hsub : ∑ k ∈ Finset.Ico (r + 1) (ℓ + 1), binomPMF ℓ η k ≤
      ∑ k ∈ (Finset.range (ℓ + 1)).filter (fun k : ℕ => a ≤ |(k : ℝ) - η * ℓ|),
        binomPMF ℓ η k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun k _ _ => binomPMF_nonneg hη0.le hη1.le k)
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hk.2, ?_⟩
    have : (r : ℝ) + 1 ≤ k := by exact_mod_cast hk.1
    exact le_trans (by rw [hadef]; linarith) (le_abs_self _)
  have hch := BE.binom_tail_le (η := η) (lam := a / (2 * r)) a hη0 hη1 (by positivity)
    (by rw [div_le_one (by positivity)]; linarith) ℓ
  rw [hsum]
  refine (hsub.trans hch).trans ?_
  have e1 : η * (1 - η) * ℓ ≤ r := by
    have : η * ℓ ≤ r := by rw [hadef] at ha0; linarith
    nlinarith [mul_nonneg hη0.le hℓ0]
  have e2 : (a / (2 * r)) ^ 2 * (η * (1 - η)) * ℓ ≤ (a / (2 * r)) ^ 2 * r := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left e1 (sq_nonneg _)
  have e3 : (a / (2 * r)) ^ 2 * r - a / (2 * r) * a = -(a ^ 2 / r) / 4 := by
    field_simp; ring
  have e4 : K ^ 2 ≤ a ^ 2 / r := by
    rw [le_div_iff₀ hr0]
    calc K ^ 2 * r = (K * √(r : ℝ)) ^ 2 := by rw [mul_pow, Real.sq_sqrt hr0.le]
      _ ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) ha 2
  have e5 : (a / (2 * r)) ^ 2 * (η * (1 - η)) * ℓ - a / (2 * r) * a ≤ -K ^ 2 / 4 := by
    linarith
  exact mul_le_mul_of_nonneg_left (exp_le_exp.2 e5) (by norm_num)

end Majorant

open Majorant

/-- **Goal A.** For `0 < η < 1` and `0 < κ < 1` there is `r₀` such that for all `r ≥ r₀` and all
`ℓ`, `Pr{Bin(ℓ,η) > r} ≤ ℓ / λ_r`, `λ_r := (r + s_r √((1-η) r)) / η`,
`s_r := √((1-κ) log r)`. -/
theorem binomGT_le_linear {η κ : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ∀ ℓ : ℕ,
      binomGT ℓ η r ≤ (ℓ : ℝ) / ((r + √((1 - κ) * Real.log r) * √((1 - η) * r)) / η) := by
  obtain ⟨C, hC⟩ := binomBE hη0 hη1
  have hη' : 0 < 1 - η := by linarith
  have hκ' : 0 < 1 - κ := by linarith
  have hlog4 : 0 ≤ Real.log (4 / η) :=
    Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
  set K : ℝ := 2 * √(Real.log (4 / η)) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hKexp : 2 * exp (-K ^ 2 / 4) = η / 2 := by
    rw [hKdef, mul_pow, Real.sq_sqrt hlog4,
      show -(2 ^ 2 * Real.log (4 / η)) / 4 = -Real.log (4 / η) by ring, exp_neg,
      exp_log (by positivity)]
    field_simp; ring
  have hκ2 : 0 < κ / (2 * (1 - κ)) := by positivity
  obtain ⟨S₀, hS₀⟩ := exp_growth hκ2 (c := (√(2 * π))⁻¹) (by positivity) (B := K + |C|)
    (by positivity)
  have htend : Tendsto (fun r : ℕ => √((1 - κ) * Real.log r)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hκ')
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.1 (htend.eventually_ge_atTop S₀)
  refine ⟨max r₀ 1, fun r hr ℓ => ?_⟩
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  have hsS := hr₀ r ((le_max_left _ _).trans hr)
  have hDr := sqrt_log_mul_sqrt_le (η := η) (κ := κ) hη0.le hκ0.le r
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hrR
  have hslog : √((1 - κ) * Real.log r) ^ 2 = (1 - κ) * Real.log r :=
    Real.sq_sqrt (by positivity)
  set s : ℝ := √((1 - κ) * Real.log r) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set D : ℝ := s * √((1 - η) * r) with hD
  have hD0 : 0 ≤ D := by positivity
  have hsq : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr0
  have hsqr : √(r : ℝ) * √(r : ℝ) = r := Real.mul_self_sqrt hr0.le
  have hDs : D ≤ s * √(r : ℝ) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by nlinarith)) hs0
  have hlam0 : 0 < (r + D) / η := by positivity
  rcases le_or_gt ℓ r with hℓr | hℓr
  · exact (binomGT_le_zero_of_le hη0.le hη1.le hℓr).trans (by positivity)
  rcases le_or_gt ((r + D) / η) ℓ with hbig | hsmall
  · exact (binomGT_le_one hη0.le hη1.le ℓ r).trans ((one_le_div hlam0).2 hbig)
  have hℓR : (r : ℝ) ≤ ℓ := by exact_mod_cast hℓr.le
  have hG0 := binomGT_nonneg hη0.le hη1.le ℓ r
  rw [le_div_iff₀ hlam0, ← mul_div_assoc, div_le_iff₀ hη0]
  rcases le_or_gt (K * √(r : ℝ)) (r - η * ℓ) with hfar | hnear
  · -- far below the threshold: Chernoff
    have h1 := binomGT_le_chernoff hη0 hη1 hℓr hr1 hK0 hfar
    rw [hKexp] at h1
    have h2 : binomGT ℓ η r * (r + D) ≤ η / 2 * (r + D) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hℓR hη0.le]
  · -- near the threshold: Berry–Esseen at `⌈λ_r⌉`
    set L : ℕ := ⌈(r + D) / η⌉₊ with hL
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
    have hσD : D ≤ s * √((L : ℝ) * (η * (1 - η))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by nlinarith)) hs0
    have hz : -s ≤ (((r + 1 : ℕ) : ℝ) - η * L) / √((L : ℝ) * (η * (1 - η))) := by
      rw [le_div_iff₀ hσ0]; push_cast; linarith
    have hΦ1 := Φ_strictMono.monotone hz
    have hΦ2 := SecondOrderLog.Φ_sub_ge (a := -s - 1) (b := -s) (K := s + 1) (by linarith) (by
      intro x hx; rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
    have hΦ3 := SecondOrderLog.Φ_pos (-s - 1)
    have hCL : C / √(L : ℝ) ≤ |C| / √(r : ℝ) :=
      calc C / √(L : ℝ) ≤ |C| / √(L : ℝ) :=
            div_le_div_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
        _ ≤ |C| / √(r : ℝ) :=
            div_le_div_of_nonneg_left (abs_nonneg C) hsq (Real.sqrt_le_sqrt hLr)
    have hgrow := hS₀ s hsS
    have hsqexp : √(r : ℝ) = exp (s ^ 2 / (2 * (1 - κ))) := by
      rw [hslog, ← exp_half_log hr0]; congr 1; field_simp
    have hexp : exp (-(s + 1) ^ 2 / 2) * √(r : ℝ) =
        exp (κ / (2 * (1 - κ)) * s ^ 2 - s - 1 / 2) := by
      rw [hsqexp, ← exp_add]; congr 1; field_simp; ring
    have hkey : (s + K + |C|) / √(r : ℝ) ≤ (√(2 * π))⁻¹ * exp (-(s + 1) ^ 2 / 2) := by
      rw [div_le_iff₀ hsq, mul_assoc, hexp]; linarith
    have hθ : binomGT ℓ η r ≤ 1 - (s + K) / √(r : ℝ) := by
      have e : (s + K + |C|) / √(r : ℝ) = (s + K) / √(r : ℝ) + |C| / √(r : ℝ) := by ring
      have e2 : -s - (-s - 1) = (1 : ℝ) := by ring
      rw [e2, mul_one] at hΦ2
      linarith
    have hθr : (s + K) / √(r : ℝ) * r = (s + K) * √(r : ℝ) := by
      calc (s + K) / √(r : ℝ) * r = (s + K) / √(r : ℝ) * (√(r : ℝ) * √(r : ℝ)) := by rw [hsqr]
        _ = (s + K) * √(r : ℝ) := by field_simp
    have hθ0 : 0 ≤ (s + K) / √(r : ℝ) := by positivity
    have h2 : binomGT ℓ η r * (r + D) ≤ (1 - (s + K) / √(r : ℝ)) * (r + D) :=
      mul_le_mul_of_nonneg_right hθ (by positivity)
    linarith [mul_nonneg hθ0 hD0]

/-- **Goal B.** Moderate-deviation lower-tail bound from Berry–Esseen:
`∃ C', ∀ ℓ ≥ 2, ∀ t, t ≤ η ℓ - √((1+κ) log ℓ) √(ℓ η (1-η)) → Pr{Bin(ℓ,η) < t} ≤ C'/√ℓ`. -/
theorem binomLT_moderate {η κ : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hκ0 : 0 ≤ κ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ t : ℕ,
      (t : ℝ) ≤ η * ℓ - √((1 + κ) * Real.log ℓ) * √(ℓ * (η * (1 - η))) →
        binomLT ℓ η t ≤ C' / √(ℓ : ℝ) := by
  obtain ⟨C, hC⟩ := binomBE hη0 hη1
  have hη' : 0 < 1 - η := by linarith
  refine ⟨|C| + 1, by positivity, fun ℓ hℓ t ht => ?_⟩
  have hℓ2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hlog : 0 ≤ Real.log ℓ := Real.log_nonneg (by linarith)
  have hσ : 0 < √((ℓ : ℝ) * (η * (1 - η))) := Real.sqrt_pos.2 (by positivity)
  have hsqrt : 0 < √(ℓ : ℝ) := Real.sqrt_pos.2 hℓ0
  have hz : ((t : ℝ) - η * ℓ) / √((ℓ : ℝ) * (η * (1 - η))) ≤ -√((1 + κ) * Real.log ℓ) := by
    rw [div_le_iff₀ hσ]; linarith
  have h1 := (abs_le.1 (hC ℓ (by omega) t)).2
  have h2 := Φ_strictMono.monotone hz
  have h3 := Φ_neg_le_exp (Real.sqrt_nonneg ((1 + κ) * Real.log ℓ))
  have h4 : exp (-√((1 + κ) * Real.log ℓ) ^ 2 / 2) ≤ 1 / √(ℓ : ℝ) := by
    rw [Real.sq_sqrt (by positivity)]
    have h5 : -((1 + κ) * Real.log ℓ) / 2 ≤ -(Real.log ℓ / 2) := by nlinarith
    calc exp (-((1 + κ) * Real.log ℓ) / 2) ≤ exp (-(Real.log ℓ / 2)) := exp_le_exp.2 h5
      _ = 1 / √(ℓ : ℝ) := by rw [exp_neg, exp_half_log hℓ0, one_div]
  have h6 : C / √(ℓ : ℝ) ≤ |C| / √(ℓ : ℝ) :=
    div_le_div_of_nonneg_right (le_abs_self C) hsqrt.le
  have e : (|C| + 1) / √(ℓ : ℝ) = |C| / √(ℓ : ℝ) + 1 / √(ℓ : ℝ) := by ring
  rw [e]
  linarith

end QIQCOP
