import QIQCOP.MainGeneral

/-!
# Upper Stirling bound and the quantile threshold step for the converse

* `logb_choose_le`: exact bound `log₂ C(n+k,k) ≤ n g(x) + (k - n x) g'(x)`.
* `converse_threshold`: the CLT thresholds `r_n` satisfy `r_n - n x ≤ (z √(η(1-η)N_S) + τ) √n`.
* `binomLT_cutoff_tendsto`: `Pr{K < r_n} → Φ z`.
* `gp_mul_sqrt_eq_sqrt_Vocc`: `g'(ηN_S) √(η(1-η)N_S) = √V_occ`.
-/

open Real Filter Topology

namespace QIQCOP

/-- `C(n+k,k) p^k (1-p)^n ≤ 1` for `0 ≤ p ≤ 1`. -/
lemma choose_mul_pow_le_one (n k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((n + k).choose k : ℝ) * p ^ k * (1 - p) ^ n ≤ 1 := by
  have h := add_pow p (1 - p) (n + k)
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  have hq : 0 ≤ 1 - p := by linarith
  have hmem : k ∈ Finset.range (n + k + 1) := by simp
  have := Finset.single_le_sum (f := fun m => p ^ m * (1 - p) ^ (n + k - m) * ((n + k).choose m : ℝ))
    (fun i _ => by positivity) hmem
  simp only [Nat.add_sub_cancel] at this
  linarith

/-- Upper bound on the dimension of the ≤k photon space:
`log₂ C(n+k,k) ≤ n g(x) + (k - n x) g'(x)`. -/
theorem logb_choose_le (n k : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.logb 2 ((n + k).choose k : ℝ) ≤ n * g x + ((k : ℝ) - n * x) * gp x := by
  have hx1 : 0 < x + 1 := by linarith
  have hp0 : 0 < x / (x + 1) := by positivity
  have hp1 : x / (x + 1) ≤ 1 := by rw [div_le_one hx1]; linarith
  have h := choose_mul_pow_le_one n k hp0.le hp1
  have hq : 1 - x / (x + 1) = 1 / (x + 1) := by field_simp; ring
  rw [hq] at h
  have hC : (0 : ℝ) < ((n + k).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left k n)
  have hlog := Real.logb_nonpos (b := 2) (by norm_num) (by positivity) h
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul hC.ne' (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_div hx.ne' hx1.ne',
    Real.logb_div one_ne_zero hx1.ne', Real.logb_one] at hlog
  have hgp : gp x = Real.logb 2 (x + 1) - Real.logb 2 x := by
    unfold gp
    rw [← Real.logb_div hx1.ne' hx.ne']
    congr 1
    field_simp
  rw [hgp]
  unfold g
  nlinarith [hlog]

/-- `g'(ηN_S) √(η(1-η)N_S) = √V_occ`. -/
theorem gp_mul_sqrt_eq_sqrt_Vocc {η Ns : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns) :
    gp (η * Ns) * Real.sqrt (η * (1 - η) * Ns) = Real.sqrt (Vocc η Ns) := by
  have hg := gp_pos (mul_pos hη0 hNs)
  have h1 : 0 < 1 - η := by linarith
  unfold Vocc
  rw [Real.sqrt_mul (x := η * (1 - η) * Ns) (by positivity), Real.sqrt_sq hg.le, mul_comm]

/-- `Pr{K < r_n} → Φ z` along `L = ⌈n N_S⌉`. -/
theorem binomLT_cutoff_tendsto {η Ns : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns) (z : ℝ) :
    Filter.Tendsto (fun n : ℕ => binomLT (cutoff Ns n) η
      ⌈η * (cutoff Ns n : ℝ) + z * Real.sqrt ((cutoff Ns n : ℝ) * (η * (1 - η)))⌉₊)
      Filter.atTop (nhds (Φ z)) :=
  (binomLT_tendsto hη0 hη1 z).comp (tendsto_cutoff hNs)

/-- Thresholds `r_n := ⌈η L + z √(L η(1-η))⌉₊` satisfy
`r_n - n x ≤ (z √(η(1-η) N_S) + τ) √n` for large `n`. -/
theorem converse_threshold {η Ns : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns) (z τ : ℝ)
    (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((⌈η * (cutoff Ns n : ℝ) + z * Real.sqrt ((cutoff Ns n : ℝ) * (η * (1 - η)))⌉₊ : ℕ) : ℝ)
          - n * (η * Ns)
        ≤ (z * Real.sqrt (η * (1 - η) * Ns) + τ) * Real.sqrt n := by
  have h1 : 0 < 1 - η := by linarith
  set c : ℝ := η * (1 - η) with hc
  have hc0 : 0 < c := by positivity
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hx : 0 < η * Ns := mul_pos hη0 hNs
  filter_upwards [hsqrt.eventually_ge_atTop ((η + 1 + |z| * Real.sqrt c) / τ),
    hsqrt.eventually_ge_atTop (|z| * Real.sqrt (c * Ns) / (η * Ns))] with n hn1 hn2
  rw [div_le_iff₀ hτ] at hn1
  rw [div_le_iff₀ hx] at hn2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0
  have hsn0 := Real.sqrt_nonneg (n : ℝ)
  have hzle : z ≤ |z| := le_abs_self z
  have hzge : -|z| ≤ z := neg_abs_le z
  have hsc0 := Real.sqrt_nonneg (c * Ns)
  set L : ℝ := (cutoff Ns n : ℝ) with hL
  have hLlo : (n : ℝ) * Ns ≤ L := Nat.le_ceil _
  have hLhi : L < n * Ns + 1 := Nat.ceil_lt_add_one (by positivity)
  set a : ℝ := η * L + z * Real.sqrt (L * c) with ha
  by_cases ha0 : 0 ≤ a
  · have hr : ((⌈a⌉₊ : ℕ) : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
    -- bound z * √(L c)
    have hkey : z * Real.sqrt (L * c) ≤
        z * Real.sqrt (c * Ns) * Real.sqrt n + |z| * Real.sqrt c := by
      have hid : Real.sqrt (n * Ns * c) = Real.sqrt (c * Ns) * Real.sqrt n := by
        rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
      have hlo : Real.sqrt (c * Ns) * Real.sqrt n ≤ Real.sqrt (L * c) := by
        rw [← hid]; exact Real.sqrt_le_sqrt (by nlinarith)
      have hhi : Real.sqrt (L * c) ≤ Real.sqrt (c * Ns) * Real.sqrt n + Real.sqrt c := by
        rw [← hid]
        refine le_trans (Real.sqrt_le_sqrt ?_) (sqrt_add_le _ _ (by positivity) hc0.le)
        nlinarith
      have hsc := Real.sqrt_nonneg c
      rcases le_total 0 z with hz | hz
      · rw [abs_of_nonneg hz]; nlinarith
      · have : 0 ≤ |z| * Real.sqrt c := by positivity
        nlinarith
    have : η * L ≤ η * (n * Ns + 1) := by nlinarith
    nlinarith
  · have hr : ⌈a⌉₊ = 0 := Nat.ceil_eq_zero.2 (not_le.1 ha0).le
    rw [hr]
    simp only [Nat.cast_zero, zero_sub]
    have h3 : 0 ≤ (Real.sqrt n * (η * Ns) + z * Real.sqrt (c * Ns)) * Real.sqrt n := by
      apply mul_nonneg _ hsn0
      nlinarith
    have h4 : 0 ≤ τ * Real.sqrt n := by positivity
    rw [show η * (1 - η) * Ns = c * Ns by rw [hc]]
    nlinarith

end QIQCOP

