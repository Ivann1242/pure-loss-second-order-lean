import QIQCOP.LogConv

/-!
# Second-order achievability with `O(log n)` remainder, from Berry–Esseen

* `ach_numeric`: a threshold `t ≤ ⌈n N_S⌉` and a code size `M` with
  `(1-δ) Pr{Bin(L,η) < t} + 1/√n + (M-1) e / D_{n,t} ≤ (1-δ) Φ(q)` and
  `log₂ M ≥ n g(η N_S) + q √V_occ √n - A log n`.
* `ach_log`: codes with leakage `≤ δ` above the cutoff, error `(1-δ) Φ(q)`.
* `ach_log_cutoff`: codes inside the strict cutoff space, error `Φ(q)`.
-/

open Real Filter

namespace QIQCOP

open SecondOrderLog

set_option maxHeartbeats 2000000 in
/-- The numerical core of the achievability proof. -/
theorem ach_numeric {η Ns δ q : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hδ1 : δ < 1) (hBE : BinomBE η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n : ℕ in atTop, ∃ t M : ℕ, t ≤ cutoff Ns n ∧ 1 ≤ M ∧
      M ≤ (n + t - 1).choose t ∧
      (1 - δ) * binomLT (cutoff Ns n) η t + 1 / √(n : ℝ) +
        ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ (1 - δ) * Φ q ∧
      n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) - A * Real.log n ≤ Real.logb 2 M := by
  set x := η * Ns with hx
  have hx0 : 0 < x := mul_pos hη0 hNs
  have hgp := gp_pos hx0
  have hgs := gp_mul_sqrt_eq_sqrt_Vocc hη0 hη1 hNs
  set a := η * (1 - η) with ha
  have ha0 : 0 < a := mul_pos hη0 (by linarith)
  have hsa : 0 < √a := Real.sqrt_pos.2 ha0
  have hd : 0 < 1 - δ := by linarith
  have h1η : 0 < 1 - η := by linarith
  have hsN1 : 0 < √(Ns + 1) := Real.sqrt_pos.2 (by linarith)
  set K := 2 * √(Ns + 1) / (1 - δ) with hK
  obtain ⟨c, hc0, L₁, hL₁⟩ := binomLT_le_of_BE hη0 hη1 hBE q K
  set D := |q| * √a + c + 1 with hD
  have hD0 : 0 ≤ D := by positivity
  set sN := √(η * (1 - η) * Ns) with hsN
  have hsN0 : 0 ≤ sN := Real.sqrt_nonneg _
  set R := |q| * sN + D + η with hR
  obtain ⟨B, hB0, hB⟩ := stirlingExpansion hx0 R
  set c1 := Real.logb 2 (1 / (2 * Real.exp 1)) with hc1
  set c2 := 1 / Real.log 2 with hc2
  have hc20 : 0 < c2 := by rw [hc2]; exact one_div_pos.2 (Real.log_pos (by norm_num))
  refine ⟨B + D * gp x + |c1| + c2, by positivity, ?_⟩
  filter_upwards [hB, eventually_ge_atTop 3,
    (tendsto_cutoff hNs).eventually (eventually_ge_atTop L₁),
    eventually_sqrt_cutoff_ge hNs ((|q| * √a + c) / η),
    eventually_sqrt_cutoff_ge hNs (|q| * √a / (1 - η))] with n hSt hn3 hnL hnW1 hnW2
  rw [← hx] at hSt
  have hn1 : 1 ≤ n := by omega
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlog := one_le_log_of_three_le hn3
  obtain ⟨hLlo, hLhi, hσlo, hσhi, hsLn⟩ := cutoff_facts hη0 hη1 hNs hn1
  rw [← ha] at hσlo hσhi
  rw [← hsN] at hσlo hσhi
  set L := cutoff Ns n with hLdef
  set Lr : ℝ := (L : ℝ) with hLr
  set sn := √(n : ℝ) with hsn
  have hsn1 : 1 ≤ sn := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hLr0 : 0 < Lr := lt_of_lt_of_le (by positivity) hLlo
  have hL1 : 1 ≤ L := by exact_mod_cast (show (0 : ℝ) < L from hLr0)
  have hLr1 : (1 : ℝ) ≤ Lr := Nat.one_le_cast.2 hL1
  set sL := √Lr with hsL
  have hsL0 : 0 < sL := Real.sqrt_pos.2 hLr0
  have hsL1 : 1 ≤ sL := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hLr1
  have hsL2 : sL * sL = Lr := Real.mul_self_sqrt hLr0.le
  set σ := √(Lr * a) with hσ
  have hσe : σ = sL * √a := Real.sqrt_mul hLr0.le _
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  set s₀ := sn * sN with hs₀
  have hs₀0 : 0 ≤ s₀ := by positivity
  obtain ⟨hqlo, hqhi⟩ := mul_between (q := q) hσlo hσhi
  have hqabs1 : -(|q| * σ) ≤ q * σ := by
    have := neg_abs_le q; nlinarith
  have hqabs2 : q * σ ≤ |q| * σ := by
    have := le_abs_self q; nlinarith
  have hqs1 : -(|q| * s₀) ≤ q * s₀ := by
    have := neg_abs_le q; nlinarith
  have hqs2 : q * s₀ ≤ |q| * s₀ := by
    have := le_abs_self q; nlinarith
  have hqa0 : 0 ≤ |q| * √a := by positivity
  -- the threshold
  set y := η * Lr + q * σ - c with hy
  have hy0 : 0 ≤ y := by
    rw [div_le_iff₀ hη0] at hnW1
    have h2 : (|q| * √a + c) * sL ≤ η * Lr := by
      rw [← hsL2]
      have := mul_le_mul_of_nonneg_right hnW1 hsL0.le
      nlinarith
    have h3 : c ≤ c * sL := le_mul_of_one_le_right hc0 hsL1
    have h4 : |q| * σ = |q| * √a * sL := by rw [hσe]; ring
    nlinarith
  have hyL : y ≤ Lr := by
    rw [div_le_iff₀ h1η] at hnW2
    have h2 : |q| * √a * sL ≤ (1 - η) * Lr := by
      rw [← hsL2]
      have := mul_le_mul_of_nonneg_right hnW2 hsL0.le
      nlinarith
    have h4 : |q| * σ = |q| * √a * sL := by rw [hσe]; ring
    nlinarith
  set t := ⌊y⌋₊ with ht
  have hty : (t : ℝ) ≤ y := Nat.floor_le hy0
  have hty1 : y - 1 < t := Nat.sub_one_lt_floor y
  have htL : t ≤ L := by
    have : (t : ℝ) ≤ L := hty.trans hyL
    exact_mod_cast this
  have hP := hL₁ L hnL t hty
  -- slack
  set u := 1 / sn with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu, div_le_one (by linarith)]; exact hsn1
  have hKu : 2 * u ≤ (1 - δ) * (K / sL) := by
    have e : (1 - δ) * (K / sL) = 2 * √(Ns + 1) / sL := by rw [hK]; field_simp
    rw [e, hu, le_div_iff₀ hsL0]
    have h1 : 2 * (1 / sn) * sL ≤ 2 * (1 / sn) * (sn * √(Ns + 1)) :=
      mul_le_mul_of_nonneg_left hsLn (by positivity)
    have h2 : 2 * (1 / sn) * (sn * √(Ns + 1)) = 2 * √(Ns + 1) := by field_simp
    linarith
  have hPt : (1 - δ) * binomLT L η t ≤ (1 - δ) * Φ q - 2 * u := by
    have := mul_le_mul_of_nonneg_left hP hd.le
    linarith
  -- bounds on t - n x
  have e3 : (n : ℝ) * x = η * (n * Ns) := by rw [hx]; ring
  have e4 : η * (n * Ns) ≤ η * Lr := mul_le_mul_of_nonneg_left hLlo hη0.le
  have e5 : η * Lr ≤ η * (n * Ns + 1) := mul_le_mul_of_nonneg_left hLhi.le hη0.le
  have htlow : q * s₀ - D ≤ (t : ℝ) - n * x := by rw [hD]; linarith
  have hthigh : (t : ℝ) - n * x ≤ q * s₀ + |q| * √a + η := by linarith
  have hwin : |(t : ℝ) - n * x| ≤ R * sn := by
    have e : R * sn = |q| * s₀ + (D + η) * sn := by rw [hR, hs₀]; ring
    have k1 : D + η ≤ (D + η) * sn := le_mul_of_one_le_right (by positivity) hsn1
    rw [abs_le, e, hD] at *
    constructor <;> linarith
  have hSt' := hSt t hwin
  have hcoef : q * √(Vocc η Ns) * sn - D * gp x ≤ ((t : ℝ) - n * x) * gp x := by
    have h := mul_le_mul_of_nonneg_right htlow hgp.le
    have e : (q * s₀ - D) * gp x = q * √(Vocc η Ns) * sn - D * gp x := by
      rw [← hgs, hs₀, hsN]; ring
    linarith
  -- the code size M = max 1 ⌊u D_t / e⌋
  have hD1 : (1 : ℝ) ≤ sectorDim n t := by
    unfold sectorDim; exact_mod_cast Nat.choose_pos (by omega)
  have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set z := u * sectorDim n t / Real.exp 1 with hz
  have hz0 : 0 < z := by positivity
  have hzD : z ≤ sectorDim n t := by
    rw [hz, div_le_iff₀ he0]; nlinarith
  set M : ℕ := max 1 ⌊z⌋₊ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMz : (M : ℝ) - 1 ≤ z := by
    rcases le_total 1 ⌊z⌋₊ with h | h
    · rw [hM, max_eq_right h]; have := Nat.floor_le hz0.le; linarith
    · rw [hM, max_eq_left h]; push_cast; linarith
  have hMz2 : z / 2 ≤ M := by
    have h1 : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have h2 : (⌊z⌋₊ : ℝ) ≤ M := by exact_mod_cast le_max_right 1 ⌊z⌋₊
    have h3 := Nat.sub_one_lt_floor z
    rcases lt_or_ge z 2 with h | h <;> linarith
  have hMD : M ≤ (n + t - 1).choose t := by
    have : (M : ℝ) ≤ sectorDim n t := by
      rcases le_total 1 ⌊z⌋₊ with h | h
      · rw [hM, max_eq_right h]; exact (Nat.floor_le hz0.le).trans hzD
      · rw [hM, max_eq_left h]; push_cast; exact hD1
    unfold sectorDim at this; exact_mod_cast this
  have herr : ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ u := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_right hMz he0.le
    rw [hz] at this; field_simp at this; linarith
  refine ⟨t, M, htL, hM1, hMD, by linarith, ?_⟩
  -- log₂ M ≥ log₂ (z/2) = log₂ D_t + log₂ (1/(2e)) - ½ log₂ n
  have hlogM : Real.logb 2 (z / 2) ≤ Real.logb 2 M :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hMz2
  have hlogu : Real.logb 2 u = -(c2 / 2) * Real.log n := by
    have hsn0 : sn ≠ 0 := by linarith
    rw [logb_two_eq, hu, Real.log_div one_ne_zero hsn0, Real.log_one, hsn,
      Real.log_sqrt (by linarith), hc2]
    ring
  have hsplit : Real.logb 2 (z / 2) =
      Real.logb 2 (sectorDim n t) + c1 - (c2 / 2) * Real.log n := by
    have e : z / 2 = sectorDim n t * (1 / (2 * Real.exp 1)) * u := by rw [hz]; field_simp
    rw [e, Real.logb_mul (by positivity) hu0.ne', Real.logb_mul (by positivity) (by positivity),
      hlogu, hc1]
    ring
  have habs1 : -|c1| ≤ c1 := neg_abs_le c1
  have hlog0 : 0 ≤ Real.log n := by linarith
  have hc : D * gp x + |c1| ≤ (D * gp x + |c1|) * Real.log n :=
    le_mul_of_one_le_right (by positivity) hlog
  have hc2' : c2 / 2 * Real.log n ≤ c2 * Real.log n := by nlinarith
  have hexp : (B + D * gp x + |c1| + c2) * Real.log n =
      B * Real.log n + (D * gp x + |c1|) * Real.log n + c2 * Real.log n := by ring
  rw [hsplit] at hlogM
  rw [hexp]
  linarith

/-- **Second-order achievability with `O(log n)` remainder and leakage `≤ δ`**, assuming
Berry–Esseen. -/
theorem ach_log {η Ns δ q : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hBE : BinomBE η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n : ℕ in atTop, ∃ L' M : ℕ, 1 ≤ M ∧ cutoff Ns n ≤ L' ∧
      (∃ C : Code n L' M, 1 - (1 - δ) * Φ q ≤ C.success η ∧ C.leak (cutoff Ns n) ≤ δ) ∧
      n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) - A * Real.log n ≤ Real.logb 2 M := by
  obtain ⟨A, hA0, hA⟩ := ach_numeric (δ := δ) (q := q) hη0 hη1 hNs hδ1 hBE
  set a := η * (1 - η) with ha
  have ha0 : 0 < a := mul_pos hη0 (by linarith)
  set c : ℕ := ⌈2 / η⌉₊ with hcdef
  have hcη : 2 ≤ η * c := by
    have h : 2 / η ≤ c := Nat.le_ceil _
    rw [div_le_iff₀ hη0] at h; linarith
  have hc1 : 1 ≤ c := by
    have : (0 : ℝ) < c := by
      by_contra h
      have h0 : (c : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg c)
      rw [h0] at hcη; linarith
    exact_mod_cast this
  refine ⟨A, hA0, ?_⟩
  filter_upwards [hA, eventually_ge_atTop 1, eventually_sqrt_ge (c * a / Ns)] with n hn hn1 hnW
  obtain ⟨t, M, htL, hM1, hMD, herr, hlogM⟩ := hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set L := cutoff Ns n with hLdef
  have hLlo : (n : ℝ) * Ns ≤ (L : ℝ) := Nat.le_ceil _
  have hLr0 : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hLlo
  have hL1 : 1 ≤ L := by exact_mod_cast hLr0
  set sn := √(n : ℝ) with hsn
  have hsn0 : 0 < sn := Real.sqrt_pos.2 (by linarith)
  have hsn2 : sn * sn = n := Real.mul_self_sqrt (by linarith)
  have hbig : 2 / (2 / sn) * (c * a) ≤ (L : ℝ) := by
    rw [div_le_iff₀ hNs] at hnW
    have e : 2 / (2 / sn) * (c * a) = sn * (c * a) := by field_simp
    rw [e]
    have h1 : sn * (c * a) ≤ sn * (sn * Ns) := mul_le_mul_of_nonneg_left hnW hsn0.le
    have h2 : sn * (sn * Ns) = n * Ns := by rw [← mul_assoc, hsn2]
    linarith
  have hfar : binomLT (c * L) η t ≤ 2 / sn / 2 :=
    binomLT_far_le hη0 hη1 (by positivity) hL1 hcη hbig htL
  have hfar0 : 0 ≤ binomLT (c * L) η t :=
    Finset.sum_nonneg fun k _ => binomPMF_nonneg hη0.le hη1.le k
  have hLL' : L ≤ c * L := Nat.le_mul_of_pos_left L hc1
  have hfar' : δ * binomLT (c * L) η t ≤ 1 / sn := by
    have e : 2 / sn / 2 = 1 / sn := by field_simp
    rw [e] at hfar
    nlinarith
  obtain ⟨C, hC1, hC2⟩ := exists_leakCode (L := c * L) (ε := (1 - δ) * Φ q) hη0.le hη1.le hn1
    htL hLL' hδ0 hδ1.le hM1 hMD (by linarith)
  exact ⟨c * L, M, hM1, hLL', ⟨C, hC1, hC2⟩, hlogM⟩

/-- **Second-order achievability with `O(log n)` remainder inside the strict cutoff space**,
assuming Berry–Esseen. -/
theorem ach_log_cutoff {η Ns q : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hBE : BinomBE η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n : ℕ in atTop, ∃ M : ℕ, 1 ≤ M ∧
      (∃ C : Code n (cutoff Ns n) M, 1 - Φ q ≤ C.success η) ∧
      n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) - A * Real.log n ≤ Real.logb 2 M := by
  obtain ⟨A, hA0, hA⟩ := ach_numeric (δ := 0) (q := q) hη0 hη1 hNs one_pos hBE
  refine ⟨A, hA0, ?_⟩
  filter_upwards [hA, eventually_ge_atTop 1] with n hn hn1
  obtain ⟨t, M, htL, hM1, hMD, herr, hlogM⟩ := hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hu0 : 0 < 1 / √(n : ℝ) := by positivity
  simp only [sub_zero, one_mul] at herr
  exact ⟨M, hM1, exists_code hη0.le hη1.le hn1 htL hM1 hMD (by linarith), hlogM⟩

end QIQCOP
