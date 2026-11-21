import QIQCOP.StirlingWide

/-!
# Achievability under a mean photon-number constraint

`mean_ach`: for large `n` there is a code with mean photon number `≤ n N_S`, success `≥ 1 - ε`
and `log₂ M ≥ n g(x_ε) - √((1+κ) V_ε n ln n)`, where `x_ε = η N_S/(1-ε)` and
`V_ε = (1-η) x_ε g'(x_ε)²`. The input law is `(1-p) δ_0 + p δ_ℓ` with `p = 1 - ε + c/√n`,
`ℓ = ⌊n N_S / p⌋`.
-/

open Real Filter Finset

namespace QIQCOP

namespace MeanAsymp

lemma sum_two {ℓ : ℕ} (hℓ : ℓ ≠ 0) (q p : ℝ) (f : ℕ → ℝ) :
    ∑ j ∈ range (ℓ + 1), (if j = 0 then q else if j = ℓ then p else 0) * f j =
      q * f 0 + p * f ℓ := by
  have h : ∀ j, (if j = 0 then q else if j = ℓ then p else 0) * f j =
      (if j = 0 then q * f 0 else 0) + (if j = ℓ then p * f ℓ else 0) := by
    intro j
    by_cases h0 : j = 0
    · subst h0; simp [hℓ.symm]
    · by_cases h1 : j = ℓ
      · subst h1; simp [h0]
      · simp [h0, h1]
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

end MeanAsymp

theorem mean_ach {η Ns ε κ : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∀ᶠ n : ℕ in atTop, ∃ L' M : ℕ, 1 ≤ M ∧ ∃ C : Code n L' M, C.meanPhotons ≤ n * Ns ∧
      1 - ε ≤ C.success η ∧
        n * g (η * Ns / (1 - ε))
          - √((1 + κ) * ((1 - η) * (η * Ns / (1 - ε)) * gp (η * Ns / (1 - ε)) ^ 2) * n *
              Real.log n) ≤ Real.logb 2 M := by
  obtain ⟨C', hC'0, hC'⟩ := binomLT_moderate hη0 hη1 (κ := κ / 2) (by linarith)
  have he1 : 0 < 1 - ε := by linarith
  set e1 := 1 - ε with he1def
  set xe := η * Ns / e1 with hxe
  have hxe0 : 0 < xe := by positivity
  have hxee : xe * e1 = η * Ns := by rw [hxe]; field_simp
  have hη' : 0 < 1 - η := by linarith
  set w := (1 - η) * xe with hw
  have hw0 : 0 < w := by positivity
  set G := gp xe with hG
  have hG0 : 0 < G := gp_pos hxe0
  set a := 1 + κ / 2 with ha
  set m := 1 + 3 * κ / 4 with hm
  set d := 1 + κ with hd
  set δ := κ / 8 with hδ
  have ha0 : 0 < a := by rw [ha]; linarith
  have hm0 : 0 < m := by rw [hm]; linarith
  have hd0 : 0 < d := by rw [hd]; linarith
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hmd : √m < √d := Real.sqrt_lt_sqrt hm0.le (by rw [hm, hd]; linarith)
  have hsw : 0 < √w := Real.sqrt_pos.2 hw0
  have hma : a * (1 + δ) ≤ m := by
    have e : m - a * (1 + δ) = κ * (2 - κ) / 16 := by rw [ha, hm, hδ]; ring
    have : 0 ≤ κ * (2 - κ) / 16 := by
      have : 0 ≤ κ * (2 - κ) := mul_nonneg hκ0.le (by linarith)
      linarith
    linarith
  set c₁ := C' * √(2 / Ns) + 1 with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set A := xe * c₁ / e1 with hA
  have hA0 : 0 < A := by positivity
  set R := √m * √w + 1 with hR
  obtain ⟨B, hB0, hB⟩ := stirlingWide hxe0 R
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [hB, eventually_ge_atTop 1, SecondOrderLog.eventually_sqrt_ge (c₁ / ε),
    eventually_ge_atTop ⌈4 / Ns⌉₊, MeanAsymp.ev_log_ge (Real.log (Ns / e1) / δ),
    MeanAsymp.absorb A 0 (η + 1) (δ := 1) one_pos,
    MeanAsymp.sqrt_nlogn_le R (δ := xe) hxe0,
    MeanAsymp.absorb (G * A) (B + 1 / (2 * Real.log 2))
      (G * (η + 1) + Real.logb 2 (2 * Real.exp 1)) (δ := G * (√d - √m) * √w)
      (mul_pos (mul_pos hG0 (by linarith)) hsw),
    MeanAsymp.ev_log_ge 1] with n F0 F1 F2 F3 F4 F5 F6 F7 F8
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast F1
  have hn0 : (0 : ℝ) < n := by linarith
  set S := √((n : ℝ) * Real.log n) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set s := √(n : ℝ) with hs'
  have hs0 : 0 < s := Real.sqrt_pos.2 hn0
  have hss : s * s = n := Real.mul_self_sqrt hn0.le
  have hs1 : 1 ≤ s := by
    rw [hs', show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hnr
  have hlog0 : 0 ≤ Real.log n := by linarith
  have hnNs : 4 ≤ (n : ℝ) * Ns := by
    have h := Nat.ceil_le.1 F3
    rw [div_le_iff₀ hNs] at h; exact h
  -- the weight p
  set u := c₁ / s with hu
  have hu0 : 0 < u := by positivity
  have hus : u * s = c₁ := by rw [hu]; field_simp
  have huε : u ≤ ε := by
    rw [div_le_iff₀ hε0] at F2
    rw [hu, div_le_iff₀ hs0]; linarith only [F2]
  set p := e1 + u with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, he1def]; linarith only [huε]
  have hpe : e1 ≤ p := by rw [hp]; linarith only [hu0]
  -- the photon number ℓ
  set X := (n : ℝ) * Ns / p with hX
  have hXp : X * p = n * Ns := by rw [hX]; field_simp
  have hX0 : 0 < X := by positivity
  have hXlo : (n : ℝ) * Ns ≤ X := by
    rw [hX, le_div_iff₀ hp0]
    have : 0 ≤ (n : ℝ) * Ns := by positivity
    nlinarith only [this, hp1]
  have hXhi : X ≤ n * Ns / e1 := div_le_div_of_nonneg_left (by positivity) he1 hpe
  set ℓ := ⌊X⌋₊ with hℓ
  have hℓX : (ℓ : ℝ) ≤ X := Nat.floor_le hX0.le
  have hXℓ : X < ℓ + 1 := Nat.lt_floor_add_one X
  have hℓ3 : (3 : ℝ) < ℓ := by linarith only [hXℓ, hXlo, hnNs]
  have hℓ2 : 2 ≤ ℓ := by
    have : (2 : ℝ) ≤ ℓ := by linarith only [hℓ3]
    exact_mod_cast this
  have hℓne : ℓ ≠ 0 := by omega
  have hℓ0 : (0 : ℝ) < ℓ := by linarith only [hℓ3]
  have hℓhalf : (n : ℝ) * Ns / 2 ≤ ℓ := by linarith only [hXℓ, hXlo, hnNs]
  have hpℓ : p * ℓ ≤ n * Ns := by
    rw [← hXp, mul_comm]; exact mul_le_mul_of_nonneg_right hℓX hp0.le
  have hℓhi : (ℓ : ℝ) ≤ n * Ns / e1 := hℓX.trans hXhi
  -- the threshold
  set τ := η * ℓ - √(a * Real.log ℓ) * √(ℓ * (η * (1 - η))) with hτ
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg (by linarith only [hℓ3])
  have hlogℓ : Real.log ℓ ≤ (1 + δ) * Real.log n := by
    have h1 : Real.log ℓ ≤ Real.log (Ns / e1 * n) :=
      Real.log_le_log hℓ0 (by rw [show Ns / e1 * n = n * Ns / e1 by ring]; exact hℓhi)
    rw [Real.log_mul (by positivity) hn0.ne'] at h1
    rw [div_le_iff₀ hδ0] at F4
    linarith only [h1, F4]
  have hprod : (a * Real.log ℓ) * (ℓ * (η * (1 - η))) ≤ m * w * (n * Real.log n) := by
    have h1 : a * Real.log ℓ ≤ a * ((1 + δ) * Real.log n) :=
      mul_le_mul_of_nonneg_left hlogℓ ha0.le
    have h2 : (ℓ : ℝ) * (η * (1 - η)) ≤ w * n := by
      have := mul_le_mul_of_nonneg_right hℓhi (by positivity : 0 ≤ η * (1 - η))
      have e : (n : ℝ) * Ns / e1 * (η * (1 - η)) = w * n := by rw [hw, hxe]; ring
      rw [e] at this; exact this
    have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : a * (1 + δ) * (w * (n * Real.log n)) ≤ m * (w * (n * Real.log n)) :=
      mul_le_mul_of_nonneg_right hma (by positivity)
    calc _ ≤ a * ((1 + δ) * Real.log n) * (w * n) := h3
      _ = a * (1 + δ) * (w * (n * Real.log n)) := by ring
      _ ≤ m * (w * (n * Real.log n)) := h4
      _ = _ := by ring
  have hsq : √(a * Real.log ℓ) * √(ℓ * (η * (1 - η))) ≤ √m * √w * S := by
    have e1' : √m * √w * S = √(m * w * (n * Real.log n)) := by
      rw [Real.sqrt_mul (mul_nonneg hm0.le hw0.le) (n * Real.log n), Real.sqrt_mul hm0.le w]
    rw [e1', ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hprod
  have hηX : (n : ℝ) * xe - A * s ≤ η * X := by
    have h1 : ((n : ℝ) * xe - A * s) * p ≤ η * (n * Ns) := by
      have e : ((n : ℝ) * xe - A * s) * p =
          n * (xe * e1) + s * xe * (u * s) - xe * c₁ * s - xe * c₁ / e1 * (u * s) := by
        rw [hp, hA, ← hss]; field_simp; ring
      rw [e, hus, hxee]
      have : 0 ≤ xe * c₁ / e1 * c₁ := by positivity
      linarith only [this]
    calc (n : ℝ) * xe - A * s = ((n : ℝ) * xe - A * s) * p / p := by field_simp
      _ ≤ η * (n * Ns) / p := div_le_div_of_nonneg_right h1 hp0.le
      _ = η * X := by rw [hX]; ring
  have hηℓlo : (n : ℝ) * xe - A * s - η ≤ η * ℓ := by
    have : η * X < η * (ℓ + 1) := mul_lt_mul_of_pos_left hXℓ hη0
    linarith only [this, hηX]
  have hηℓhi : η * (ℓ : ℝ) ≤ n * xe := by
    have := mul_le_mul_of_nonneg_left hℓhi hη0.le
    have e : η * ((n : ℝ) * Ns / e1) = n * xe := by rw [hxe]; ring
    rw [e] at this; exact this
  rw [zero_mul, add_zero, one_mul] at F5
  have hRS : R * S = √m * √w * S + S := by rw [hR]; ring
  have hτlo : (n : ℝ) * xe - R * S + 1 ≤ τ := by
    rw [hτ, hRS]; linarith only [hsq, hηℓlo, F5]
  have hτ1 : 1 ≤ τ := by linarith only [hτlo, F6]
  have hτhi : τ ≤ η * ℓ := by
    rw [hτ]
    have : 0 ≤ √(a * Real.log ℓ) * √(ℓ * (η * (1 - η))) := by positivity
    linarith only [this]
  set t := ⌊τ⌋₊ with ht
  have htτ : (t : ℝ) ≤ τ := Nat.floor_le (by linarith only [hτ1])
  have hτt : τ < t + 1 := Nat.lt_floor_add_one τ
  have htℓ : t ≤ ℓ := by
    have h1 : η * (ℓ : ℝ) ≤ ℓ := by nlinarith only [hℓ0, hη1]
    have : (t : ℝ) ≤ ℓ := by linarith only [htτ, hτhi, h1]
    exact_mod_cast this
  have habs : |(t : ℝ) - n * xe| ≤ R * √((n : ℝ) * Real.log n) := by
    rw [abs_le]
    constructor
    · linarith only [hτt, hτlo]
    · have : 0 ≤ R * S := by rw [hRS]; positivity
      linarith only [htτ, hτhi, hηℓhi, this]
  have hSt := F0 t habs
  -- error of the law
  have hBL := hC' ℓ hℓ2 t htτ
  have hsℓ : s ≤ √(2 / Ns) * √(ℓ : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_mul_eq_mul_div, le_div_iff₀ hNs]; linarith only [hℓhalf]
  have hsℓ0 : 0 < √(ℓ : ℝ) := Real.sqrt_pos.2 hℓ0
  have hBL' : binomLT ℓ η t ≤ (c₁ - 1) / s := by
    refine hBL.trans ?_
    rw [div_le_div_iff₀ hsℓ0 hs0, hc₁]
    have := mul_le_mul_of_nonneg_left hsℓ hC'0
    linarith only [this]
  -- the message set
  have hD1 : (1 : ℝ) ≤ sectorDim n t := by
    unfold sectorDim; exact_mod_cast Nat.choose_pos (by omega)
  have he1' : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hee0 : 0 < Real.exp 1 := Real.exp_pos 1
  set v := 1 / s with hv
  have hv0 : 0 < v := by positivity
  have hv1 : v ≤ 1 := by rw [hv, div_le_one hs0]; exact hs1
  set z := v * sectorDim n t / Real.exp 1 with hz
  have hz0 : 0 < z := by positivity
  have hzD : z ≤ sectorDim n t := by
    rw [hz, div_le_iff₀ hee0]; nlinarith only [hv1, he1', hD1, hv0]
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
  have herrM : ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ v := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_right hMz hee0.le
    rw [hz] at this; field_simp at this; linarith
  -- the code
  set pl : ℕ → ℝ := fun j => if j = 0 then 1 - p else if j = ℓ then p else 0 with hpl
  have hpl0 : ∀ j, 0 ≤ pl j := by
    intro j; rw [hpl]; dsimp only
    split_ifs <;> linarith
  have hpl1 : ∑ j ∈ range (ℓ + 1), pl j = 1 := by
    have := MeanAsymp.sum_two hℓne (1 - p) p (fun _ => 1)
    simp only [mul_one] at this
    rw [hpl, this]; ring
  have hb0 : binomLT 0 η t ≤ 1 := BE.binomLT_le_one hη0 hη1 0 t
  have hbℓ0 : 0 ≤ binomLT ℓ η t := BE.binomLT_nonneg hη0 hη1 ℓ t
  have herr : ∑ j ∈ range (ℓ + 1), pl j * binomLT j η t +
      ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ ε := by
    rw [hpl, MeanAsymp.sum_two hℓne (1 - p) p (fun j => binomLT j η t)]
    have h1 : (1 - p) * binomLT 0 η t ≤ 1 - p :=
      mul_le_of_le_one_right (by linarith only [hp1]) hb0
    have h2 : p * binomLT ℓ η t ≤ binomLT ℓ η t := mul_le_of_le_one_left hbℓ0 hp1
    have h3 : (c₁ - 1) / s + v = u := by rw [hv, hu]; ring
    rw [hp, he1def] at h1
    linarith only [h1, h2, h3, hBL', herrM]
  obtain ⟨C, hC1, -, hC3⟩ := exists_lawCode hη0.le hη1.le F1 htℓ pl hpl0 hpl1 hM1 hMD herr
  refine ⟨ℓ, M, hM1, C, ?_, hC1, ?_⟩
  · rw [hC3, hpl, MeanAsymp.sum_two hℓne (1 - p) p (fun j => (j : ℝ))]
    simp only [Nat.cast_zero, mul_zero, zero_add]
    exact hpℓ
  -- the rate
  have hlogM : Real.logb 2 (z / 2) ≤ Real.logb 2 M :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hMz2
  have hlogv : Real.logb 2 v = -(1 / (2 * Real.log 2)) * Real.log n := by
    rw [SecondOrderLog.logb_two_eq, hv, Real.log_div one_ne_zero hs0.ne', Real.log_one, hs',
      Real.log_sqrt hn0.le]
    field_simp
    ring
  have hsplit : Real.logb 2 (z / 2) =
      Real.logb 2 (sectorDim n t) - Real.logb 2 (2 * Real.exp 1)
        - (1 / (2 * Real.log 2)) * Real.log n := by
    have e : z / 2 = sectorDim n t / (2 * Real.exp 1) * v := by rw [hz]; field_simp
    rw [e, Real.logb_mul (by positivity) hv0.ne', Real.logb_div (by positivity) (by positivity),
      hlogv]
    ring
  have hτlo' : (n : ℝ) * xe - √m * √w * S - A * s - η ≤ τ := by
    rw [hτ]; linarith only [hsq, hηℓlo]
  have htG : -(√m * √w * S + A * s + η + 1) * G ≤ ((t : ℝ) - n * xe) * G :=
    mul_le_mul_of_nonneg_right (by linarith only [hτt, hτlo']) hG0.le
  rw [MeanAsymp.sqrt_form hd0.le hw0.le hG0.le]
  rw [hsplit] at hlogM
  linarith only [hlogM, hSt, htG, F7]
end QIQCOP
