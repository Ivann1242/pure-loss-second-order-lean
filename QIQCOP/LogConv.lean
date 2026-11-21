import QIQCOP.BEDefs
import QIQCOP.ConverseMain
import QIQCOP.LeakAch

/-!
# Second-order converse with `O(log n)` remainder, from Berry–Esseen

* `SecondOrderLog.Φ_sub_ge`, `SecondOrderLog.Φ_slope`: the standard normal CDF has slope bounded
  below near any point.
* `SecondOrderLog.binomLT_le_of_BE`, `SecondOrderLog.binomLT_ge_of_BE`: explicit thresholds
  `η L + q √(L η(1-η)) ∓ c` at which `Pr{Bin(L, η) < t}` is below / above `Φ(q) ∓ K/√L`.
* `converse_log`: for codes with leakage `≤ δ + B/√n` above `⌈n N_S⌉` and error `(1-δ) Φ(q)`,
  `log₂ M ≤ n g(η N_S) + q √V_occ √n + A log n`.
-/

open MeasureTheory ProbabilityTheory Real Filter

namespace QIQCOP

namespace SecondOrderLog

/-! ### The normal CDF -/

lemma Φ_pos (q : ℝ) : 0 < Φ q := by
  have h1 := Φ_strictMono (show q - 1 < q by linarith)
  have h0 : 0 ≤ Φ (q - 1) := ENNReal.toReal_nonneg
  linarith

lemma Φ_lt_one (q : ℝ) : Φ q < 1 :=
  lt_of_lt_of_le (Φ_strictMono (show q < q + 1 by linarith)) (Φ_le_one _)

/-- Lower bound on increments of `Φ` from a lower bound on the Gaussian density. -/
lemma Φ_sub_ge {a b K : ℝ} (hab : a ≤ b) (hK : ∀ x ∈ Set.Ioc a b, |x| ≤ K) :
    (√(2 * π))⁻¹ * Real.exp (-K ^ 2 / 2) * (b - a) ≤ Φ b - Φ a := by
  set m : ℝ := (√(2 * π))⁻¹ * Real.exp (-K ^ 2 / 2) with hm
  have hm0 : 0 ≤ m := by positivity
  have hpdf : ∀ x ∈ Set.Ioc a b, ENNReal.ofReal m ≤ gaussianPDF 0 1 x := by
    intro x hx
    rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Real.exp_le_exp]
    have h := hK x hx
    have h2 : x ^ 2 ≤ K ^ 2 := sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
    linarith
  have hle : ENNReal.ofReal (m * (b - a)) ≤ gaussianReal 0 1 (Set.Ioc a b) := by
    rw [gaussianReal_apply _ one_ne_zero]
    calc ENNReal.ofReal (m * (b - a)) = ENNReal.ofReal m * ENNReal.ofReal (b - a) :=
          ENNReal.ofReal_mul hm0
      _ = ∫⁻ _ in Set.Ioc a b, ENNReal.ofReal m := by
          rw [setLIntegral_const, Real.volume_Ioc]
      _ ≤ ∫⁻ x in Set.Ioc a b, gaussianPDF 0 1 x := setLIntegral_mono' measurableSet_Ioc hpdf
  have h1 : m * (b - a) ≤ (gaussianReal 0 1).real (Set.Ioc a b) := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hle
  rw [Φ_eq, Φ_eq, ← Set.Iic_union_Ioc_eq_Iic hab,
    measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
  linarith

/-- `Φ` has slope at least `m > 0` on `[q - 1, q + 1]`. -/
lemma Φ_slope (q : ℝ) : ∃ m : ℝ, 0 < m ∧ ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
    m * h ≤ Φ (q + h) - Φ q ∧ m * h ≤ Φ q - Φ (q - h) := by
  refine ⟨(√(2 * π))⁻¹ * Real.exp (-(|q| + 1) ^ 2 / 2), by positivity, fun h h0 h1 => ⟨?_, ?_⟩⟩
  · have := Φ_sub_ge (a := q) (b := q + h) (K := |q| + 1) (by linarith) (by
      intro x hx
      have hq := abs_le.1 (le_refl |q|)
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
    simpa using this
  · have := Φ_sub_ge (a := q - h) (b := q) (K := |q| + 1) (by linarith) (by
      intro x hx
      have hq := abs_le.1 (le_refl |q|)
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
    simpa using this

/-! ### Thresholds from Berry–Esseen -/

/-- Below `η L + q σ_L - c` the binomial CDF is at most `Φ(q) - K/√L`. -/
theorem binomLT_le_of_BE {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hBE : BinomBE η) (q K : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ L₁ : ℕ, ∀ L : ℕ, L₁ ≤ L → ∀ t : ℕ,
      (t : ℝ) ≤ η * L + q * √((L : ℝ) * (η * (1 - η))) - c →
        binomLT L η t ≤ Φ q - K / √(L : ℝ) := by
  obtain ⟨C, hC⟩ := hBE
  obtain ⟨m, hm0, hm⟩ := Φ_slope q
  set a := η * (1 - η) with ha
  have ha0 : 0 < a := mul_pos hη0 (by linarith)
  have hsa : 0 < √a := Real.sqrt_pos.2 ha0
  set c' := (|C| + |K|) / m with hc'
  have hc'0 : 0 ≤ c' := by positivity
  refine ⟨c' * √a, by positivity, max 1 ⌈c' ^ 2⌉₊, fun L hL t ht => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLc : c' ^ 2 ≤ L := by
    have h1 : c' ^ 2 ≤ (⌈c' ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈c' ^ 2⌉₊ : ℕ) : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
    linarith
  set sL := √(L : ℝ) with hsL
  have hsL0 : 0 < sL := Real.sqrt_pos.2 (by linarith)
  have hcs : c' ≤ sL := Real.le_sqrt_of_sq_le hLc
  have hσ : √((L : ℝ) * a) = sL * √a := Real.sqrt_mul (by linarith) _
  rw [hσ] at ht
  have hσ0 : 0 < sL * √a := by positivity
  set h := c' / sL with hh
  have hh0 : 0 ≤ h := by positivity
  have hh1 : h ≤ 1 := by rw [hh, div_le_one hsL0]; exact hcs
  have hz : ((t : ℝ) - η * L) / (sL * √a) ≤ q - h := by
    rw [div_le_iff₀ hσ0]
    have : (q - h) * (sL * √a) = q * (sL * √a) - c' * √a := by
      rw [hh]; field_simp
    rw [this]; linarith
  have hΦ : Φ (((t : ℝ) - η * L) / (sL * √a)) ≤ Φ q - (|C| + |K|) / sL := by
    have h1 := Φ_strictMono.monotone hz
    have h2 := (hm h hh0 hh1).2
    have h3 : m * h = (|C| + |K|) / sL := by rw [hh, hc']; field_simp
    linarith
  have hbe := (abs_le.1 (hC L hL1 t)).2
  rw [hσ] at hbe
  have e1 : C / sL ≤ |C| / sL := div_le_div_of_nonneg_right (le_abs_self C) hsL0.le
  have e2 : K / sL ≤ |K| / sL := div_le_div_of_nonneg_right (le_abs_self K) hsL0.le
  have e3 : (|C| + |K|) / sL = |C| / sL + |K| / sL := add_div _ _ _
  linarith

/-- Above `η L + q σ_L + c` the binomial CDF is at least `Φ(q) + K/√L`. -/
theorem binomLT_ge_of_BE {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hBE : BinomBE η) (q K : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ L₁ : ℕ, ∀ L : ℕ, L₁ ≤ L → ∀ t : ℕ,
      η * L + q * √((L : ℝ) * (η * (1 - η))) + c ≤ (t : ℝ) →
        Φ q + K / √(L : ℝ) ≤ binomLT L η t := by
  obtain ⟨C, hC⟩ := hBE
  obtain ⟨m, hm0, hm⟩ := Φ_slope q
  set a := η * (1 - η) with ha
  have ha0 : 0 < a := mul_pos hη0 (by linarith)
  have hsa : 0 < √a := Real.sqrt_pos.2 ha0
  set c' := (|C| + |K|) / m with hc'
  have hc'0 : 0 ≤ c' := by positivity
  refine ⟨c' * √a, by positivity, max 1 ⌈c' ^ 2⌉₊, fun L hL t ht => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLc : c' ^ 2 ≤ L := by
    have h1 : c' ^ 2 ≤ (⌈c' ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈c' ^ 2⌉₊ : ℕ) : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
    linarith
  set sL := √(L : ℝ) with hsL
  have hsL0 : 0 < sL := Real.sqrt_pos.2 (by linarith)
  have hcs : c' ≤ sL := Real.le_sqrt_of_sq_le hLc
  have hσ : √((L : ℝ) * a) = sL * √a := Real.sqrt_mul (by linarith) _
  rw [hσ] at ht
  have hσ0 : 0 < sL * √a := by positivity
  set h := c' / sL with hh
  have hh0 : 0 ≤ h := by positivity
  have hh1 : h ≤ 1 := by rw [hh, div_le_one hsL0]; exact hcs
  have hz : q + h ≤ ((t : ℝ) - η * L) / (sL * √a) := by
    rw [le_div_iff₀ hσ0]
    have : (q + h) * (sL * √a) = q * (sL * √a) + c' * √a := by
      rw [hh]; field_simp
    rw [this]; linarith
  have hΦ : Φ q + (|C| + |K|) / sL ≤ Φ (((t : ℝ) - η * L) / (sL * √a)) := by
    have h1 := Φ_strictMono.monotone hz
    have h2 := (hm h hh0 hh1).1
    have h3 : m * h = (|C| + |K|) / sL := by rw [hh, hc']; field_simp
    linarith
  have hbe := (abs_le.1 (hC L hL1 t)).1
  rw [hσ] at hbe
  have e1 : C / sL ≤ |C| / sL := div_le_div_of_nonneg_right (le_abs_self C) hsL0.le
  have e2 : K / sL ≤ |K| / sL := div_le_div_of_nonneg_right (le_abs_self K) hsL0.le
  have e3 : (|C| + |K|) / sL = |C| / sL + |K| / sL := add_div _ _ _
  linarith

/-! ### Elementary facts about the cutoff -/

lemma eventually_sqrt_cutoff_ge {Ns : ℝ} (hNs : 0 < Ns) (W : ℝ) :
    ∀ᶠ n : ℕ in atTop, W ≤ √(cutoff Ns n : ℝ) :=
  (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_cutoff hNs))).eventually_ge_atTop W

lemma eventually_sqrt_ge (W : ℝ) : ∀ᶠ n : ℕ in atTop, W ≤ √(n : ℝ) :=
  (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop W

/-- Bounds relating `L = ⌈n N_S⌉` and `σ_L = √(L η(1-η))` to `n`. -/
lemma cutoff_facts {η Ns : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Ns ≤ (cutoff Ns n : ℝ) ∧ (cutoff Ns n : ℝ) < n * Ns + 1 ∧
    √(n : ℝ) * √(η * (1 - η) * Ns) ≤ √((cutoff Ns n : ℝ) * (η * (1 - η))) ∧
    √((cutoff Ns n : ℝ) * (η * (1 - η))) ≤ √(n : ℝ) * √(η * (1 - η) * Ns) + √(η * (1 - η)) ∧
    √(cutoff Ns n : ℝ) ≤ √(n : ℝ) * √(Ns + 1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha0 : 0 < η * (1 - η) := mul_pos hη0 (by linarith)
  have hL1 : (n : ℝ) * Ns ≤ (cutoff Ns n : ℝ) := Nat.le_ceil _
  have hL2 : (cutoff Ns n : ℝ) < n * Ns + 1 := Nat.ceil_lt_add_one (by positivity)
  have hid : √((n : ℝ) * (η * (1 - η) * Ns)) = √(n : ℝ) * √(η * (1 - η) * Ns) :=
    Real.sqrt_mul (by linarith) _
  refine ⟨hL1, hL2, ?_, ?_, ?_⟩
  · rw [← hid]; exact Real.sqrt_le_sqrt (by nlinarith)
  · rw [← hid]
    refine le_trans (Real.sqrt_le_sqrt ?_) (sqrt_add_le _ _ (by positivity) ha0.le)
    nlinarith
  · rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt (by nlinarith)

lemma mul_between {q σ s₀ d : ℝ} (h1 : s₀ ≤ σ) (h2 : σ ≤ s₀ + d) :
    q * s₀ - |q| * d ≤ q * σ ∧ q * σ ≤ q * s₀ + |q| * d := by
  have hd : 0 ≤ d := by linarith
  rcases le_total 0 q with hq | hq
  · rw [abs_of_nonneg hq]; constructor <;> nlinarith
  · rw [abs_of_nonpos hq]; constructor <;> nlinarith

lemma one_le_log_of_three_le {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log (n : ℝ) := by
  have h : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9; linarith

lemma logb_two_eq (x : ℝ) : Real.logb 2 x = 1 / Real.log 2 * Real.log x := by
  rw [← Real.log_div_log]; ring

/-- `√u - √v ≥ γ/2` when `v ≤ u - γ`, `0 ≤ γ ≤ u ≤ 1`. -/
lemma sqrt_gap {u v γ : ℝ} (hu1 : u ≤ 1) (hγ0 : 0 ≤ γ) (hγu : γ ≤ u) (hv : v ≤ u - γ) :
    γ / 2 ≤ √u - √v := by
  have hu0 : 0 ≤ u := by linarith
  have hs0 := Real.sqrt_nonneg u
  have hs2 : √u ^ 2 = u := Real.sq_sqrt hu0
  have hs1 : √u ≤ 1 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hu1
  have hsu : u ≤ √u := by nlinarith
  have : √v ≤ √u - γ / 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  linarith

end SecondOrderLog

open SecondOrderLog

/-! ### The converse -/

set_option maxHeartbeats 1000000 in
/-- **Second-order converse with `O(log n)` remainder**, assuming Berry–Esseen. -/
theorem converse_log {η Ns δ q B : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hB : 0 ≤ B) (hBE : BinomBE η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n : ℕ in atTop, ∀ (L' M : ℕ) (C : Code n L' M), 1 ≤ M →
      C.leak (cutoff Ns n) ≤ δ + B / √(n : ℝ) → 1 - (1 - δ) * Φ q ≤ C.success η →
        Real.logb 2 M ≤ n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) + A * Real.log n := by
  have hx : 0 < η * Ns := mul_pos hη0 hNs
  have hgp := gp_pos hx
  have hgs := gp_mul_sqrt_eq_sqrt_Vocc hη0 hη1 hNs
  set a := η * (1 - η) with ha
  have ha0 : 0 < a := mul_pos hη0 (by linarith)
  have hsa : 0 < √a := Real.sqrt_pos.2 ha0
  have hd : 0 < 1 - δ := by linarith
  have hsN1 : 0 < √(Ns + 1) := Real.sqrt_pos.2 (by linarith)
  set K := (B + 1) * √(Ns + 1) / (1 - δ) with hK
  obtain ⟨c, hc0, L₁, hL₁⟩ := binomLT_ge_of_BE hη0 hη1 hBE q K
  set D := |q| * √a + η + c + 1 with hD
  have hD0 : 0 ≤ D := by positivity
  set c2 := 1 / Real.log 2 with hc2
  have hc20 : 0 < c2 := by rw [hc2]; exact one_div_pos.2 (Real.log_pos (by norm_num))
  have hΦ0 := Φ_pos q
  have hΦ1 := Φ_lt_one q
  refine ⟨D * gp (η * Ns) + 2 + c2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 3, (tendsto_cutoff hNs).eventually (eventually_ge_atTop L₁),
    eventually_sqrt_cutoff_ge hNs (|q| * √a / η), eventually_sqrt_ge (B / (1 - δ))]
    with n hn3 hnL hnW hnB
  intro L' M C hM hleak hs
  have hn1 : 1 ≤ n := by omega
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlog := one_le_log_of_three_le hn3
  obtain ⟨hLlo, hLhi, hσlo, hσhi, hsLn⟩ := cutoff_facts hη0 hη1 hNs hn1
  rw [← ha] at hσlo hσhi
  set L := cutoff Ns n with hLdef
  set Lr : ℝ := (L : ℝ) with hLr
  set sn := √(n : ℝ) with hsn
  have hsn1 : 1 ≤ sn := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsn2 : sn ^ 2 = n := Real.sq_sqrt (by linarith)
  have hLr0 : 0 < Lr := lt_of_lt_of_le (by positivity) hLlo
  set sL := √Lr with hsL
  have hsL0 : 0 < sL := Real.sqrt_pos.2 hLr0
  have hsL2 : sL * sL = Lr := Real.mul_self_sqrt hLr0.le
  set σ := √(Lr * a) with hσ
  have hσe : σ = sL * √a := Real.sqrt_mul hLr0.le _
  set s₀ := sn * √(η * (1 - η) * Ns) with hs₀
  obtain ⟨hqlo, hqhi⟩ := mul_between (q := q) hσlo hσhi
  -- the threshold
  set y := η * Lr + q * σ + c with hy
  have hy0 : 0 ≤ y := by
    rw [div_le_iff₀ hη0] at hnW
    have h1 : -(|q| * σ) ≤ q * σ := by
      have := neg_abs_le q
      have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
      nlinarith
    have h2 : |q| * σ ≤ η * Lr := by
      rw [hσe, ← hsL2]
      have := mul_le_mul_of_nonneg_right hnW hsL0.le
      nlinarith
    linarith
  set r := ⌈y⌉₊ with hr
  have hry : y ≤ r := Nat.le_ceil y
  have hry1 : (r : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have hP := hL₁ L hnL (r + 1) (by push_cast; linarith)
  set P := binomLT L η (r + 1) with hPdef
  have hG : binomGT L η r = 1 - P := rfl
  have hG0 := binomGT_nonneg hη0.le hη1.le L r
  have hP1 : P ≤ 1 := by linarith
  -- slack
  set u := 1 / sn with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu, div_le_one (by linarith)]; exact hsn1
  have hKu : (B + 1) * u / (1 - δ) ≤ K / sL := by
    rw [hK, hu, div_le_div_iff₀ hd hsL0]
    have h1 : (B + 1) * (1 / sn) * sL ≤ (B + 1) * (1 / sn) * (sn * √(Ns + 1)) :=
      mul_le_mul_of_nonneg_left hsLn (by positivity)
    have h2 : (B + 1) * (1 / sn) * (sn * √(Ns + 1)) = (B + 1) * √(Ns + 1) := by
      field_simp
    have h3 : (B + 1) * √(Ns + 1) / (1 - δ) * (1 - δ) = (B + 1) * √(Ns + 1) := by
      field_simp
    linarith
  set P₀ := Φ q + (B + 1) * u / (1 - δ) with hP₀
  have hP₀P : P₀ ≤ P := by linarith
  have hP₀e : (1 - δ) * P₀ = (1 - δ) * Φ q + (B + 1) * u := by
    rw [hP₀]; field_simp
  have hBu : B / sn = B * u := by rw [hu]; ring
  rw [hBu] at hleak
  have hδn1 : δ + B * u ≤ 1 := by
    rw [div_le_iff₀ hd] at hnB
    have : B * u ≤ 1 - δ := by
      rw [hu, mul_one_div, div_le_iff₀ (by linarith)]
      linarith
    linarith
  have hBu0 : 0 ≤ B * u := by positivity
  have hkey : (1 - δ) * Φ q + u ≤ (1 - (δ + B * u)) * P := by
    have h1 : (1 - (δ + B * u)) * P₀ ≤ (1 - (δ + B * u)) * P :=
      mul_le_mul_of_nonneg_left hP₀P (by linarith)
    have h2 : (1 - (δ + B * u)) * P₀ = (1 - δ) * P₀ - B * u * P₀ := by ring
    have h3 : B * u * P₀ ≤ B * u * 1 := mul_le_mul_of_nonneg_left (by linarith) hBu0
    linarith
  set ε := (1 - δ) * Φ q with hε
  have hε0 : 0 ≤ ε := by positivity
  set Q := (1 - (δ + B * u)) * binomGT L η r + (δ + B * u) with hQ
  have hQle : Q ≤ 1 - ε - u := by rw [hQ, hG]; linarith
  have hQ0 : 0 ≤ Q := by
    have := mul_nonneg (sub_nonneg.2 hδn1) hG0
    rw [hQ]; linarith
  have hfin := converse_finite hη0.le hη1.le hM C L r (by linarith) hδn1 hleak hs
    (by linarith)
  have hgap : u / 2 ≤ √(1 - ε) - √Q :=
    sqrt_gap (by linarith) hu0.le (by linarith) hQle
  have hch : (0 : ℝ) < ((n + r).choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left _ _)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hu2 : (u / 2) ^ 2 * (4 * n) = 1 := by
    have e1 : u * sn = 1 := by rw [hu]; field_simp
    have e2 : (u / 2) ^ 2 * (4 * n) = (u * sn) ^ 2 := by rw [← hsn2]; ring
    rw [e2, e1]; norm_num
  have hM' : (M : ℝ) ≤ ((n + r).choose r : ℝ) * (4 * n) := by
    have hpos : 0 < √(1 - ε) - √Q := lt_of_lt_of_le (by positivity) hgap
    rw [le_div_iff₀ (pow_pos hpos 2)] at hfin
    have h1 := pow_le_pow_left₀ (by positivity) hgap 2
    have h2 : (M : ℝ) * (u / 2) ^ 2 ≤ ((n + r).choose r : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left h1 hMr.le) hfin
    have h3 := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ 4 * n by positivity)
    rw [mul_assoc, hu2, mul_one] at h3
    exact h3
  have hlogM : Real.logb 2 M ≤ Real.logb 2 ((n + r).choose r : ℝ) + 2 + c2 * Real.log n := by
    have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hMr hM'
    rw [Real.logb_mul hch.ne' (by positivity), Real.logb_mul (by norm_num) (by positivity)] at h1
    have h4 : Real.logb 2 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [h4, logb_two_eq (n : ℝ)] at h1
    linarith
  have hst := logb_choose_le n r hx
  -- r - n x ≤ q s₀ + D
  have hrn : (r : ℝ) - n * (η * Ns) ≤ q * s₀ + D := by
    have e2 : η * Lr ≤ η * (n * Ns + 1) := mul_le_mul_of_nonneg_left hLhi.le hη0.le
    rw [hD]
    nlinarith
  have h4 := mul_le_mul_of_nonneg_right hrn hgp.le
  have h5 : (q * s₀ + D) * gp (η * Ns) = q * √(Vocc η Ns) * sn + D * gp (η * Ns) := by
    rw [← hgs, hs₀]; ring
  rw [h5] at h4
  have h6 : D * gp (η * Ns) + 2 ≤ (D * gp (η * Ns) + 2) * Real.log n :=
    le_mul_of_one_le_right (by positivity) hlog
  have h7 : (D * gp (η * Ns) + 2 + c2) * Real.log n =
      (D * gp (η * Ns) + 2) * Real.log n + c2 * Real.log n := by ring
  rw [h7]
  linarith

end QIQCOP
