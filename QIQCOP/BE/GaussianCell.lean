import QIQCOP.GaussianInv

/-!
# Gaussian cell estimates

* `phi z = exp(-z²/2)/√(2π)` and `Φ b - Φ a = ∫_a^b phi`;
* `|Φ(z+h) - Φ(z) - h·phi(z)| ≤ C h²/(1+|z|)²` for `0 < h ≤ 1`;
* `∑_{k<t} h/(1+|z₀+kh|)² ≤ 4` (telescoping against `s/(1+|s|)`);
* Chebyshev tail bound `Φ(-u) ≤ 1/u²`.
-/

open Real MeasureTheory ProbabilityTheory Finset

namespace QIQCOP.BE

/-- Standard normal density. -/
noncomputable def phi (z : ℝ) : ℝ := exp (-z ^ 2 / 2) / √(2 * π)

lemma phi_eq (z : ℝ) : phi z = gaussianPDFReal 0 1 z := by
  simp [phi, gaussianPDFReal, div_eq_inv_mul]

lemma phi_nonneg (z : ℝ) : 0 ≤ phi z := by unfold phi; positivity

lemma one_le_sqrt_two_pi : (1 : ℝ) ≤ √(2 * π) := by
  rw [Real.one_le_sqrt]
  nlinarith [Real.pi_gt_three]

lemma continuous_phi : Continuous phi := by unfold phi; fun_prop

/-- Gaussian decay: `exp(-y²/2) ≤ 1536/(1+|y|)⁵`. -/
lemma exp_neg_sq_le (y : ℝ) : exp (-y ^ 2 / 2) ≤ 1536 / (1 + |y|) ^ 5 := by
  have ht : 0 ≤ |y| := abs_nonneg y
  rw [le_div_iff₀ (by positivity), show -y ^ 2 / 2 = -(|y| ^ 2 / 2) by rw [sq_abs]; ring,
    exp_neg, inv_mul_le_iff₀ (exp_pos _)]
  set t := |y|
  rcases le_total t 1 with h | h
  · have h1 : (1 + t) ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
    have h2 : 1 ≤ exp (t ^ 2 / 2) := one_le_exp (by positivity)
    nlinarith
  · have h1 : (1 + t) ^ 5 ≤ (2 * t) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
    have h2 := Real.pow_div_factorial_le_exp (x := t ^ 2 / 2) (by positivity) 3
    have h3 : (t ^ 2 / 2) ^ 3 / (Nat.factorial 3 : ℝ) = t ^ 6 / 48 := by
      norm_num [Nat.factorial]; ring
    rw [h3] at h2
    have h4 : t ^ 5 ≤ t ^ 6 := by
      have : 0 ≤ t ^ 5 := by positivity
      nlinarith
    nlinarith

lemma phi_le (z : ℝ) : phi z ≤ 1536 / (1 + |z|) ^ 5 := by
  unfold phi
  refine (div_le_self (exp_pos _).le one_le_sqrt_two_pi).trans (exp_neg_sq_le z)

lemma abs_exp_neg_sub_le (A B : ℝ) :
    |exp (-A) - exp (-B)| ≤ |A - B| * (exp (-A) + exp (-B)) := by
  have key : ∀ A B : ℝ, A ≤ B → |exp (-A) - exp (-B)| ≤ |A - B| * (exp (-A) + exp (-B)) := by
    intro A B hAB
    have h1 : exp (-B) ≤ exp (-A) := exp_le_exp.2 (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    have h2 : exp (-B) = exp (-A) * exp (-(B - A)) := by rw [← exp_add]; congr 1; ring
    have h3 := add_one_le_exp (-(B - A))
    have h4 := exp_pos (-A)
    have h5 := exp_pos (-B)
    have h6 : exp (-A) * (1 - (B - A)) ≤ exp (-A) * exp (-(B - A)) :=
      mul_le_mul_of_nonneg_left (by linarith) h4.le
    nlinarith
  rcases le_total A B with h | h
  · exact key A B h
  · have := key B A h
    rw [abs_sub_comm, abs_sub_comm A B, add_comm (exp (-A))]
    exact this

/-- Local Lipschitz bound with decay for the normal density. -/
lemma abs_phi_sub_le {z s h : ℝ} (hh1 : h ≤ 1) (hs : |s - z| ≤ h) :
    |phi s - phi z| ≤ 50688 * h / (1 + |z|) ^ 2 := by
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hh0 : 0 ≤ h := (abs_nonneg _).trans hs
  have hsz : |z| - 1 ≤ |s| := by
    have := abs_sub_abs_le_abs_sub z s
    rw [abs_sub_comm] at this
    linarith
  have hszu : |s| ≤ |z| + 1 := by
    have := abs_sub_abs_le_abs_sub s z
    linarith
  have h1s : (1 + |z|) / 2 ≤ 1 + |s| := by
    have := abs_nonneg s
    rcases le_total |z| 1 with h | h <;> linarith
  have e1 : exp (-s ^ 2 / 2) ≤ 1536 * 32 / (1 + |z|) ^ 5 := by
    refine (exp_neg_sq_le s).trans ?_
    have : 1536 * 32 / (1 + |z|) ^ 5 = 1536 / ((1 + |z|) / 2) ^ 5 := by
      field_simp; norm_num
    rw [this]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ (by positivity) h1s 5)
  have e2 := exp_neg_sq_le z
  have e3 : |s ^ 2 / 2 - z ^ 2 / 2| ≤ h * (1 + |z|) := by
    have : s ^ 2 / 2 - z ^ 2 / 2 = (s - z) * (s + z) / 2 := by ring
    rw [this, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h2 : |s + z| ≤ 2 * |z| + 1 := (abs_add_le s z).trans (by linarith)
    have := mul_le_mul hs h2 (abs_nonneg _) hh0
    nlinarith
  have e4 := abs_exp_neg_sub_le (s ^ 2 / 2) (z ^ 2 / 2)
  have e5 : exp (-(s ^ 2 / 2)) + exp (-(z ^ 2 / 2)) ≤ 50688 / (1 + |z|) ^ 5 := by
    have : (50688 : ℝ) / (1 + |z|) ^ 5 = 1536 * 32 / (1 + |z|) ^ 5 + 1536 / (1 + |z|) ^ 5 := by
      ring
    rw [this, show -(s ^ 2 / 2) = -s ^ 2 / 2 by ring, show -(z ^ 2 / 2) = -z ^ 2 / 2 by ring]
    linarith
  have e6 : |exp (-(s ^ 2 / 2)) - exp (-(z ^ 2 / 2))| ≤
      h * (1 + |z|) * (50688 / (1 + |z|) ^ 5) :=
    e4.trans (mul_le_mul e3 e5 (by positivity) (by positivity))
  have e7 : h * (1 + |z|) * (50688 / (1 + |z|) ^ 5) ≤ 50688 * h / (1 + |z|) ^ 2 := by
    have : h * (1 + |z|) * (50688 / (1 + |z|) ^ 5) = 50688 * h / (1 + |z|) ^ 4 := by
      field_simp
    rw [this]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    exact pow_le_pow_right₀ (by linarith) (by norm_num)
  have e8 : phi s - phi z = (exp (-(s ^ 2 / 2)) - exp (-(z ^ 2 / 2))) / √(2 * π) := by
    unfold phi; ring_nf
  rw [e8, abs_div, abs_of_pos (by positivity : (0 : ℝ) < √(2 * π))]
  exact (div_le_self (abs_nonneg _) one_le_sqrt_two_pi).trans (e6.trans e7)

lemma Φ_sub_eq_integral {a b : ℝ} (hab : a ≤ b) : Φ b - Φ a = ∫ x in a..b, phi x := by
  have h1 : Φ b = Φ a + (gaussianReal 0 1).real (Set.Ioc a b) := by
    rw [Φ_eq, Φ_eq, ← measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hab]
  rw [h1, add_sub_cancel_left, measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg _ _ _),
    intervalIntegral.integral_of_le hab]
  simp_rw [phi_eq]

/-- Cell estimate: `Φ(z+h) - Φ(z) = h·phi(z) + O(h²/(1+|z|)²)`. -/
theorem abs_cell_sub_le {z h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) :
    |Φ (z + h) - Φ z - h * phi z| ≤ 50688 * h ^ 2 / (1 + |z|) ^ 2 := by
  rw [Φ_sub_eq_integral (by linarith)]
  have hint : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume z (z + h) :=
    fun f hf => hf.intervalIntegrable _ _
  have e : (∫ x in z..(z + h), phi x) - h * phi z = ∫ x in z..(z + h), (phi x - phi z) := by
    rw [intervalIntegral.integral_sub (hint _ continuous_phi) (hint _ continuous_const),
      intervalIntegral.integral_const]
    simp
  rw [e, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := z) (b := z + h)
    (C := 50688 * h / (1 + |z|) ^ 2) (f := fun x => phi x - phi z) (by
      intro x hx
      rw [Set.uIoc_of_le (by linarith)] at hx
      rw [Real.norm_eq_abs]
      refine abs_phi_sub_le hh1 ?_
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
  refine this.trans (le_of_eq ?_)
  rw [add_sub_cancel_left, abs_of_pos hh0]
  ring

/-- Telescoping weight. -/
lemma weight_le_telescope {z h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) :
    h / (1 + |z|) ^ 2 ≤ 2 * ((z + h) / (1 + |z + h|) - z / (1 + |z|)) := by
  rcases le_or_gt 0 z with hz | hz
  · rw [abs_of_nonneg hz, abs_of_nonneg (by linarith : 0 ≤ z + h)]
    have e : 2 * ((z + h) / (1 + (z + h)) - z / (1 + z)) = 2 * h / ((1 + z) * (1 + z + h)) := by
      field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hh0 (by linarith : 0 < 1 + z)]
  · rcases le_or_gt (z + h) 0 with hzh | hzh
    · rw [abs_of_neg hz, abs_of_nonpos hzh]
      have p1 : 0 < 1 + -z := by linarith
      have p2 : 0 < 1 + -(z + h) := by linarith
      have e : 2 * ((z + h) / (1 + -(z + h)) - z / (1 + -z)) =
          2 * h / ((1 + -z) * (1 + -(z + h))) := by
        field_simp; ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hh0 p1, mul_pos p1 p2]
    · rw [abs_of_neg hz, abs_of_pos hzh]
      have p1 : 0 < 1 + -z := by linarith
      have p2 : 0 < 1 + (z + h) := by linarith
      have a1 : (z + h) / 2 ≤ (z + h) / (1 + (z + h)) :=
        div_le_div_of_nonneg_left hzh.le p2 (by linarith)
      have a2 : z / (1 + -z) ≤ z / 2 := by
        rw [div_le_div_iff₀ p1 (by norm_num)]
        nlinarith
      have a3 : h / (1 + -z) ^ 2 ≤ h := by
        refine div_le_self hh0.le ?_
        nlinarith
      linarith

theorem sum_weight_le {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (z0 : ℝ) (t : ℕ) :
    ∑ k ∈ range t, h / (1 + |z0 + k * h|) ^ 2 ≤ 4 := by
  set G : ℝ → ℝ := fun s => s / (1 + |s|) with hG
  have hGle : ∀ s, |G s| ≤ 1 := by
    intro s
    rw [hG]
    simp only
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + |s|), div_le_one (by positivity)]
    linarith
  calc ∑ k ∈ range t, h / (1 + |z0 + k * h|) ^ 2
      ≤ ∑ k ∈ range t, 2 * (G (z0 + (k + 1 : ℕ) * h) - G (z0 + k * h)) := by
        refine sum_le_sum fun k _ => ?_
        have := weight_le_telescope (z := z0 + k * h) hh0 hh1
        have e : z0 + ((k + 1 : ℕ) : ℝ) * h = z0 + k * h + h := by push_cast; ring
        rw [e]
        exact this
    _ = 2 * (G (z0 + t * h) - G (z0 + (0 : ℕ) * h)) := by
        rw [← mul_sum, Finset.sum_range_sub (fun k : ℕ => G (z0 + k * h))]
    _ ≤ 4 := by
        have h1 := (abs_le.1 (hGle (z0 + t * h))).2
        have h2 := (abs_le.1 (hGle (z0 + (0 : ℕ) * h))).1
        linarith

/-- Chebyshev bound for the lower Gaussian tail. -/
theorem Φ_neg_le {u : ℝ} (hu : 0 < u) : Φ (-u) ≤ 1 / u ^ 2 := by
  have h := meas_ge_le_variance_div_sq (μ := gaussianReal 0 1) (X := id)
    (memLp_id_gaussianReal 2) hu
  rw [variance_id_gaussianReal] at h
  have hmean : (∫ x, id x ∂(gaussianReal 0 1)) = 0 := by
    simp
  rw [hmean] at h
  have hsub : Set.Iic (-u) ⊆ {ω : ℝ | u ≤ |id ω - 0|} := by
    intro x hx
    simp only [Set.mem_Iic] at hx
    simp only [id, sub_zero, Set.mem_ofPred_eq]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have h2 := (measure_mono hsub).trans h
  rw [Φ]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  simpa using h2

end QIQCOP.BE
