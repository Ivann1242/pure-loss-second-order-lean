import QIQCOP.Defs

/-!
# The standard normal CDF `Φ`

`Φ z = Pr{Z ≤ z}` for `Z ~ N(0,1)`. The problem's `Φ⁻¹(ε)` is the unique `q` with `Φ q = ε`
(uniqueness from strict monotonicity).
-/

open MeasureTheory ProbabilityTheory

namespace QIQCOP

/-- Standard normal cumulative distribution function. -/
noncomputable def Φ (z : ℝ) : ℝ := (gaussianReal 0 1 (Set.Iic z)).toReal

lemma Φ_eq (z : ℝ) : Φ z = (gaussianReal 0 1).real (Set.Iic z) := rfl

lemma Φ_le_one (z : ℝ) : Φ z ≤ 1 := by
  rw [Φ_eq]; exact measureReal_le_one

/-- Every nonempty open-closed interval has positive standard-normal mass. -/
lemma gaussianReal_Ioc_pos {a b : ℝ} (hab : a < b) :
    0 < (gaussianReal 0 1).real (Set.Ioc a b) := by
  rw [measureReal_def]
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  intro h0
  have hac := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero
  have := hac h0
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at this
  linarith

theorem Φ_strictMono : StrictMono Φ := by
  intro a b hab
  rw [Φ_eq, Φ_eq, ← Set.Iic_union_Ioc_eq_Iic hab.le,
    measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
  linarith [gaussianReal_Ioc_pos hab]

/-- Symmetry: `Pr{Z ≥ 1} = Pr{Z ≤ -1}`. -/
lemma gaussianReal_Ici_one :
    (gaussianReal 0 1).real (Set.Ici 1) = (gaussianReal 0 1).real (Set.Iic (-1)) := by
  have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  rw [neg_zero] at h
  conv_lhs => rw [← h]
  rw [map_measureReal_apply measurable_neg measurableSet_Ici]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]
  constructor <;> intro hx <;> linarith

/-- `Pr{-1 < Z < 1} ≤ 2/√(2π) ≤ 4/5`. -/
lemma gaussianReal_Ioo_le :
    (gaussianReal 0 1).real (Set.Ioo (-1) 1) ≤ 4 / 5 := by
  set c : ℝ := (√(2 * Real.pi))⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hpdf : ∀ x, gaussianPDF 0 1 x ≤ ENNReal.ofReal c := by
    intro x
    rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    refine mul_le_of_le_one_right hc0 ?_
    rw [Real.exp_le_one_iff]
    have : 0 ≤ x ^ 2 := sq_nonneg x
    have : -x ^ 2 / 2 ≤ 0 := by linarith
    exact this
  have hle : gaussianReal 0 1 (Set.Ioo (-1) 1) ≤ ENNReal.ofReal (c * 2) := by
    rw [gaussianReal_apply _ one_ne_zero]
    calc ∫⁻ x in Set.Ioo (-1) 1, gaussianPDF 0 1 x
        ≤ ∫⁻ _ in Set.Ioo (-1 : ℝ) 1, ENNReal.ofReal c := lintegral_mono hpdf
      _ = ENNReal.ofReal c * ENNReal.ofReal 2 := by
        rw [setLIntegral_const, Real.volume_Ioo]; norm_num
      _ = ENNReal.ofReal (c * 2) := (ENNReal.ofReal_mul hc0).symm
  have h1 : (gaussianReal 0 1).real (Set.Ioo (-1) 1) ≤ c * 2 := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle
  have h2 : c * 2 ≤ 4 / 5 := by
    have hs : (5 : ℝ) / 2 ≤ √(2 * Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      have := Real.pi_gt_d2
      norm_num at this ⊢
      linarith
    have hpos : (0 : ℝ) < √(2 * Real.pi) := by positivity
    rw [hc, inv_mul_eq_div, div_le_iff₀ hpos]
    linarith
  linarith

theorem Φ_neg_one_ge : (1 : ℝ) / 10 ≤ Φ (-1) := by
  have hsum : (gaussianReal 0 1).real (Set.Iic (-1)) + (gaussianReal 0 1).real (Set.Ioo (-1) 1)
      + (gaussianReal 0 1).real (Set.Ici 1) = 1 := by
    have hd : Disjoint (Set.Iic (-1 : ℝ)) (Set.Ioo (-1) 1) :=
      Set.disjoint_left.mpr fun x hx hy => absurd hx (not_le.mpr hy.1)
    rw [← measureReal_union (μ := gaussianReal 0 1) hd measurableSet_Ioo,
      Set.Iic_union_Ioo_eq_Iio (by norm_num),
      ← measureReal_union (Set.Iio_disjoint_Ici le_rfl) measurableSet_Ici,
      Set.Iio_union_Ici, probReal_univ]
  rw [gaussianReal_Ici_one] at hsum
  have := gaussianReal_Ioo_le
  rw [Φ_eq]
  linarith

theorem Φ_neg_one_lt_one : Φ (-1) < 1 :=
  lt_of_lt_of_le (Φ_strictMono (by norm_num : (-1 : ℝ) < 0)) (Φ_le_one 0)

end QIQCOP
