import QIQCOP.Binomial
import QIQCOP.Gaussian

/-!
# De Moivre–Laplace for the threshold `Pr{K < η L + z √(L η (1-η))}`

For `K ~ Bin(L, η)` with `0 < η < 1` and any real `z`,
`Pr{K < η L + z √(L η(1-η))} → Φ(z)` as `L → ∞`. Here the probability is written as
`binomLT L η ⌈η L + z √(L η(1-η))⌉₊` (for integer `K`, `K < ⌈y⌉₊ ↔ K < y`).
-/

open Filter Topology MeasureTheory ProbabilityTheory Complex

namespace QIQCOP

private noncomputable def discMeas (s : Finset ℕ) (w x : ℕ → ℝ) : Measure ℝ :=
  ∑ j ∈ s, ENNReal.ofReal (w j) • Measure.dirac (x j)

private lemma integral_discMeas {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (s : Finset ℕ) (w x : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (f : ℝ → E) :
    ∫ y, f y ∂(discMeas s w x) = ∑ j ∈ s, w j • f (x j) := by
  unfold discMeas
  rw [integral_finsetSum_measure]
  · simp [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw _)]
  · intro j _
    exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

private lemma discMeas_apply (s : Finset ℕ) (w x : ℕ → ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    discMeas s w x S = ∑ j ∈ s, ENNReal.ofReal (w j) * S.indicator 1 (x j) := by
  unfold discMeas
  simp [Measure.dirac_apply' _ hS]

private lemma charFun_discMeas (s : Finset ℕ) (w x : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (t : ℝ) :
    charFun (discMeas s w x) t = ∑ j ∈ s, (w j : ℂ) * cexp (t * x j * I) := by
  rw [charFun_apply_real, integral_discMeas s w x hw]
  simp [Complex.real_smul]

private lemma isProb_discMeas (s : Finset ℕ) (w x : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (h1 : ∑ j ∈ s, w j = 1) : IsProbabilityMeasure (discMeas s w x) := by
  constructor
  rw [discMeas_apply _ _ _ _ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hw j), h1, ENNReal.ofReal_one]

/-- The standardized Bernoulli law. -/
private noncomputable def bernStd (η : ℝ) : Measure ℝ :=
  discMeas (Finset.range 2) (fun j => if j = 0 then 1 - η else η)
    (fun j => if j = 0 then -η / √(η * (1 - η)) else (1 - η) / √(η * (1 - η)))

/-- The law of `(K - ηL)/√(L η (1-η))`. -/
private noncomputable def binStd (η : ℝ) (L : ℕ) : Measure ℝ :=
  discMeas (Finset.range (L + 1)) (binomPMF L η)
    (fun j => ((j : ℝ) - η * L) / √(L * (η * (1 - η))))

section
variable {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
include hη0 hη1

private lemma bernStd_w_nonneg : ∀ j, 0 ≤ (fun j : ℕ => if j = 0 then 1 - η else η) j := by
  intro j; dsimp only; split_ifs <;> linarith

private lemma isProb_bernStd : IsProbabilityMeasure (bernStd η) :=
  isProb_discMeas _ _ _ (bernStd_w_nonneg hη0 hη1) (by simp [Finset.sum_range_succ])

private lemma isProb_binStd (L : ℕ) : IsProbabilityMeasure (binStd η L) :=
  isProb_discMeas _ _ _ (binomPMF_nonneg hη0.le hη1.le) (sum_binomPMF L η)

private lemma bernStd_mean : ∫ x, id x ∂(bernStd η) = 0 := by
  rw [bernStd, integral_discMeas _ _ _ (bernStd_w_nonneg hη0 hη1)]
  simp [Finset.sum_range_succ]
  ring

private lemma bernStd_var : ∫ x, (id ^ 2 : ℝ → ℝ) x ∂(bernStd η) = 1 := by
  rw [bernStd, integral_discMeas _ _ _ (bernStd_w_nonneg hη0 hη1)]
  have ha : 0 < η * (1 - η) := mul_pos hη0 (by linarith)
  have hs := Real.sq_sqrt ha.le
  have hs0 : √(η * (1 - η)) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have h1 : 1 - η ≠ 0 := by linarith
  simp [Finset.sum_range_succ, div_pow, hs]
  field_simp
  ring

private lemma charFun_binStd {L : ℕ} (hL : 1 ≤ L) (t : ℝ) :
    charFun (binStd η L) t = (charFun (bernStd η) ((√L)⁻¹ * t)) ^ L := by
  have ha : 0 < η * (1 - η) := mul_pos hη0 (by linarith)
  have hs0 : √(η * (1 - η)) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hL0 : √(L : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hL)).ne'
  rw [binStd, bernStd, charFun_discMeas _ _ _ (binomPMF_nonneg hη0.le hη1.le),
    charFun_discMeas _ _ _ (bernStd_w_nonneg hη0 hη1)]
  conv_rhs =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_ne_zero, ite_false,
      ite_true]
    rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjL : j ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hr : t * (((j : ℝ) - η * L) / √(L * (η * (1 - η)))) =
      j * ((√L)⁻¹ * t * ((1 - η) / √(η * (1 - η)))) +
        ((L - j : ℕ) : ℝ) * ((√L)⁻¹ * t * (-η / √(η * (1 - η)))) := by
    rw [Nat.cast_sub hjL, Real.sqrt_mul (Nat.cast_nonneg _)]
    field_simp
    ring
  have hc : (↑t * ↑(((j : ℝ) - η * L) / √(L * (η * (1 - η)))) * I : ℂ) =
      j * (↑((√L)⁻¹ * t) * ↑((1 - η) / √(η * (1 - η))) * I) +
        ((L - j : ℕ) : ℂ) * (↑((√L)⁻¹ * t) * ↑(-η / √(η * (1 - η))) * I) := by
    have := congrArg (fun r : ℝ => (r : ℂ) * I) hr
    push_cast at this ⊢
    linear_combination this
  rw [hc, Complex.exp_add, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    binomPMF]
  push_cast
  ring

end

theorem binomLT_tendsto {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (z : ℝ) :
    Tendsto (fun L : ℕ => binomLT L η ⌈η * L + z * √(L * (η * (1 - η)))⌉₊) atTop
      (𝓝 (Φ z)) := by
  have := isProb_bernStd hη0 hη1
  let μs : ℕ → ProbabilityMeasure ℝ := fun L => ⟨binStd η L, isProb_binStd hη0 hη1 L⟩
  let μ₀ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hconv : Tendsto μs atTop (𝓝 μ₀) := by
    rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
    intro t
    have h := tendsto_charFun_inv_sqrt_mul_pow (P := bernStd η) (X := id) aemeasurable_id
      (bernStd_mean hη0 hη1) (bernStd_var hη0 hη1) t
    rw [Measure.map_id] at h
    have hg : charFun (μ₀ : Measure ℝ) t = cexp (-(t : ℂ) ^ 2 / 2) := by
      simp only [μ₀, ProbabilityMeasure.coe_mk, charFun_gaussianReal]
      congr 1; push_cast; ring
    rw [hg]
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with L hL
    exact (charFun_binStd hη0 hη1 hL t).symm
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv
    (E := Set.Iio z) (by simp [μ₀])
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
  have hlim : ((μ₀ : Measure ℝ) (Set.Iio z)).toReal = Φ z := by
    simp only [μ₀, ProbabilityMeasure.coe_mk, Φ]
    rw [measure_congr (Iio_ae_eq_Iic' (measure_singleton z))]
  rw [hlim] at hreal
  refine hreal.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hpos : 0 < √(L * (η * (1 - η))) :=
    Real.sqrt_pos.2 (mul_pos (by exact_mod_cast hL) (mul_pos hη0 (by linarith)))
  simp only [Function.comp_apply, μs, ProbabilityMeasure.coe_mk, binStd]
  rw [discMeas_apply _ _ _ _ measurableSet_Iio]
  have hterm : ∀ j ∈ Finset.range (L + 1), ENNReal.ofReal (binomPMF L η j) *
      (Set.Iio z).indicator 1 (((j : ℝ) - η * L) / √(L * (η * (1 - η)))) =
      ENNReal.ofReal (if j < ⌈η * L + z * √(L * (η * (1 - η)))⌉₊ then binomPMF L η j else 0) := by
    intro j _
    have hiff : ((j : ℝ) - η * L) / √(L * (η * (1 - η))) ∈ Set.Iio z ↔
        j < ⌈η * L + z * √(L * (η * (1 - η)))⌉₊ := by
      rw [Set.mem_Iio, div_lt_iff₀ hpos, Nat.lt_ceil]
      constructor <;> intro h <;> linarith
    by_cases hj : j < ⌈η * L + z * √(L * (η * (1 - η)))⌉₊
    · simp only [Set.indicator_of_mem (hiff.2 hj), hj, ite_true, Pi.one_apply, mul_one]
    · simp only [Set.indicator_of_notMem (fun h => hj (hiff.1 h)), hj, ite_false, mul_zero,
        ENNReal.ofReal_zero]
  rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg, ENNReal.toReal_ofReal,
    ← Finset.sum_filter, binomLT, eq_comm, ← Finset.sum_filter_of_ne (p := fun j => j < L + 1)]
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    tauto
  · intro j _ hne
    by_contra hj
    apply hne
    rw [binomPMF, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · exact Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact binomPMF_nonneg hη0.le hη1.le j
      · exact le_rfl
  · intro j _
    split_ifs
    · exact binomPMF_nonneg hη0.le hη1.le j
    · exact le_rfl

end QIQCOP
