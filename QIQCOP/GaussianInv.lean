import QIQCOP.Gaussian

/-!
# `Φ` is a continuous bijection `ℝ → (0,1)` with `Φ 0 = 1/2`

So for every `ε ∈ (0,1)` there is a unique `q = Φ⁻¹(ε)`, and `q < 0 ↔ ε < 1/2`.
-/

open Filter Topology MeasureTheory ProbabilityTheory

namespace QIQCOP

lemma Φ_eq_cdf : Φ = cdf (gaussianReal 0 1) := by
  funext z; rw [cdf_eq_real]; rfl

theorem Φ_continuous : Continuous Φ := by
  rw [Φ_eq_cdf]
  have := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := 1) one_ne_zero
  set f := cdf (gaussianReal 0 1)
  rw [continuous_iff_continuousAt]
  intro x
  have hmono : Monotone f := f.mono
  have hl : Function.leftLim f x = f x := by
    have h1 := f.measure_singleton x
    rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at h1
    exact le_antisymm (Monotone.leftLim_le hmono le_rfl) (by linarith)
  refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
  · exact hmono.continuousWithinAt_Iio_iff_leftLim_eq.2 hl
  · exact (f.right_continuous x).mono Set.Ioi_subset_Ici_self

theorem Φ_zero : Φ 0 = 1 / 2 := by
  have := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := 1) one_ne_zero
  have hsym : (gaussianReal 0 1).real (Set.Ici 0) = (gaussianReal 0 1).real (Set.Iic 0) := by
    have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
    rw [neg_zero] at h
    conv_lhs => rw [← h]
    rw [map_measureReal_apply measurable_neg measurableSet_Ici]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]
    constructor <;> intro hx <;> linarith
  have hIoi : (gaussianReal 0 1).real (Set.Ioi 0) = (gaussianReal 0 1).real (Set.Ici 0) :=
    measureReal_congr Ioi_ae_eq_Ici
  have hsum : (gaussianReal 0 1).real (Set.Iic 0) + (gaussianReal 0 1).real (Set.Ioi 0) = 1 := by
    rw [← measureReal_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi,
      Set.Iic_union_Ioi, probReal_univ]
  rw [Φ_eq]
  linarith

theorem exists_Φ_eq {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : ∃ q, Φ q = ε := by
  have hbot : Tendsto Φ atBot (𝓝 0) := Φ_eq_cdf ▸ tendsto_cdf_atBot _
  have htop : Tendsto Φ atTop (𝓝 1) := Φ_eq_cdf ▸ tendsto_cdf_atTop _
  obtain ⟨a, ha⟩ := (hbot.eventually (gt_mem_nhds h0)).exists
  obtain ⟨b, hb⟩ := (htop.eventually (lt_mem_nhds h1)).exists
  have hab : a ≤ b := by
    by_contra h
    push Not at h
    linarith [Φ_strictMono.monotone h.le]
  obtain ⟨q, -, hq⟩ := intermediate_value_Icc hab Φ_continuous.continuousOn ⟨ha.le, hb.le⟩
  exact ⟨q, hq⟩

theorem Φ_lt_half_iff {q : ℝ} : Φ q < 1 / 2 ↔ q < 0 := by
  rw [← Φ_zero]; exact Φ_strictMono.lt_iff_lt

end QIQCOP
