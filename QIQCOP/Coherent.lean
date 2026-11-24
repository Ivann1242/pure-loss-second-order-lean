import QIQCOP.UnboundedConverse

/-!
# Coherent-state codes (M5)

* `coherent α`: the `n`-mode coherent vector, a unit vector with Poisson(`‖α‖²`) photon law.
* `coherent_output_law`: loss sends it to output photon law Poisson(`η‖α‖²`).
* `poi_clt`: the central limit theorem for Poisson(`N`), `N ∈ ℕ`.
* `coherent_converse`: for codes whose inputs are countable mixtures of coherent states of energy
  at most `⌈n N_S⌉`, `log₂ M ≤ n g(x) + (q √x g'(x) + τ) √n` eventually, `x = η N_S`.
* `coherent_separation`: for `q < 0`, `q √x g'(x) < q √V_occ`.

Scope: mixtures here are **countable**. A general continuous Glauber–Sudarshan mixture is not
covered by `UCode.IsCoherentMixture`.
-/

open Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped Nat NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace QIQCOP

namespace Unbounded

variable {n M : ℕ}

noncomputable section

/-! ### Poisson weights -/

/-- The Poisson probability `e^{-x} x^k / k!`. -/
def poi (x : ℝ) (k : ℕ) : ℝ := Real.exp (-x) * x ^ k / (k ! : ℝ)

lemma poi_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : 0 ≤ poi x k := by
  unfold poi; positivity

lemma hasSum_exp_series (x : ℝ) : HasSum (fun s : ℕ => x ^ s / (s ! : ℝ)) (Real.exp x) := by
  simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

lemma hasSum_poi (x : ℝ) : HasSum (poi x) 1 := by
  have h := (hasSum_exp_series x).mul_left (Real.exp (-x))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  refine h.congr_fun fun k => ?_
  simp only [poi]
  ring

/-- **Binomial thinning of a Poisson law.** -/
theorem poi_thinning {η : ℝ} (E : ℝ) (k : ℕ) :
    HasSum (fun t => poi E t * binomPMF t η k) (poi (η * E) k) := by
  rw [← hasSum_nat_add_iff' k]
  have hz : ∑ i ∈ range k, poi E i * binomPMF i η k = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [binomPMF, Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hi)]
      simp
  rw [hz, sub_zero]
  have h := (hasSum_exp_series ((1 - η) * E)).mul_left
    (Real.exp (-E) * (η * E) ^ k / (k ! : ℝ))
  have e : Real.exp (-E) * (η * E) ^ k / (k ! : ℝ) * Real.exp ((1 - η) * E) = poi (η * E) k := by
    have : Real.exp (-(η * E)) = Real.exp (-E) * Real.exp ((1 - η) * E) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [poi, this]; ring
  rw [e] at h
  refine h.congr_fun fun s => ?_
  have hc : ((s + k).choose k : ℝ) * ((k ! : ℝ) * (s ! : ℝ)) = ((s + k)! : ℝ) := by
    have := Nat.add_choose_mul_factorial_mul_factorial s k
    rw [show s + k = s + k from rfl] at this
    have h2 : (s + k).choose k * k ! * s ! = (s + k)! := by
      rw [Nat.add_comm s k] at this ⊢
      have h3 := Nat.choose_symm_add (a := k) (b := s)
      nlinarith [this, h3]
    have h4 : (((s + k).choose k * k ! * s ! : ℕ) : ℝ) = ((s + k)! : ℝ) := by rw [h2]
    push_cast at h4
    linarith
  have hk : (k ! : ℝ) ≠ 0 := by positivity
  have hs : (s ! : ℝ) ≠ 0 := by positivity
  have hf : ((s + k)! : ℝ) ≠ 0 := by positivity
  simp only [poi, binomPMF, Nat.add_sub_cancel]
  rw [← hc, mul_pow (1 - η) E s, mul_pow η E k]
  have hC : ((s + k).choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_left k s)).ne'
  field_simp
  ring

/-- The CDF `Pr{Poisson(x) ≤ r}`. -/
def poiLE (x : ℝ) (r : ℕ) : ℝ := ∑ k ∈ range (r + 1), poi x k

lemma hasDerivAt_poi_succ (x : ℝ) (k : ℕ) :
    HasDerivAt (fun y => poi y (k + 1)) (poi x k - poi x (k + 1)) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa using (hasDerivAt_neg x).exp
  have h2 := (h1.mul (hasDerivAt_pow (k + 1) x)).div_const (((k + 1)! : ℕ) : ℝ)
  refine h2.congr_deriv ?_
  simp only [poi, Nat.add_sub_cancel, Nat.factorial_succ]
  have hk : (k ! : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma hasDerivAt_poiLE (x : ℝ) (r : ℕ) :
    HasDerivAt (fun y => poiLE y r) (-poi x r) x := by
  induction r with
  | zero =>
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
      simpa using (hasDerivAt_neg x).exp
    refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
    · simp [poiLE, poi]
    · simp [poi]
  | succ r ih =>
    have h := ih.add (hasDerivAt_poi_succ x r)
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv (by ring)
    simp only [poiLE, Pi.add_apply]
    rw [Finset.sum_range_succ _ (r + 1)]

/-- **Stochastic monotonicity**: the Poisson CDF decreases in the mean. -/
theorem poiLE_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (r : ℕ) : poiLE y r ≤ poiLE x r := by
  have hanti : AntitoneOn (fun z => poiLE z r) (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun z _ => (hasDerivAt_poiLE z r).continuousAt.continuousWithinAt)
      (fun z _ => (hasDerivAt_poiLE z r).differentiableAt.differentiableWithinAt)
      (fun z hz => ?_)
    rw [(hasDerivAt_poiLE z r).deriv]
    rw [interior_Ici] at hz
    have := poi_nonneg (le_of_lt hz) r
    linarith
  exact hanti hx (hx.trans hxy) hxy

/-- Averaging the binomial tail over a Poisson law gives the thinned Poisson tail. -/
theorem poi_tail {η : ℝ} (E : ℝ) (r : ℕ) :
    HasSum (fun t => poi E t * binomGT t η r) (1 - poiLE (η * E) r) := by
  have h1 := hasSum_poi E
  have h2 : HasSum (fun t => ∑ k ∈ range (r + 1), poi E t * binomPMF t η k)
      (∑ k ∈ range (r + 1), poi (η * E) k) :=
    hasSum_sum fun k _ => poi_thinning E k
  refine (h1.sub h2).congr_fun fun t => ?_
  simp only [binomGT, binomLT, ← Finset.mul_sum]
  ring

/-! ### Coherent vectors -/

/-- Mean photon number `‖α‖² = ∑ⱼ |αⱼ|²` (the Euclidean norm, not the sup norm on `Fin n → ℂ`). -/
def energy (α : Fin n → ℂ) : ℝ := ∑ j, ‖α j‖ ^ 2

lemma energy_nonneg (α : Fin n → ℂ) : 0 ≤ energy α :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- Fock coefficients of the coherent state:
`⟨m|α⟩ = exp(-‖α‖²/2) ∏ⱼ αⱼ^{mⱼ}/√(mⱼ!)`. -/
def cohCoeff (α : Fin n → ℂ) (m : Idx n) : ℂ :=
  (Real.exp (-energy α / 2) : ℂ) * ∏ j, (α j ^ m j / ((√((m j)! : ℝ) : ℝ) : ℂ))

lemma norm_cohCoeff_sq (α : Fin n → ℂ) (m : Idx n) :
    ‖cohCoeff α m‖ ^ 2 =
      Real.exp (-energy α) * ∏ j, ((‖α j‖ ^ 2) ^ m j / ((m j)! : ℝ)) := by
  rw [cohCoeff, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_prod,
    ← Finset.prod_pow, ← Real.exp_nat_mul]
  congr 1
  · congr 1; push_cast; ring
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_pow,
      sq_abs, Real.sq_sqrt (by positivity), ← pow_mul, ← pow_mul, mul_comm]

/-- Multinomial theorem, sector form. -/
lemma sum_sector_pow (x : Fin n → ℝ) (t : ℕ) :
    ∑ m ∈ sector n t, ∏ j, (x j ^ m j / ((m j)! : ℝ)) = (∑ j, x j) ^ t / (t ! : ℝ) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_div]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hsum : ∑ j, m j = t := (Finset.mem_piAntidiag.1 hm).1
  have hspec := Nat.multinomial_spec Finset.univ m
  rw [hsum] at hspec
  have hspec' : (∏ j, ((m j)! : ℝ)) * (Nat.multinomial Finset.univ m : ℝ) = (t ! : ℝ) := by
    exact_mod_cast hspec
  have hp : (∏ j, ((m j)! : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => by positivity
  have ht : (t ! : ℝ) ≠ 0 := by positivity
  have hmn : (Nat.multinomial Finset.univ m : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hspec'
    exact ht hspec'.symm
  rw [Finset.prod_div_distrib, ← hspec']
  field_simp

lemma coh_sector (α : Fin n → ℂ) (t : ℕ) :
    ∑ m ∈ sector n t, ‖cohCoeff α m‖ ^ 2 = poi (energy α) t := by
  simp only [norm_cohCoeff_sq]
  rw [← Finset.mul_sum, sum_sector_pow, poi, energy]
  ring

lemma coh_hasSum (α : Fin n → ℂ) : HasSum (fun m => ‖cohCoeff α m‖ ^ 2) 1 := by
  set ph : (Σ t : ℕ, ↥(sector n t)) → ℝ :=
    (fun m => ‖cohCoeff α m‖ ^ 2) ∘ (photonEquiv n).symm with hph
  have hin : ∀ t, HasSum (fun c : ↥(sector n t) => ph ⟨t, c⟩) (poi (energy α) t) := by
    intro t
    have h : HasSum (fun c : ↥(sector n t) => ‖cohCoeff α c.1‖ ^ 2)
        (∑ c : ↥(sector n t), ‖cohCoeff α c.1‖ ^ 2) := hasSum_fintype _
    rw [Finset.sum_coe_sort (sector n t) (fun m => ‖cohCoeff α m‖ ^ 2), coh_sector] at h
    exact h
  have hs : Summable ph :=
    (summable_sigma_of_nonneg (f := ph) (fun x => by simp only [hph, Function.comp]; positivity)).2
      ⟨fun t => (hin t).summable, by
        simpa only [(hin _).tsum_eq] using (hasSum_poi (energy α)).summable⟩
  have hsig : HasSum ph 1 := HasSum.sigma_of_hasSum (hasSum_poi (energy α)) hin hs
  exact (Equiv.hasSum_iff (photonEquiv n).symm).1 hsig

/-- The `n`-mode coherent vector `|α⟩`. -/
def coherent (α : Fin n → ℂ) : Fock n := mkF (cohCoeff α) (coh_hasSum α).summable

@[simp] lemma coherent_apply (α : Fin n → ℂ) (m : Idx n) : coherent α m = cohCoeff α m := rfl

/-- `|α⟩` is a unit vector. -/
theorem norm_coherent (α : Fin n → ℂ) : ‖coherent α‖ = 1 := by
  have h := (hasSum_normSq (coherent α)).unique (coh_hasSum α)
  have h0 := norm_nonneg (coherent α)
  nlinarith

/-- The photon-number law of `|α⟩` is Poisson(`‖α‖²`). -/
theorem coherent_photon_law (α : Fin n → ℂ) (t : ℕ) :
    ‖secP t (coherent α)‖ ^ 2 = poi (energy α) t := by
  rw [norm_secP_sq]
  exact coh_sector α t

lemma binomPMF_le_one {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (L k : ℕ) : binomPMF L η k ≤ 1 := by
  by_cases h : k ≤ L
  · rw [← sum_binomPMF L η]
    exact Finset.single_le_sum (f := fun j => binomPMF L η j)
      (fun j _ => binomPMF_nonneg hη.1 hη.2 j) (Finset.mem_range.2 (Nat.lt_succ_of_le h))
  · rw [binomPMF, Nat.choose_eq_zero_of_lt (not_le.1 h)]
    simp

/-- One Kraus branch of the sector weight, as a coordinate sum. -/
lemma norm_secP_loss {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (ℓ' : Idx n) (ψ : Fock n) :
    ‖secP k (lossOp hη ℓ' ψ)‖ ^ 2 =
      ∑' m, (if photons m = k then (1 : ℝ) else 0) * lossW η ℓ' m * ‖ψ (m + ℓ')‖ ^ 2 := by
  have h := (hasSum_cut (fun m => photons m = k) (lossOp hη ℓ' ψ)).tsum_eq
  rw [show ‖secP k (lossOp hη ℓ' ψ)‖ ^ 2 =
    ‖cut (fun m => photons m = k) (lossOp hη ℓ' ψ)‖ ^ 2 from rfl, ← h]
  refine tsum_congr fun m => ?_
  rw [lossOp_apply, norm_coeff_sq hη]
  split_ifs <;> simp

/-- Output sector weight of a general vector, as a binomial average of its input weights. -/
lemma hasSum_secP_loss {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (ψ : Fock n) :
    HasSum (fun ℓ' : Idx n => ‖secP k (lossOp hη ℓ' ψ)‖ ^ 2)
      (∑' N, ‖ψ N‖ ^ 2 * binomPMF (photons N) η k) := by
  have h := (loss_fiber hη (h := fun t => if t = k then (1 : ℝ) else 0)
    (fun t => by split_ifs <;> norm_num) (fun t => by split_ifs <;> norm_num)
    (a := fun m => ‖ψ m‖ ^ 2) (fun m => by positivity) (hasSum_normSq ψ).summable).2
  have e0 : (∑' N, ‖ψ N‖ ^ 2 * transW η (fun t => if t = k then (1 : ℝ) else 0) N) =
      ∑' N, ‖ψ N‖ ^ 2 * binomPMF (photons N) η k :=
    tsum_congr fun N => by rw [transW_eq hη]
  rw [e0] at h
  exact h.congr_fun fun ℓ' => norm_secP_loss hη k ℓ' ψ

/-- A vector with Poisson(`E`) photon law has output photon law Poisson(`ηE`). -/
theorem output_law_of_poisson {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (ψ : Fock n) (E : ℝ)
    (hψ : ∀ t, ‖secP t ψ‖ ^ 2 = poi E t) :
    HasSum (fun ℓ' : Idx n => ‖secP k (lossOp hη ℓ' ψ)‖ ^ 2) (poi (η * E) k) := by
  have h := hasSum_secP_loss hη k ψ
  have hsum : Summable fun N : Idx n => ‖ψ N‖ ^ 2 * binomPMF (photons N) η k :=
    Summable.of_nonneg_of_le
      (fun N => mul_nonneg (sq_nonneg _) (binomPMF_nonneg hη.1 hη.2 k))
      (fun N => mul_le_of_le_one_right (sq_nonneg _) (binomPMF_le_one hη _ k))
      (hasSum_normSq ψ).summable
  have hf := photon_fiber (a := fun m => ‖ψ m‖ ^ 2) (f := fun t => binomPMF t η k) hsum
  have hf' : HasSum (fun t => poi E t * binomPMF t η k)
      (∑' N, ‖ψ N‖ ^ 2 * binomPMF (photons N) η k) :=
    hf.congr_fun fun t => by
      rw [← hψ t, norm_secP_sq, mul_comm]
  have hv := hf'.unique (poi_thinning (η := η) E k)
  rw [hv] at h
  exact h

/-- **Loss on a coherent state**: the output photon law is Poisson(`η‖α‖²`). -/
theorem coherent_output_law {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (α : Fin n → ℂ) (k : ℕ) :
    HasSum (fun ℓ' : Idx n => ‖secP k (lossOp hη ℓ' (coherent α))‖ ^ 2)
      (poi (η * energy α) k) :=
  output_law_of_poisson hη k (coherent α) (energy α) (coherent_photon_law α)

/-! ### Central limit theorem for the Poisson law -/

lemma tendsto_poisson_exponent (t : ℝ) :
    Tendsto (fun N : ℕ => (N : ℂ) * (Complex.exp (((t / √(N : ℝ) : ℝ) : ℂ) * Complex.I) - 1)
      - (t : ℂ) * (√(N : ℝ) : ℝ) * Complex.I) atTop (𝓝 (-(t : ℂ) ^ 2 / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun N : ℕ => |t| ^ 3 / √(N : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop _
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop |t|] with N hN hNt
  simp only [Function.comp_apply] at hNt
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set s := √(N : ℝ) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hss : (N : ℝ) = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hNC : (N : ℂ) = (s : ℂ) ^ 2 := by exact_mod_cast hss
  set x : ℂ := ((t / s : ℝ) : ℂ) * Complex.I with hx
  have hxn : ‖x‖ = |t| / s := by
    rw [hx, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos hs0]
  have hx1 : ‖x‖ ≤ 1 := by
    rw [hxn, div_le_one hs0]; exact hNt
  have hb := Complex.exp_bound hx1 (n := 3) (by norm_num)
  have hsx : (s : ℂ) * x = (t : ℂ) * Complex.I := by
    rw [hx]; push_cast; field_simp
  have key : (N : ℂ) * (Complex.exp x - 1) - (t : ℂ) * (s : ℂ) * Complex.I - (-(t : ℂ) ^ 2 / 2) =
      (N : ℂ) * (Complex.exp x - ∑ m ∈ range 3, x ^ m / (m.factorial : ℂ)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    rw [hNC]
    push_cast
    linear_combination ((s : ℂ) + ((s : ℂ) * x + (t : ℂ) * Complex.I) / 2) * hsx +
      ((t : ℂ) ^ 2 / 2) * Complex.I_sq
  rw [key, norm_mul, Complex.norm_natCast]
  have hc : ((Nat.succ 3 : ℕ) : ℝ) * (((3 : ℕ).factorial : ℝ) * ((3 : ℕ) : ℝ))⁻¹ ≤ 1 := by
    norm_num [Nat.factorial]
  have hb2 : ‖Complex.exp x - ∑ m ∈ range 3, x ^ m / (m.factorial : ℂ)‖ ≤ ‖x‖ ^ 3 :=
    hb.trans (mul_le_of_le_one_right (by positivity) hc)
  calc (N : ℝ) * ‖Complex.exp x - ∑ m ∈ range 3, x ^ m / (m.factorial : ℂ)‖
      ≤ (N : ℝ) * ‖x‖ ^ 3 := mul_le_mul_of_nonneg_left hb2 (by positivity)
    _ = |t| ^ 3 / s := by
      rw [hxn, hss]
      field_simp

/-- The standardized Poisson(`N`) law. -/
def poiStd (N : ℕ) : Measure ℝ :=
  ((poissonMeasure (N : ℝ≥0)).map (Nat.cast : ℕ → ℝ)).map fun x => (x - N) / √(N : ℝ)

instance (N : ℕ) : IsProbabilityMeasure (poiStd N) := by
  unfold poiStd
  have : IsProbabilityMeasure ((poissonMeasure (N : ℝ≥0)).map (Nat.cast : ℕ → ℝ)) :=
    (Measure.isProbabilityMeasure_map_iff (Measurable.of_discrete).aemeasurable).2 inferInstance
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 this

lemma charFun_poiStd {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    charFun (poiStd N) t = Complex.exp ((N : ℂ) * (Complex.exp (((t / √(N : ℝ) : ℝ) : ℂ) *
      Complex.I) - 1) - (t : ℂ) * (√(N : ℝ) : ℝ) * Complex.I) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set s := √(N : ℝ) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hss : (N : ℝ) = s * s := (Real.mul_self_sqrt (by linarith)).symm
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hP := charFun_map_cast_poissonMeasure (N : ℝ≥0) (t / s)
  rw [charFun_apply_real] at hP
  rw [charFun_apply_real, poiStd, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ x : ℝ, Complex.exp ((t : ℂ) * (((x - N) / s : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((t : ℂ) * (s : ℂ) * Complex.I)) *
        Complex.exp (((t / s : ℝ) : ℂ) * (x : ℂ) * Complex.I) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    have hNC : (N : ℂ) = (s : ℂ) * s := by exact_mod_cast hss
    push_cast
    rw [hNC]
    field_simp
    ring
  refine (integral_congr_ae (Eventually.of_forall fun x => hpt x)).trans ?_
  rw [integral_const_mul, hP, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Central limit theorem for Poisson(`N`)**. -/
theorem poi_clt (z : ℝ) :
    Tendsto (fun N : ℕ => ∑ k ∈ range ⌈(N : ℝ) + z * √(N : ℝ)⌉₊, poi N k) atTop (𝓝 (Φ z)) := by
  let μs : ℕ → ProbabilityMeasure ℝ := fun N => ⟨poiStd N, inferInstance⟩
  let μ₀ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hconv : Tendsto μs atTop (𝓝 μ₀) := by
    rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
    intro t
    have hg : charFun (μ₀ : Measure ℝ) t = Complex.exp (-(t : ℂ) ^ 2 / 2) := by
      simp only [μ₀, ProbabilityMeasure.coe_mk, charFun_gaussianReal]
      congr 1; push_cast; ring
    rw [hg]
    refine ((Complex.continuous_exp.tendsto _).comp (tendsto_poisson_exponent t)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (charFun_poiStd hN t).symm
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv
    (E := Set.Iio z) (by simp [μ₀])
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
  have hlim : ((μ₀ : Measure ℝ) (Set.Iio z)).toReal = Φ z := by
    simp only [μ₀, ProbabilityMeasure.coe_mk, Φ]
    rw [measure_congr (Iio_ae_eq_Iic' (measure_singleton z))]
  rw [hlim] at hreal
  refine hreal.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : 0 < √(N : ℝ) := Real.sqrt_pos.2 (by linarith)
  simp only [Function.comp_apply, μs, ProbabilityMeasure.coe_mk, poiStd]
  rw [Measure.map_map (by fun_prop) (Measurable.of_discrete),
    Measure.map_apply (by fun_prop) measurableSet_Iio]
  have hset : ((fun x : ℝ => (x - N) / √(N : ℝ)) ∘ (Nat.cast : ℕ → ℝ)) ⁻¹' Set.Iio z =
      ((range ⌈(N : ℝ) + z * √(N : ℝ)⌉₊ : Finset ℕ) : Set ℕ) := by
    ext k
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_Iio, Finset.coe_range]
    rw [div_lt_iff₀ hs0, Nat.lt_ceil]
    constructor <;> intro h <;> linarith
  rw [hset, ← sum_measure_singleton, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [poissonMeasure_singleton, ENNReal.toReal_ofReal (by positivity)]
  simp [poi]

/-! ### The coherent-state converse -/

/-- Every input of `C` is a countable mixture `∑ₖ pᵢₖ |αᵢₖ⟩⟨αᵢₖ|` of coherent states of energy
at most `L`, presented as the ensemble `ψᵢₖ = √pᵢₖ |αᵢₖ⟩`. -/
def UCode.IsCoherentMixture (C : UCode n M) (L : ℕ) : Prop :=
  ∃ (p : Fin M → ℕ → ℝ) (α : Fin M → ℕ → Fin n → ℂ),
    (∀ i k, 0 ≤ p i k) ∧ (∀ i, HasSum (p i) 1) ∧ (∀ i k, energy (α i k) ≤ L) ∧
      ∀ i k, C.ψ i k = ((√(p i k) : ℝ) : ℂ) • coherent (α i k)

/-- For a coherent-mixture code, `w_r ≤ Pr{Poisson(ηL) > r}`. -/
theorem UCode.tail_le_of_coherent (C : UCode n M) {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (hM : 1 ≤ M) {L : ℕ} (hC : C.IsCoherentMixture L) (r : ℕ) :
    C.tail η r ≤ 1 - poiLE (η * L) r := by
  obtain ⟨p, α, hp0, hp, hE, hψ⟩ := hC
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set T := 1 - poiLE (η * L) r with hT
  have hsec : ∀ i k t, ‖secP t (C.ψ i k)‖ ^ 2 = p i k * poi (energy (α i k)) t := by
    intro i k t
    rw [norm_secP_sq, ← coh_sector, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hψ i k, lp.coeFn_smul, Pi.smul_apply, coherent_apply, smul_eq_mul, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hp0 i k)]
  have hin : ∀ i k, HasSum (fun t => binomGT t η r * ‖secP t (C.ψ i k)‖ ^ 2)
      (p i k * (1 - poiLE (η * energy (α i k)) r)) := by
    intro i k
    refine ((poi_tail (η := η) (energy (α i k)) r).mul_left (p i k)).congr_fun fun t => ?_
    rw [hsec]; ring
  have hle : ∀ i k, p i k * (1 - poiLE (η * energy (α i k)) r) ≤ p i k * T := by
    intro i k
    refine mul_le_mul_of_nonneg_left ?_ (hp0 i k)
    have := poiLE_anti (mul_nonneg hη.1 (energy_nonneg (α i k)))
      (mul_le_mul_of_nonneg_left (hE i k) hη.1) r
    rw [hT]; linarith
  have hnn : ∀ i k, 0 ≤ p i k * (1 - poiLE (η * energy (α i k)) r) := fun i k =>
    (hin i k).nonneg fun t => mul_nonneg (binomGT_nonneg hη.1 hη.2 _ _) (by positivity)
  have hi : ∀ i, ∑' k, ∑' t, binomGT t η r * ‖secP t (C.ψ i k)‖ ^ 2 ≤ T := by
    intro i
    simp only [fun k => (hin i k).tsum_eq]
    have hR := (hp i).mul_right T
    rw [one_mul] at hR
    exact hasSum_le (hle i)
      (Summable.of_nonneg_of_le (hnn i) (hle i) hR.summable).hasSum hR
  have htail := (C.hasSum_tail hη r).tsum_eq
  change C.tail η r = _ at htail
  rw [htail, one_div, inv_mul_le_iff₀ hM0]
  calc ∑ i, ∑' k, ∑' t, binomGT t η r * ‖secP t (C.ψ i k)‖ ^ 2
      ≤ ∑ _i : Fin M, T := Finset.sum_le_sum fun i _ => hi i
    _ = M * T := by simp

set_option maxHeartbeats 1000000 in
/-- **M5.** Second-order converse for countable mixtures of coherent states of energy at most
`⌈n N_S⌉`: the dispersion coefficient is `√x g'(x)`, with no factor `√(1-η)`. -/
theorem coherent_converse {η Ns q τ : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop, ∀ (M : ℕ) (C : UCode n M), 1 ≤ M →
      C.IsCoherentMixture (cutoff Ns n) →
      1 - Φ q ≤ C.success (⟨hη0.le, hη1.le⟩ : η ∈ Set.Icc (0 : ℝ) 1) →
        Real.logb 2 M ≤ n * g (η * Ns) + (q * √(η * Ns) * gp (η * Ns) + τ) * √(n : ℝ) := by
  have hηI : η ∈ Set.Icc (0 : ℝ) 1 := ⟨hη0.le, hη1.le⟩
  set x := η * Ns with hx
  have hx0 : 0 < x := mul_pos hη0 hNs
  have hG : 0 < gp x := gp_pos hx0
  have hsx : 0 < √x := Real.sqrt_pos.2 hx0
  set z := q + τ / (2 * (√x * gp x)) with hz
  have hqz : q < z := by
    have : 0 < τ / (2 * (√x * gp x)) := by positivity
    rw [hz]; linarith
  have hΦ := Φ_strictMono hqz
  set γ := (Φ z - Φ q) / 2 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hzG : z * √x * gp x = q * √x * gp x + τ / 2 := by
    rw [hz]; field_simp
  set c0 := Real.logb 2 (4 / γ ^ 2) with hc0
  set D := 3 + 2 * |z| with hD
  have hD0 : 0 ≤ D := by positivity
  have hNlim : Tendsto (fun n : ℕ => ⌈η * (cutoff Ns n : ℝ)⌉₊) atTop atTop := by
    refine tendsto_nat_ceil_atTop.comp ?_
    exact (tendsto_natCast_atTop_atTop.comp (tendsto_cutoff hNs)).const_mul_atTop hη0
  have hclt := (poi_clt z).comp hNlim
  have hev := hclt.eventually (lt_mem_nhds (show Φ q + γ < Φ z by rw [hγ]; linarith))
  have hsqN := (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hNlim))
  filter_upwards [hev, hsqN.eventually_ge_atTop |z|, eventually_ge_atTop 1,
    SecondOrderLog.eventually_sqrt_ge (2 * (|c0| + D * gp x) / τ)] with n hP hsN hn hsn
  intro M C hM hcoh hs
  simp only [Function.comp_apply] at hP hsN
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set L := cutoff Ns n with hL
  have hL1 : (n : ℝ) * Ns ≤ L := Nat.le_ceil _
  have hL2 : (L : ℝ) < n * Ns + 1 := Nat.ceil_lt_add_one (by positivity)
  set N := ⌈η * (L : ℝ)⌉₊ with hN
  have hN1 : η * (L : ℝ) ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) < η * L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hnx : (n : ℝ) * x ≤ η * L := by
    have := mul_le_mul_of_nonneg_left hL1 hη0.le
    rw [hx]; linarith
  have hNlo : (n : ℝ) * x ≤ N := hnx.trans hN1
  have hNhi : (N : ℝ) ≤ n * x + 2 := by
    have := mul_le_mul_of_nonneg_left hL2.le hη0.le
    have e : η * ((n : ℝ) * Ns + 1) = n * x + η := by rw [hx]; ring
    linarith
  have hNnn : (0 : ℝ) ≤ N := by positivity
  set sN := √(N : ℝ) with hsNdef
  have hsN2 : sN * sN = N := Real.mul_self_sqrt hNnn
  have hsN0 : 0 ≤ sN := Real.sqrt_nonneg _
  set y := (N : ℝ) + z * sN with hy
  have hy0 : 0 ≤ y := by
    have h1 : -(|z| * sN) ≤ z * sN := by
      have := neg_abs_le z
      nlinarith
    have h2 : |z| * sN ≤ sN * sN := mul_le_mul_of_nonneg_right hsN hsN0
    rw [hy]; linarith
  set r := ⌈y⌉₊ with hr
  have hr1 : (r : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  -- the tail
  have htail := C.tail_le_of_coherent hηI hM hcoh r
  have hmono : poiLE (N : ℝ) r ≤ poiLE (η * L) r :=
    poiLE_anti (by positivity) hN1 r
  have hsub : ∑ k ∈ range r, poi (N : ℝ) k ≤ poiLE (N : ℝ) r := by
    rw [poiLE, Finset.sum_range_succ]
    linarith [poi_nonneg hNnn r]
  have hw : C.tail η r ≤ 1 - Φ q - γ := by
    have hP' : Φ q + γ < ∑ k ∈ range r, poi (N : ℝ) k := hP
    linarith
  have hconv := unbounded_quantile_conv hηI hM C r hs hγ0 hw
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hch : (0 : ℝ) < ((n + r).choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left r n)
  have hlogM : Real.logb 2 M ≤ c0 + Real.logb 2 ((n + r).choose r : ℝ) := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hMr hconv
    rwa [Real.logb_mul (by positivity) hch.ne'] at h
  have hst := logb_choose_le n r hx0
  -- `√N` versus `√(n x)`
  set sn := √(n : ℝ) with hsndef
  have hsn0 : 0 < sn := Real.sqrt_pos.2 (by linarith)
  have hsnx : √((n : ℝ) * x) = sn * √x := Real.sqrt_mul (by positivity) _
  have hlo : sn * √x ≤ sN := by
    rw [← hsnx]; exact Real.sqrt_le_sqrt hNlo
  have hhi : sN ≤ sn * √x + 2 := by
    have h1 : sN ≤ √((n : ℝ) * x + 2) := Real.sqrt_le_sqrt hNhi
    have h2 : √((n : ℝ) * x + 2) ≤ √((n : ℝ) * x) + √2 :=
      sqrt_add_le _ _ (by positivity) (by norm_num)
    have h3 : √(2 : ℝ) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [hsnx] at h2
    linarith
  have hzs : z * sN ≤ z * (sn * √x) + 2 * |z| := by
    rcases le_total 0 z with h0 | h0
    · rw [abs_of_nonneg h0]; nlinarith
    · rw [abs_of_nonpos h0]; nlinarith
  have hrn : (r : ℝ) - n * x ≤ z * (sn * √x) + D := by
    rw [hD]; linarith
  have h4 := mul_le_mul_of_nonneg_right hrn hG.le
  have e5 : (z * (sn * √x) + D) * gp x = (q * √x * gp x + τ / 2) * sn + D * gp x := by
    rw [← hzG]; ring
  rw [e5] at h4
  have hrem : c0 + D * gp x ≤ τ / 2 * sn := by
    rw [div_le_iff₀ hτ] at hsn
    have := le_abs_self c0
    nlinarith
  nlinarith

/-- **Separation.** For `q < 0` the coherent upper bound lies strictly below the coefficient
achievable by general inputs. -/
theorem coherent_separation {η Ns q : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hq : q < 0) : q * √(η * Ns) * gp (η * Ns) < q * √(Vocc η Ns) := by
  have hx : 0 < η * Ns := mul_pos hη0 hNs
  have hG := gp_pos hx
  rw [← gp_mul_sqrt_eq_sqrt_Vocc hη0 hη1 hNs]
  have hlt : √(η * (1 - η) * Ns) < √(η * Ns) := by
    refine Real.sqrt_lt_sqrt (mul_nonneg (mul_nonneg hη0.le (by linarith)) hNs.le) ?_
    nlinarith [mul_pos hη0 hNs]
  have := mul_lt_mul_of_pos_left hlt hG
  nlinarith

end

end Unbounded

end QIQCOP
