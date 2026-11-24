import QIQCOP.Counting

/-!
# Pure loss on the full `n`-mode Fock space

This file removes the finite photon truncation from the converse.

## Model

* `Fock n = ℓ²(Fin n → ℕ)` is the `n`-mode Fock space in the Fock basis.
* An input state is a **countable pure-state ensemble** `ψ : ℕ → Fock n` with
  `∑ₖ ‖ψ k‖² = 1`, representing `ρ = ∑ₖ |ψ k⟩⟨ψ k|`.  Every density operator on a separable
  Hilbert space has this form by the spectral theorem, and `Tr[Xρ] = ∑ₖ ⟨ψ k, X ψ k⟩`.  The
  spectral theorem itself is not formalized here: the ensemble is the *definition* of an input.
* A POVM is a finite family of positive bounded operators summing to the identity.
* `lossOp hη ℓ` is the Kraus operator
  `(A_ℓ ψ)(m) = ∏ⱼ √(C(mⱼ+ℓⱼ, ℓⱼ) η^{mⱼ} (1-η)^{ℓⱼ}) ψ(m+ℓ)`;
  `lossOp_eq_lossKraus` identifies it with the project's `lossKraus` on truncated vectors.

## Main results

* `lossOp_complete`: `∑_ℓ ‖A_ℓ ψ‖² = ‖ψ‖²`.
* `heisenberg` (M1): `∑_ℓ' ‖(1-Π_r) A_ℓ' ψ‖² = ∑_ℓ Pr{Bin(ℓ,η) > r} ‖Π^{=}_ℓ ψ‖²`.
-/

open Finset
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace QIQCOP

namespace Unbounded

/-- Occupation vectors of `n` modes. -/
abbrev Idx (n : ℕ) := Fin n → ℕ

/-- The `n`-mode Fock space. -/
noncomputable abbrev Fock (n : ℕ) := lp (fun _ : Idx n => ℂ) 2

variable {n : ℕ}

noncomputable section

lemma hasSum_normSq (ψ : Fock n) : HasSum (fun m => ‖ψ m‖ ^ 2) (‖ψ‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) ψ
  simpa using h

/-- Build a Fock vector from a square-summable coefficient function. -/
def mkF (f : Idx n → ℂ) (h : Summable fun m => ‖f m‖ ^ 2) : Fock n :=
  ⟨f, memℓp_gen (by simpa using h)⟩

@[simp] lemma mkF_apply (f : Idx n → ℂ) (h : Summable fun m => ‖f m‖ ^ 2) (m : Idx n) :
    mkF f h m = f m := rfl

/-- Coordinate restriction: the orthogonal projection onto the span of `{|m⟩ : p m}`. -/
def cut (p : Idx n → Prop) [DecidablePred p] (ψ : Fock n) : Fock n :=
  mkF (fun m => if p m then ψ m else 0) (by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_)
      (hasSum_normSq ψ).summable
    split_ifs <;> simp)

@[simp] lemma cut_apply (p : Idx n → Prop) [DecidablePred p] (ψ : Fock n) (m : Idx n) :
    cut p ψ m = if p m then ψ m else 0 := rfl

lemma hasSum_cut (p : Idx n → Prop) [DecidablePred p] (ψ : Fock n) :
    HasSum (fun m => if p m then ‖ψ m‖ ^ 2 else 0) (‖cut p ψ‖ ^ 2) := by
  convert hasSum_normSq (cut p ψ) using 2 with m
  by_cases h : p m <;> simp [h]

/-- `Π_r`: projection onto at most `r` photons. -/
def lowP (r : ℕ) (ψ : Fock n) : Fock n := cut (fun m => photons m ≤ r) ψ

/-- `Π^{=}_t`: projection onto exactly `t` photons. -/
def secP (t : ℕ) (ψ : Fock n) : Fock n := cut (fun m => photons m = t) ψ

/-- `‖Π^{=}_t ψ‖²` is the finite sum of the squared Fock coefficients in sector `t`. -/
lemma norm_secP_sq (t : ℕ) (ψ : Fock n) :
    ‖secP t ψ‖ ^ 2 = ∑ m ∈ sector n t, ‖ψ m‖ ^ 2 := by
  have h := hasSum_cut (fun m => photons m = t) ψ
  have h2 : HasSum (fun m => if photons m = t then ‖ψ m‖ ^ 2 else 0)
      (∑ m ∈ sector n t, (if photons m = t then ‖ψ m‖ ^ 2 else 0)) :=
    hasSum_sum_of_ne_finset_zero fun m hm => by
      rw [if_neg (fun e => hm (mem_sector.2 e))]
  have h3 := h.unique h2
  rw [show secP t ψ = cut (fun m => photons m = t) ψ from rfl, h3]
  exact Finset.sum_congr rfl fun m hm => by rw [if_pos (mem_sector.1 hm)]

/-! ### Kraus weights -/

/-- Squared Kraus coefficient. -/
def lossW (η : ℝ) (ℓ m : Idx n) : ℝ :=
  ∏ j, (((m j + ℓ j).choose (ℓ j) : ℝ) * η ^ (m j) * (1 - η) ^ (ℓ j))

/-- Kraus coefficient `∏ⱼ √(C(mⱼ+ℓⱼ, ℓⱼ) η^{mⱼ} (1-η)^{ℓⱼ})`. -/
def lossCoeff (η : ℝ) (ℓ m : Idx n) : ℝ :=
  ∏ j, √(((m j + ℓ j).choose (ℓ j) : ℝ) * η ^ (m j) * (1 - η) ^ (ℓ j))

/-- Loss patterns compatible with the input occupation `N`. -/
def fiberF (N : Idx n) : Finset (Idx n) := Fintype.piFinset fun j => range (N j + 1)

lemma mem_fiberF {N ℓ : Idx n} : ℓ ∈ fiberF N ↔ ℓ ≤ N := by
  simp only [fiberF, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
  rfl

/-- The binomial weight of the pattern `ℓ` on input `N`. -/
def patW (η : ℝ) (N ℓ : Idx n) : ℝ :=
  ∏ j, ((N j).choose (ℓ j) : ℝ) * η ^ (N j - ℓ j) * (1 - η) ^ (ℓ j)

lemma lossW_sub {η : ℝ} {N ℓ : Idx n} (h : ℓ ≤ N) : lossW η ℓ (N - ℓ) = patW η N ℓ := by
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply, Nat.sub_add_cancel (h j)]

lemma patW_add {η : ℝ} (ℓ m : Idx n) : patW η (m + ℓ) ℓ = lossW η ℓ m := by
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Nat.add_sub_cancel]

section weights
variable {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
include hη

lemma patW_nonneg (N ℓ : Idx n) : 0 ≤ patW η N ℓ :=
  Finset.prod_nonneg fun j _ => by
    have := sub_nonneg.2 hη.2
    have := hη.1
    positivity

lemma lossW_nonneg (ℓ m : Idx n) : 0 ≤ lossW η ℓ m := by
  rw [← patW_add]; exact patW_nonneg hη _ _

lemma lossCoeff_sq (ℓ m : Idx n) : lossCoeff η ℓ m ^ 2 = lossW η ℓ m := by
  rw [lossCoeff, lossW, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => Real.sq_sqrt ?_
  have := sub_nonneg.2 hη.2
  have := hη.1
  positivity

lemma sum_patW (N : Idx n) : ∑ ℓ ∈ fiberF N, patW η N ℓ = 1 := sum_le_binom η N

lemma lossW_le_one (ℓ m : Idx n) : lossW η ℓ m ≤ 1 := by
  rw [← patW_add, ← sum_patW hη (m + ℓ)]
  exact Finset.single_le_sum (f := fun i => patW η (m + ℓ) i)
    (fun i _ => patW_nonneg hη _ i) (mem_fiberF.2 le_add_self)

end weights

/-! ### The Kraus operators -/

section ops
variable {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)

lemma add_right_inj' (ℓ : Idx n) : Function.Injective fun m : Idx n => m + ℓ :=
  add_left_injective ℓ

include hη in
lemma norm_coeff_sq (ℓ m : Idx n) (z : ℂ) :
    ‖(lossCoeff η ℓ m : ℂ) * z‖ ^ 2 = lossW η ℓ m * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, lossCoeff_sq hη]

include hη in
lemma summable_loss (ℓ : Idx n) (ψ : Fock n) :
    Summable fun m => ‖(lossCoeff η ℓ m : ℂ) * ψ (m + ℓ)‖ ^ 2 := by
  have h0 : Summable fun m : Idx n => ‖ψ (m + ℓ)‖ ^ 2 :=
    (hasSum_normSq ψ).summable.comp_injective (add_right_inj' ℓ)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) h0
  rw [norm_coeff_sq hη]
  exact mul_le_of_le_one_left (by positivity) (lossW_le_one hη ℓ m)

/-- The Kraus operator `A_ℓ` on Fock space. -/
def lossOp (ℓ : Idx n) : Fock n →L[ℂ] Fock n :=
  LinearMap.mkContinuous
    { toFun := fun ψ => mkF (fun m => (lossCoeff η ℓ m : ℂ) * ψ (m + ℓ)) (summable_loss hη ℓ ψ)
      map_add' := fun a b => by
        ext m
        simp [mul_add]
      map_smul' := fun c a => by
        ext m
        simp only [mkF_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring } 1
    (fun ψ => by
      simp only [one_mul]
      refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
      have h1 := hasSum_normSq (mkF (fun m => (lossCoeff η ℓ m : ℂ) * ψ (m + ℓ))
        (summable_loss hη ℓ ψ))
      have h0 : Summable fun m : Idx n => ‖ψ (m + ℓ)‖ ^ 2 :=
        (hasSum_normSq ψ).summable.comp_injective (add_right_inj' ℓ)
      have h2 : ∑' m : Idx n, ‖ψ (m + ℓ)‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
        rw [← (hasSum_normSq ψ).tsum_eq]
        exact _root_.tsum_comp_le_tsum_of_inj (hasSum_normSq ψ).summable
          (fun _ => by positivity) (add_right_inj' ℓ)
      refine le_trans (hasSum_le (fun m => ?_) h1 h0.hasSum) h2
      simp only [mkF_apply]
      rw [norm_coeff_sq hη]
      exact mul_le_of_le_one_left (by positivity) (lossW_le_one hη ℓ m))

@[simp] lemma lossOp_apply (ℓ : Idx n) (ψ : Fock n) (m : Idx n) :
    lossOp hη ℓ ψ m = (lossCoeff η ℓ m : ℂ) * ψ (m + ℓ) := rfl

end ops

/-! ### Tonelli over loss patterns -/

/-- `(ℓ, m) ↦ (m + ℓ, ℓ)`, the reindexing of output coordinates by the input coordinate. -/
def fibEquiv (n : ℕ) : Idx n × Idx n ≃ Σ N : Idx n, ↥(fiberF N) where
  toFun p := ⟨p.2 + p.1, p.1, mem_fiberF.2 le_add_self⟩
  invFun s := (s.2.1, s.1 - s.2.1)
  left_inv p := by
    ext j <;> simp
  right_inv := by
    rintro ⟨N, ℓ, hℓ⟩
    refine Sigma.subtype_ext ?_ rfl
    exact tsub_add_cancel_of_le (mem_fiberF.1 hℓ)

/-- The number-resolved transition weight from input `N`. -/
def transW (η : ℝ) (h : ℕ → ℝ) (N : Idx n) : ℝ :=
  ∑ ℓ ∈ fiberF N, h (photons (N - ℓ)) * patW η N ℓ

lemma transW_nonneg {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) {h : ℕ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    (N : Idx n) : 0 ≤ transW η h N :=
  Finset.sum_nonneg fun ℓ _ => mul_nonneg (h0 _) (patW_nonneg hη _ _)

lemma transW_le_one {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) {h : ℕ → ℝ} (h1 : ∀ t, h t ≤ 1)
    (N : Idx n) : transW η h N ≤ 1 := by
  rw [← sum_patW hη N]
  exact Finset.sum_le_sum fun ℓ _ =>
    mul_le_of_le_one_left (patW_nonneg hη _ _) (h1 _)

/-- Tonelli for the loss patterns: output weight filtered by `h(photons)` equals the input
weight against the transition weight. -/
theorem loss_fiber {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) {h : ℕ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    (h1 : ∀ t, h t ≤ 1) {a : Idx n → ℝ} (ha0 : ∀ m, 0 ≤ a m) (ha : Summable a) :
    (∀ ℓ : Idx n, Summable fun m => h (photons m) * lossW η ℓ m * a (m + ℓ)) ∧
    HasSum (fun ℓ : Idx n => ∑' m, h (photons m) * lossW η ℓ m * a (m + ℓ))
      (∑' N, a N * transW η h N) := by
  set φ : Idx n × Idx n → ℝ := fun p => h (photons p.2) * lossW η p.1 p.2 * a (p.2 + p.1) with hφ
  have hφ0 : ∀ p, 0 ≤ φ p := fun p =>
    mul_nonneg (mul_nonneg (h0 _) (lossW_nonneg hη _ _)) (ha0 _)
  set φ' : (Σ N : Idx n, ↥(fiberF N)) → ℝ := φ ∘ (fibEquiv n).symm with hφ'
  have hin : ∀ N : Idx n, HasSum (fun c : ↥(fiberF N) => φ' ⟨N, c⟩) (a N * transW η h N) := by
    intro N
    have e : ∀ c : ↥(fiberF N), φ' ⟨N, c⟩ =
        a N * (h (photons (N - c.1)) * patW η N c.1) := by
      rintro ⟨ℓ, hℓ⟩
      have hle := mem_fiberF.1 hℓ
      simp only [hφ', hφ, Function.comp_apply, fibEquiv, Equiv.coe_fn_symm_mk]
      rw [lossW_sub hle, tsub_add_cancel_of_le hle]
      ring
    have hs : HasSum (fun c : ↥(fiberF N) => a N * (h (photons (N - c.1)) * patW η N c.1))
        (∑ c : ↥(fiberF N), a N * (h (photons (N - c.1)) * patW η N c.1)) := hasSum_fintype _
    rw [Finset.sum_coe_sort (fiberF N) (fun ℓ => a N * (h (photons (N - ℓ)) * patW η N ℓ)),
      ← Finset.mul_sum] at hs
    exact (hs.congr_fun e)
  have hT : Summable fun N => a N * transW η h N :=
    Summable.of_nonneg_of_le (fun N => mul_nonneg (ha0 N) (transW_nonneg hη h0 N))
      (fun N => mul_le_of_le_one_right (ha0 N) (transW_le_one hη h1 N)) ha
  have hφ's : Summable φ' := by
    refine (summable_sigma_of_nonneg (f := φ') (fun x => hφ0 _)).2
      ⟨fun N => (hin N).summable, ?_⟩
    simpa only [(hin _).tsum_eq] using hT
  have hsig : HasSum φ' (∑' N, a N * transW η h N) :=
    HasSum.sigma_of_hasSum hT.hasSum hin hφ's
  have hprod : HasSum φ (∑' N, a N * transW η h N) := by
    have := (Equiv.hasSum_iff (fibEquiv n).symm (f := φ)).1 hsig
    exact this
  have hsl : ∀ ℓ : Idx n, Summable fun m => φ (ℓ, m) := fun ℓ =>
    hprod.summable.comp_injective (Prod.mk_right_injective ℓ)
  refine ⟨hsl, ?_⟩
  exact hprod.prod_fiberwise fun ℓ => (hsl ℓ).hasSum

/-- Reindexing the Fock basis by total photon number. -/
def photonEquiv (n : ℕ) : Idx n ≃ Σ t : ℕ, ↥(sector n t) where
  toFun m := ⟨photons m, m, mem_sector.2 rfl⟩
  invFun s := s.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨t, m, hm⟩
    exact Sigma.subtype_ext (mem_sector.1 hm) rfl

/-- Grouping a summable family by total photon number. -/
theorem photon_fiber {a : Idx n → ℝ} {f : ℕ → ℝ}
    (hs : Summable fun N => a N * f (photons N)) :
    HasSum (fun t => f t * ∑ m ∈ sector n t, a m) (∑' N, a N * f (photons N)) := by
  set φ : (Σ t : ℕ, ↥(sector n t)) → ℝ := (fun N => a N * f (photons N)) ∘ (photonEquiv n).symm
    with hφ
  have hsig : HasSum φ (∑' N, a N * f (photons N)) :=
    (Equiv.hasSum_iff (photonEquiv n).symm).2 hs.hasSum
  refine hsig.sigma fun t => ?_
  have e : ∀ c : ↥(sector n t), φ ⟨t, c⟩ = f t * a c.1 := by
    rintro ⟨m, hm⟩
    simp only [hφ, Function.comp_apply, photonEquiv, Equiv.coe_fn_symm_mk]
    rw [mem_sector.1 hm, mul_comm]
  have h2 : HasSum (fun c : ↥(sector n t) => f t * a c.1)
      (∑ c : ↥(sector n t), f t * a c.1) := hasSum_fintype _
  rw [Finset.sum_coe_sort (sector n t) (fun m => f t * a m), ← Finset.mul_sum] at h2
  exact h2.congr_fun e

/-! ### Completeness and the Heisenberg identity -/

section main
variable {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
include hη

lemma summable_a (ψ : Fock n) : Summable fun m => ‖ψ m‖ ^ 2 := (hasSum_normSq ψ).summable

/-- Filtered output weight of one Kraus branch. -/
lemma norm_cut_loss (p : ℕ → Prop) [DecidablePred p] (ℓ : Idx n) (ψ : Fock n) :
    ‖cut (fun m => p (photons m)) (lossOp hη ℓ ψ)‖ ^ 2 =
      ∑' m, (if p (photons m) then (1 : ℝ) else 0) * lossW η ℓ m * ‖ψ (m + ℓ)‖ ^ 2 := by
  rw [← (hasSum_cut (fun m => p (photons m)) (lossOp hη ℓ ψ)).tsum_eq]
  refine tsum_congr fun m => ?_
  rw [lossOp_apply, norm_coeff_sq hη]
  split_ifs <;> simp

/-- Output law of the filtered branches, in terms of the input coefficients. -/
theorem hasSum_cut_loss (p : ℕ → Prop) [DecidablePred p] (ψ : Fock n) :
    HasSum (fun ℓ : Idx n => ‖cut (fun m => p (photons m)) (lossOp hη ℓ ψ)‖ ^ 2)
      (∑' N, ‖ψ N‖ ^ 2 * transW η (fun t => if p t then 1 else 0) N) := by
  have h := (loss_fiber hη (h := fun t => if p t then (1 : ℝ) else 0)
    (fun t => by split_ifs <;> norm_num) (fun t => by split_ifs <;> norm_num)
    (a := fun m => ‖ψ m‖ ^ 2) (fun m => by positivity) (summable_a hη ψ)).2
  exact h.congr_fun fun ℓ => norm_cut_loss hη p ℓ ψ

/-- `∑_ℓ ‖A_ℓ ψ‖² = ‖ψ‖²`. -/
theorem lossOp_complete (ψ : Fock n) :
    HasSum (fun ℓ : Idx n => ‖lossOp hη ℓ ψ‖ ^ 2) (‖ψ‖ ^ 2) := by
  have h := hasSum_cut_loss hη (fun _ => True) ψ
  have e1 : ∀ ℓ : Idx n, cut (fun m => (fun _ : ℕ => True) (photons m)) (lossOp hη ℓ ψ) =
      lossOp hη ℓ ψ := fun ℓ => by
    ext m; simp
  have e2 : ∀ N : Idx n, transW η (fun t => if (fun _ : ℕ => True) t then (1 : ℝ) else 0) N = 1 := by
    intro N
    simp only [transW, if_true, one_mul]
    exact sum_patW hη N
  simp only [e1, e2, mul_one] at h
  rwa [(hasSum_normSq ψ).tsum_eq] at h

lemma transW_gt (r : ℕ) (N : Idx n) :
    transW η (fun t => if r < t then 1 else 0) N = binomGT (photons N) η r := by
  rw [← sum_survivors_gt η N r]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases h : r < photons (N - ℓ) <;> simp [h, patW]

lemma transW_eq (k : ℕ) (N : Idx n) :
    transW η (fun t => if t = k then 1 else 0) N = binomPMF (photons N) η k := by
  rw [← sum_survivors_eq η N k]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases h : photons (N - ℓ) = k <;> simp [h, patW]

/-- `1 - Π_r` acts as restriction to more than `r` photons. -/
lemma sub_lowP (r : ℕ) (v : Fock n) : v - lowP r v = cut (fun m => r < photons m) v := by
  ext m
  simp only [lp.coeFn_sub, Pi.sub_apply, lowP, cut_apply]
  by_cases h : photons m ≤ r
  · simp [h, not_lt.2 h]
  · simp [h, not_le.1 h]

/-- Pointwise boundedness makes the binomial-tail weight summable. -/
lemma summable_binomGT (r : ℕ) (ψ : Fock n) :
    Summable fun N => ‖ψ N‖ ^ 2 * binomGT (photons N) η r :=
  Summable.of_nonneg_of_le
    (fun N => mul_nonneg (by positivity) (binomGT_nonneg hη.1 hη.2 _ _))
    (fun N => mul_le_of_le_one_right (by positivity) (binomGT_le_one hη.1 hη.2 _ _))
    (summable_a hη ψ)

/-- **M1 (Heisenberg identity on Fock space).**
`∑_ℓ' ‖(1-Π_r) A_ℓ' ψ‖² = ∑_ℓ Pr{Bin(ℓ,η) > r} ‖Π^{=}_ℓ ψ‖²`, for every `ψ`,
including vectors with coherences between photon-number sectors. -/
theorem heisenberg (r : ℕ) (ψ : Fock n) :
    Summable (fun t => binomGT t η r * ‖secP t ψ‖ ^ 2) ∧
    HasSum (fun ℓ' : Idx n => ‖lossOp hη ℓ' ψ - lowP r (lossOp hη ℓ' ψ)‖ ^ 2)
      (∑' t, binomGT t η r * ‖secP t ψ‖ ^ 2) := by
  have hf := photon_fiber (a := fun m => ‖ψ m‖ ^ 2) (f := fun t => binomGT t η r)
    (summable_binomGT hη r ψ)
  simp only [← norm_secP_sq] at hf
  refine ⟨hf.summable, ?_⟩
  have h := hasSum_cut_loss hη (fun t => r < t) ψ
  simp only [transW_gt hη] at h
  rw [hf.tsum_eq]
  refine h.congr_fun fun ℓ' => ?_
  rw [sub_lowP hη]

end main

/-- **Compatibility** with the project's truncated `lossKraus`: on a vector supported on at most
`L` photons, `lossOp` acts on the coordinates in `Occ n L` as the matrix `lossKraus η ℓ`. -/
theorem lossOp_eq_lossKraus {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) {L : ℕ} (ℓ : Occ n L)
    (ψ : Fock n) (hψ : ∀ m, L < photons m → ψ m = 0) (r : Occ n L) :
    lossOp hη ℓ.1 ψ r.1 =
      (lossKraus η ℓ).mulVec (fun m : Occ n L => ψ m.1) r := by
  classical
  simp only [lossOp_apply, Matrix.mulVec, dotProduct, lossKraus]
  by_cases hm : photons ((r : Idx n) + (ℓ : Idx n)) ≤ L
  · have hmem : (r : Idx n) + (ℓ : Idx n) ∈ occSet n L := mem_occSet.2 hm
    rw [Finset.sum_eq_single (⟨_, hmem⟩ : Occ n L)]
    · simp only [if_true, lossCoeff, Pi.add_apply]
    · intro b _ hb
      rw [if_neg, zero_mul]
      intro e
      exact hb (Subtype.ext e)
    · simp
  · rw [hψ _ (not_le.1 hm), mul_zero]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    rw [if_neg, zero_mul]
    intro e
    exact hm (e ▸ mem_occSet.1 b.2)

end

end Unbounded

end QIQCOP
