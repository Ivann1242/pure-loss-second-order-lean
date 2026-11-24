import QIQCOP.Unbounded

/-!
# Codes over the full Fock space and the output-projector bound (M2)

* `UCode n M`: `M` inputs, each a countable pure-state ensemble in `Fock n`, and a POVM.
* `UCode.success`, `UCode.law`, `UCode.leak`, `UCode.tail`, `UCode.mean`.
* `output_projector_bound`: `success ≤ (√(C(n+r,r)/M) + √w_r)²`, `w_r = ∑_ℓ P(ℓ) Pr{Bin(ℓ,η)>r}`.
* `unbounded_quantile_conv`: if `1-ε ≤ success`, `0 < γ`, `w_r ≤ 1-ε-γ` then
  `M ≤ 4/γ² · C(n+r,r)`.
-/

open Finset
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace QIQCOP

namespace Unbounded

variable {n M : ℕ}

noncomputable section

/-! ### Summation helpers -/

lemma hasSum_prod_of_nonneg {α β : Type*} {F : α → β → ℝ} (h0 : ∀ a b, 0 ≤ F a b) {b : α → ℝ}
    {B : ℝ} (hF : ∀ a, HasSum (F a) (b a)) (hb : HasSum b B) :
    HasSum (fun x : α × β => F x.1 x.2) B := by
  have hs : Summable (fun x : α × β => F x.1 x.2) :=
    (summable_prod_of_nonneg (fun x => h0 _ _)).2
      ⟨fun a => (hF a).summable, by simpa only [(hF _).tsum_eq] using hb.summable⟩
  have h := hs.hasSum.prod_fiberwise (fun a => hF a)
  have e : ∑' x : α × β, F x.1 x.2 = B := h.unique hb
  rw [← e]
  exact hs.hasSum

lemma hasSum_swap {α β : Type*} {F : α → β → ℝ} (h0 : ∀ a b, 0 ≤ F a b) {b : α → ℝ} {B : ℝ}
    (hF : ∀ a, HasSum (F a) (b a)) (hb : HasSum b B) :
    (∀ t, Summable fun k => F k t) ∧ HasSum (fun t => ∑' k, F k t) B := by
  have h := hasSum_prod_of_nonneg h0 hF hb
  have h' : HasSum (fun x : β × α => F x.2 x.1) B :=
    (Equiv.prodComm β α).hasSum_iff.2 h
  have hs : ∀ t, Summable fun k => F k t := fun t =>
    h'.summable.comp_injective (Prod.mk_right_injective t)
  exact ⟨hs, h'.prod_fiberwise fun t => (hs t).hasSum⟩

/-! ### Quadratic forms of positive operators -/

/-- The quadratic form `y ↦ Re⟨y, T y⟩`. -/
def qf (T : Fock n →L[ℂ] Fock n) (y : Fock n) : ℝ := (inner ℂ y (T y)).re

/-- A positive operator on a complex Hilbert space is `b† b`. -/
lemma exists_root_gen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {T : E →L[ℂ] E} (hT : T.IsPositive) :
    ∃ b : E →L[ℂ] E, ∀ y, (inner ℂ y (T y)).re = ‖b y‖ ^ 2 := by
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1
    (ContinuousLinearMap.nonneg_iff_isPositive.2 hT)
  refine ⟨b, fun y => ?_⟩
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

lemma exists_root {T : Fock n →L[ℂ] Fock n} (hT : T.IsPositive) :
    ∃ b : Fock n →L[ℂ] Fock n, ∀ y, qf T y = ‖b y‖ ^ 2 :=
  exists_root_gen hT

lemma qf_nonneg {T : Fock n →L[ℂ] Fock n} (hT : T.IsPositive) (y : Fock n) : 0 ≤ qf T y := by
  obtain ⟨b, hb⟩ := exists_root hT
  rw [hb]; positivity

/-- Young's inequality for a positive form. -/
lemma qf_add_le {T : Fock n →L[ℂ] Fock n} (hT : T.IsPositive) (u w : Fock n) {t : ℝ}
    (ht : 0 < t) : qf T (u + w) ≤ (1 + t) * qf T u + (1 + 1 / t) * qf T w := by
  obtain ⟨b, hb⟩ := exists_root hT
  simp only [hb, map_add]
  have h1 := norm_add_le (b u) (b w)
  set x := ‖b u‖
  set y := ‖b w‖
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have h2 : ‖b u + b w‖ ^ 2 ≤ (x + y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (x + y) ^ 2 ≤ (1 + t) * x ^ 2 + (1 + 1 / t) * y ^ 2 := by
    have : (1 + t) * x ^ 2 + (1 + 1 / t) * y ^ 2 - (x + y) ^ 2 = (t * x - y) ^ 2 / t := by
      field_simp
      ring
    have h4 : 0 ≤ (t * x - y) ^ 2 / t := by positivity
    linarith
  linarith

/-- The Fock basis vector `|a⟩`. -/
def ket (a : Idx n) : Fock n := lp.single 2 a (1 : ℂ)

lemma norm_ket (a : Idx n) : ‖ket (n := n) a‖ = 1 := by
  simp [ket, lp.norm_single]

lemma lowP_eq_sum (r : ℕ) (v : Fock n) :
    lowP r v = ∑ a ∈ occSet n r, (v a) • ket a := by
  classical
  ext m
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lowP, cut_apply, ket, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hm : photons m ≤ r
  · rw [if_pos hm, Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      simp [lp.single_apply, Ne.symm hb]
    · intro h
      exact absurd (mem_occSet.2 hm) h
  · rw [if_neg hm]
    refine (Finset.sum_eq_zero fun b hb => ?_).symm
    have : m ≠ b := fun e => hm (e ▸ mem_occSet.1 hb)
    simp [lp.single_apply, this]

/-- On the low-photon space, a positive form is bounded by its trace times the squared norm. -/
lemma qf_lowP_le {T : Fock n →L[ℂ] Fock n} (hT : T.IsPositive) (r : ℕ) (v : Fock n) :
    qf T (lowP r v) ≤ (∑ a ∈ occSet n r, qf T (ket a)) * ‖v‖ ^ 2 := by
  obtain ⟨b, hb⟩ := exists_root hT
  simp only [hb]
  have h1 : ‖b (lowP r v)‖ ≤ ∑ a ∈ occSet n r, ‖v a‖ * ‖b (ket a)‖ := by
    rw [lowP_eq_sum, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [map_smul, norm_smul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (occSet n r) (fun a => ‖v a‖) (fun a => ‖b (ket a)‖)
  have h3 : ∑ a ∈ occSet n r, ‖v a‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    sum_le_hasSum _ (fun _ _ => by positivity) (hasSum_normSq v)
  calc ‖b (lowP r v)‖ ^ 2 ≤ (∑ a ∈ occSet n r, ‖v a‖ * ‖b (ket a)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ ≤ ‖v‖ ^ 2 * ∑ a ∈ occSet n r, ‖b (ket a)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (Finset.sum_nonneg fun _ _ => by positivity)
    _ = _ := mul_comm _ _

/-! ### Codes -/

/-- A code on the full Fock space: each message is a countable pure-state ensemble
`ρᵢ = ∑ₖ |ψᵢₖ⟩⟨ψᵢₖ|`, and the decoder is a POVM. -/
structure UCode (n M : ℕ) where
  /-- Ensemble vectors. -/
  ψ : Fin M → ℕ → Fock n
  /-- Unit trace of each input state. -/
  hψ : ∀ i, HasSum (fun k => ‖ψ i k‖ ^ 2) 1
  /-- POVM elements. -/
  Λ : Fin M → Fock n →L[ℂ] Fock n
  /-- Positivity. -/
  pos : ∀ i, (Λ i).IsPositive
  /-- Completeness. -/
  povm : ∑ i, Λ i = 1

namespace UCode

variable (C : UCode n M)

/-- `Pr{i-th input has t photons}`. -/
def lawI (i : Fin M) (t : ℕ) : ℝ := ∑' k, ‖secP t (C.ψ i k)‖ ^ 2

/-- The photon law `P(t) = (1/M) ∑ᵢ ∑ₖ ‖Π^{=}_t ψᵢₖ‖²`. -/
def law (t : ℕ) : ℝ := (1 / (M : ℝ)) * ∑ i, C.lawI i t

/-- Leakage above `L` photons. -/
def leak (L : ℕ) : ℝ := ∑' t, if L < t then C.law t else 0

/-- `w_r = ∑_t P(t) Pr{Bin(t,η) > r}`. -/
def tail (η : ℝ) (r : ℕ) : ℝ := ∑' t, C.law t * binomGT t η r

/-- Mean photon number `∑_t t P(t)`. Theorems about it assume summability explicitly. -/
def mean : ℝ := ∑' t : ℕ, (t : ℝ) * C.law t

/-- Average success probability through the loss channel. -/
def success {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) : ℝ :=
  (1 / (M : ℝ)) * ∑ i, ∑' k, ∑' ℓ : Idx n,
    (inner ℂ (lossOp hη ℓ (C.ψ i k)) (C.Λ i (lossOp hη ℓ (C.ψ i k)))).re

lemma qf_le_norm (i : Fin M) (v : Fock n) : qf (C.Λ i) v ≤ ‖v‖ ^ 2 := by
  have hsum : ∑ j, qf (C.Λ j) v = ‖v‖ ^ 2 := by
    have : ∑ j, qf (C.Λ j) v = (inner ℂ v ((∑ j, C.Λ j) v)).re := by
      simp only [qf, ContinuousLinearMap.sum_apply, inner_sum, Complex.re_sum]
    rw [this, C.povm, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [← hsum]
  exact Finset.single_le_sum (f := fun j => qf (C.Λ j) v)
    (fun j _ => qf_nonneg (C.pos j) v) (Finset.mem_univ i)

/-- Each input's photon-number distribution sums to one. -/
lemma hasSum_sec (ψ : Fock n) : HasSum (fun t => ‖secP t ψ‖ ^ 2) (‖ψ‖ ^ 2) := by
  have h := photon_fiber (a := fun m => ‖ψ m‖ ^ 2) (f := fun _ => 1)
    (by simpa using (hasSum_normSq ψ).summable)
  simp only [one_mul, mul_one, ← norm_secP_sq] at h
  rwa [(hasSum_normSq ψ).tsum_eq] at h

lemma lawI_spec (i : Fin M) :
    (∀ t, Summable fun k => ‖secP t (C.ψ i k)‖ ^ 2) ∧ HasSum (C.lawI i) 1 :=
  hasSum_swap (F := fun k t => ‖secP t (C.ψ i k)‖ ^ 2) (fun _ _ => by positivity)
    (fun k => hasSum_sec (C.ψ i k)) (C.hψ i)

lemma lawI_nonneg (i : Fin M) (t : ℕ) : 0 ≤ C.lawI i t :=
  tsum_nonneg fun _ => by positivity

lemma law_nonneg (t : ℕ) : 0 ≤ C.law t :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => C.lawI_nonneg i t)

lemma hasSum_law (hM : 1 ≤ M) : HasSum C.law 1 := by
  have h := (hasSum_sum (s := Finset.univ) fun i _ => (C.lawI_spec i).2).mul_left (1 / (M : ℝ))
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  rw [one_div_mul_cancel hM0] at h
  exact h

/-- Per-message weighted law, as a sum over the ensemble. -/
lemma hasSum_lawI_weight (i : Fin M) {f : ℕ → ℝ} (f0 : ∀ t, 0 ≤ f t) (f1 : ∀ t, f t ≤ 1) :
    HasSum (fun t => C.lawI i t * f t) (∑' k, ∑' t, f t * ‖secP t (C.ψ i k)‖ ^ 2) := by
  set F : ℕ → ℕ → ℝ := fun k t => f t * ‖secP t (C.ψ i k)‖ ^ 2 with hF
  have hF0 : ∀ k t, 0 ≤ F k t := fun k t => mul_nonneg (f0 t) (by positivity)
  have hFs : ∀ k, Summable (F k) := fun k =>
    Summable.of_nonneg_of_le (hF0 k) (fun t => mul_le_of_le_one_left (by positivity) (f1 t))
      (hasSum_sec (C.ψ i k)).summable
  have hb : Summable fun k => ∑' t, F k t := by
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg (hF0 k)) (fun k => ?_)
      (C.hψ i).summable
    rw [← (hasSum_sec (C.ψ i k)).tsum_eq]
    exact (hFs k).tsum_le_tsum (fun t => mul_le_of_le_one_left (by positivity) (f1 t))
      (hasSum_sec (C.ψ i k)).summable
  have h := (hasSum_swap hF0 (fun k => (hFs k).hasSum) hb.hasSum).2
  refine h.congr_fun fun t => ?_
  simp only [hF, lawI]
  rw [tsum_mul_left, mul_comm]

lemma hasSum_tail {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (r : ℕ) :
    HasSum (fun t => C.law t * binomGT t η r)
      ((1 / (M : ℝ)) * ∑ i, ∑' k, ∑' t, binomGT t η r * ‖secP t (C.ψ i k)‖ ^ 2) := by
  have h := (hasSum_sum (s := Finset.univ) fun i _ => C.hasSum_lawI_weight i
    (f := fun t => binomGT t η r) (fun t => binomGT_nonneg hη.1 hη.2 _ _)
    (fun t => binomGT_le_one hη.1 hη.2 _ _)).mul_left (1 / (M : ℝ))
  refine h.congr_fun fun t => ?_
  simp only [law, Finset.sum_mul, Finset.mul_sum, mul_assoc]

lemma tail_nonneg {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (r : ℕ) : 0 ≤ C.tail η r :=
  tsum_nonneg fun t => mul_nonneg (C.law_nonneg t) (binomGT_nonneg hη.1 hη.2 _ _)

/-- Ensemble of branch vectors of the `i`-th output. -/
def branch {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (i : Fin M) (x : ℕ × Idx n) : Fock n :=
  lossOp hη x.2 (C.ψ i x.1)

lemma hasSum_branch {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (i : Fin M) :
    HasSum (fun x => ‖C.branch hη i x‖ ^ 2) 1 :=
  hasSum_prod_of_nonneg (F := fun k ℓ => ‖lossOp hη ℓ (C.ψ i k)‖ ^ 2)
    (fun _ _ => by positivity) (fun k => lossOp_complete hη (C.ψ i k)) (C.hψ i)

lemma hasSum_branch_high {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (i : Fin M) (r : ℕ) :
    HasSum (fun x => ‖C.branch hη i x - lowP r (C.branch hη i x)‖ ^ 2)
      (∑' k, ∑' t, binomGT t η r * ‖secP t (C.ψ i k)‖ ^ 2) := by
  have hs : Summable fun k => ∑' t, binomGT t η r * ‖secP t (C.ψ i k)‖ ^ 2 := by
    refine Summable.of_nonneg_of_le
      (fun k => tsum_nonneg fun t => mul_nonneg (binomGT_nonneg hη.1 hη.2 _ _) (by positivity))
      (fun k => ?_) (C.hψ i).summable
    rw [← (hasSum_sec (C.ψ i k)).tsum_eq]
    exact (heisenberg hη r (C.ψ i k)).1.tsum_le_tsum
      (fun t => mul_le_of_le_one_left (by positivity) (binomGT_le_one hη.1 hη.2 _ _))
      (hasSum_sec (C.ψ i k)).summable
  exact hasSum_prod_of_nonneg
    (F := fun k ℓ => ‖lossOp hη ℓ (C.ψ i k) - lowP r (lossOp hη ℓ (C.ψ i k))‖ ^ 2)
    (fun _ _ => by positivity) (fun k => (heisenberg hη r (C.ψ i k)).2) hs.hasSum

/-- The `i`-th message's contribution to the success probability, as a sum over branches. -/
lemma success_term {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (i : Fin M) :
    Summable (fun x => qf (C.Λ i) (C.branch hη i x)) ∧
    ∑' k, ∑' ℓ : Idx n, (inner ℂ (lossOp hη ℓ (C.ψ i k)) (C.Λ i (lossOp hη ℓ (C.ψ i k)))).re =
      ∑' x, qf (C.Λ i) (C.branch hη i x) := by
  have hs : Summable (fun x => qf (C.Λ i) (C.branch hη i x)) :=
    Summable.of_nonneg_of_le (fun x => qf_nonneg (C.pos i) _) (fun x => C.qf_le_norm i _)
      (C.hasSum_branch hη i).summable
  refine ⟨hs, ?_⟩
  exact (hs.tsum_prod).symm

theorem success_le_one {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hM : 1 ≤ M) :
    C.success hη ≤ 1 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hi : ∀ i, ∑' x, qf (C.Λ i) (C.branch hη i x) ≤ 1 := fun i =>
    hasSum_le (fun x => C.qf_le_norm i _) (C.success_term hη i).1.hasSum (C.hasSum_branch hη i)
  rw [success]
  simp only [fun i => (C.success_term hη i).2]
  have h2 : ∑ i, ∑' x, qf (C.Λ i) (C.branch hη i x) ≤ M := by
    calc _ ≤ ∑ _i : Fin M, (1 : ℝ) := Finset.sum_le_sum fun i _ => hi i
      _ = M := by simp
  rw [one_div, inv_mul_le_iff₀ hM0]
  linarith

/-- Trace of the POVM over the `≤ r` photon space. -/
lemma sum_trace (r : ℕ) :
    ∑ i, ∑ a ∈ occSet n r, qf (C.Λ i) (ket a) = ((n + r).choose r : ℝ) := by
  rw [Finset.sum_comm]
  have h : ∀ a ∈ occSet n r, ∑ i, qf (C.Λ i) (ket a) = 1 := by
    intro a _
    have : ∑ j, qf (C.Λ j) (ket a) = (inner ℂ (ket a) ((∑ j, C.Λ j) (ket a))).re := by
      simp only [qf, ContinuousLinearMap.sum_apply, inner_sum, Complex.re_sum]
    rw [this, C.povm, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, norm_ket]
    norm_num
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_occSet]
  simp

/-- Young-form bound, for each `t > 0`. -/
theorem success_le_young {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hM : 1 ≤ M) (r : ℕ) {t : ℝ}
    (ht : 0 < t) :
    C.success hη ≤ (1 + t) * (((n + r).choose r : ℝ) / M) + (1 + 1 / t) * C.tail η r := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set W : Fin M → ℝ := fun i => ∑' k, ∑' t, binomGT t η r * ‖secP t (C.ψ i k)‖ ^ 2 with hW
  set Tr : Fin M → ℝ := fun i => ∑ a ∈ occSet n r, qf (C.Λ i) (ket a) with hTr
  have hi : ∀ i, ∑' x, qf (C.Λ i) (C.branch hη i x) ≤ (1 + t) * Tr i + (1 + 1 / t) * W i := by
    intro i
    have hR : HasSum (fun x => (1 + t) * (Tr i * ‖C.branch hη i x‖ ^ 2) +
        (1 + 1 / t) * ‖C.branch hη i x - lowP r (C.branch hη i x)‖ ^ 2)
        ((1 + t) * (Tr i * 1) + (1 + 1 / t) * W i) :=
      (((C.hasSum_branch hη i).mul_left (Tr i)).mul_left (1 + t)).add
        ((C.hasSum_branch_high hη i r).mul_left (1 + 1 / t))
    rw [mul_one] at hR
    refine hasSum_le (fun x => ?_) (C.success_term hη i).1.hasSum hR
    set v := C.branch hη i x
    have hsplit : v = lowP r v + (v - lowP r v) := by abel
    have h1 := qf_add_le (C.pos i) (lowP r v) (v - lowP r v) ht
    rw [← hsplit] at h1
    have h2 := qf_lowP_le (C.pos i) r v
    have h3 := C.qf_le_norm i (v - lowP r v)
    have h4 : (1 + t) * qf (C.Λ i) (lowP r v) ≤ (1 + t) * (Tr i * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h5 : (1 + 1 / t) * qf (C.Λ i) (v - lowP r v) ≤
        (1 + 1 / t) * ‖v - lowP r v‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have htail : C.tail η r = (1 / (M : ℝ)) * ∑ i, W i := (C.hasSum_tail hη r).tsum_eq
  have hD : ((n + r).choose r : ℝ) / M = (1 / (M : ℝ)) * ∑ i, Tr i := by
    rw [C.sum_trace r]; ring
  rw [htail, hD, success]
  simp only [fun i => (C.success_term hη i).2]
  have hsum : ∑ i, ∑' x, qf (C.Λ i) (C.branch hη i x) ≤
      (1 + t) * ∑ i, Tr i + (1 + 1 / t) * ∑ i, W i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hi i
  have := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 1 / M by positivity)
  calc _ ≤ _ := this
    _ = _ := by ring

end UCode

/-- Optimizing Young's parameter. -/
lemma young_opt {S a w : ℝ} (ha : 0 < a) (hw : 0 ≤ w)
    (h : ∀ t : ℝ, 0 < t → S ≤ (1 + t) * a + (1 + 1 / t) * w) : S ≤ (√a + √w) ^ 2 := by
  have hsa := Real.sq_sqrt ha.le
  have hsw := Real.sq_sqrt hw
  have hsa0 : 0 < √a := Real.sqrt_pos.2 ha
  rcases hw.eq_or_lt with h0 | hw0
  · subst h0
    simp only [Real.sqrt_zero, add_zero, hsa]
    refine le_of_forall_pos_le_add fun e he => ?_
    have := h (e / a) (by positivity)
    have e2 : (1 + e / a) * a = a + e := by field_simp
    simp only [mul_zero, add_zero, e2] at this
    exact this
  · have hsw0 : 0 < √w := Real.sqrt_pos.2 hw0
    have := h (√w / √a) (by positivity)
    refine this.trans (le_of_eq ?_)
    have e1 : (1 + √w / √a) * (√a) ^ 2 = (√a) ^ 2 + √w * √a := by field_simp
    have e2 : (1 + 1 / (√w / √a)) * (√w) ^ 2 = (√w) ^ 2 + √a * √w := by field_simp
    rw [hsa] at e1
    rw [hsw] at e2
    rw [e1, e2, add_sq, hsa, hsw]
    ring

/-- **M2 (output-projector bound).** -/
theorem output_projector_bound {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hM : 1 ≤ M)
    (C : UCode n M) (r : ℕ) :
    C.success hη ≤ (√(((n + r).choose r : ℝ) / M) + √(C.tail η r)) ^ 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hch : (0 : ℝ) < ((n + r).choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left r n)
  exact young_opt (by positivity) (C.tail_nonneg hη r) fun t ht => C.success_le_young hη hM r ht

/-- **M2 consequence (quantile converse).** -/
theorem unbounded_quantile_conv {η ε γ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hM : 1 ≤ M)
    (C : UCode n M) (r : ℕ) (hs : 1 - ε ≤ C.success hη) (hγ : 0 < γ)
    (hw : C.tail η r ≤ 1 - ε - γ) :
    (M : ℝ) ≤ 4 / γ ^ 2 * ((n + r).choose r : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hch : (0 : ℝ) < ((n + r).choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left r n)
  have h1 := output_projector_bound hη hM C r
  have h2 := C.success_le_one hη hM
  have hw0 := C.tail_nonneg hη r
  set a : ℝ := ((n + r).choose r : ℝ) / M with ha
  have ha0 : 0 < a := by positivity
  set s := √a with hs'
  set z := √(C.tail η r) with hz
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha0.le
  have hz2 : z ^ 2 = C.tail η r := Real.sq_sqrt hw0
  have hkey : γ / 2 ≤ s := by
    by_contra hlt
    push Not at hlt
    have hz1 : z + γ / 2 ≤ 1 := by
      nlinarith [sq_nonneg (z + γ / 2 - 1), sq_nonneg (z + γ / 2)]
    nlinarith
  have hsq : γ ^ 2 / 4 ≤ a := by
    rw [← hs2]; nlinarith
  rw [ha, le_div_iff₀ hM0] at hsq
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

end

end Unbounded

end QIQCOP
