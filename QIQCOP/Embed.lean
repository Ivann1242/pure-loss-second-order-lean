import QIQCOP.UnboundedCode
import QIQCOP.ConverseMain
import QIQCOP.LawCode

/-!
# Embedding finite-support codes into Fock-space codes

* `Unbounded.embJ`: the coordinate isometry `ℂ^{Occ n L} → Fock n`.
* `Code.toUCode`: inputs are the spectral ensembles of the density matrices, padded by zero
  vectors; the POVM is `Λ̃ᵢ = J Λᵢ J† + (1/M)(1 - J J†)`.
* `Code.toUCode_success`, `Code.toUCode_law`, `Code.toUCode_law_of_gt`, `Code.toUCode_leak`,
  `Code.toUCode_summable_mean`, `Code.toUCode_mean`: every operational quantity is preserved.

A `Code n L 0` cannot exist since its POVM would sum to `0 ≠ 1`, so `toUCode` needs no hypothesis
on `M`.
-/

open Finset Matrix WithLp
open scoped ComplexOrder InnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace QIQCOP

namespace Unbounded

variable {n L M : ℕ}

noncomputable section

/-! ### The coordinate embedding -/

/-- Extension by zero of a function on `Occ n L`. -/
def embFun (v : Occ n L → ℂ) (m : Idx n) : ℂ :=
  if h : photons m ≤ L then v ⟨m, mem_occSet.2 h⟩ else 0

lemma embFun_occ (v : Occ n L → ℂ) (a : Occ n L) : embFun v a.1 = v a := by
  have h := mem_occSet.1 a.2
  simp [embFun, h]

lemma embFun_of_gt (v : Occ n L → ℂ) {m : Idx n} (h : L < photons m) : embFun v m = 0 := by
  simp [embFun, not_le.2 h]

lemma embFun_summable (v : Occ n L → ℂ) : Summable fun m => ‖embFun v m‖ ^ 2 :=
  summable_of_ne_finset_zero (s := occSet n L) fun m hm => by
    have : L < photons m := not_le.1 fun h => hm (mem_occSet.2 h)
    simp [embFun_of_gt v this]

/-- The coordinate isometry `J : ℂ^{Occ n L} → Fock n`. -/
def embJ : EuclideanSpace ℂ (Occ n L) →L[ℂ] Fock n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => mkF (embFun (ofLp v)) (embFun_summable _)
      map_add' := fun x y => by
        ext m
        by_cases h : photons m ≤ L <;> simp [embFun, h]
      map_smul' := fun c x => by
        ext m
        by_cases h : photons m ≤ L <;> simp [embFun, h] }

lemma embJ_apply (v : EuclideanSpace ℂ (Occ n L)) (m : Idx n) :
    embJ v m = embFun (ofLp v) m := rfl

lemma embJ_occ (v : EuclideanSpace ℂ (Occ n L)) (a : Occ n L) : embJ v a.1 = ofLp v a :=
  embFun_occ _ a

lemma embJ_of_gt (v : EuclideanSpace ℂ (Occ n L)) {m : Idx n} (h : L < photons m) :
    embJ v m = 0 := embFun_of_gt _ h

lemma embJ_single (a : Occ n L) :
    embJ (EuclideanSpace.single a (1 : ℂ)) = lp.single 2 a.1 (1 : ℂ) := by
  classical
  ext m
  rw [embJ_apply, lp.single_apply]
  by_cases h : photons m ≤ L
  · by_cases e : m = a.1
    · subst e
      have := embFun_occ (L := L) (ofLp (EuclideanSpace.single a (1 : ℂ))) a
      simpa using this
    · have hne : (⟨m, mem_occSet.2 h⟩ : Occ n L) ≠ a := fun e' => e (congrArg Subtype.val e')
      simp [embFun, h, e, hne]
  · have hne : m ≠ a.1 := fun e => h (e ▸ mem_occSet.1 a.2)
    simp [embFun, h, hne]

/-- The adjoint `J†` reads off the coordinates in `Occ n L`. -/
lemma embJ_adjoint_apply (ψ : Fock n) (a : Occ n L) :
    ofLp ((embJ (L := L)).adjoint ψ) a = ψ a.1 := by
  classical
  have h := ContinuousLinearMap.adjoint_inner_right (embJ (L := L))
    (EuclideanSpace.single a (1 : ℂ)) ψ
  rw [EuclideanSpace.inner_single_left, embJ_single, lp.inner_single_left] at h
  simpa using h

lemma embJ_adjoint_comp (v : EuclideanSpace ℂ (Occ n L)) :
    (embJ (L := L)).adjoint (embJ v) = v := by
  ext a
  rw [embJ_adjoint_apply, embJ_occ]

lemma inner_embJ (x y : EuclideanSpace ℂ (Occ n L)) : ⟪embJ x, embJ y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, embJ_adjoint_comp]

lemma norm_embJ_sq (v : EuclideanSpace ℂ (Occ n L)) :
    ‖embJ v‖ ^ 2 = ∑ a, ‖ofLp v a‖ ^ 2 := by
  have h : ‖embJ v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h1 := inner_embJ v v
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    exact_mod_cast h1
  rw [h, EuclideanSpace.norm_sq_eq]

/-! ### The lifted POVM -/

/-- `J A J† + c (1 - J J†)`. -/
def liftOp (A : Matrix (Occ n L) (Occ n L) ℂ) (c : ℝ) : Fock n →L[ℂ] Fock n :=
  embJ ∘L (toEuclideanCLM (n := Occ n L) (𝕜 := ℂ) A) ∘L (embJ (L := L)).adjoint +
    (c : ℂ) • (1 - embJ ∘L (embJ (L := L)).adjoint)

lemma liftOp_embJ (A : Matrix (Occ n L) (Occ n L) ℂ) (c : ℝ)
    (w : EuclideanSpace ℂ (Occ n L)) :
    liftOp A c (embJ w) = embJ (toEuclideanCLM (n := Occ n L) (𝕜 := ℂ) A w) := by
  have h : (1 - embJ ∘L (embJ (L := L)).adjoint : Fock n →L[ℂ] Fock n) (embJ w) = 0 := by
    simp [embJ_adjoint_comp]
  simp only [liftOp, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, h, embJ_adjoint_comp, smul_zero, add_zero]

lemma isPositive_one_sub :
    (1 - embJ ∘L (embJ (L := L)).adjoint : Fock n →L[ℂ] Fock n).IsPositive := by
  set J := embJ (n := n) (L := L)
  set Q : Fock n →L[ℂ] Fock n := 1 - J ∘L J.adjoint with hQ
  have hadj : Q.adjoint = Q := by
    have h1 : ContinuousLinearMap.adjoint (1 : Fock n →L[ℂ] Fock n) = 1 := star_one _
    simp [hQ, map_sub, ContinuousLinearMap.adjoint_comp, h1]
  have hidem : Q ∘L Q = Q := by
    ext1 x
    have : J.adjoint (J (J.adjoint x)) = J.adjoint x := embJ_adjoint_comp _
    simp [hQ, this]
  have := Q.isPositive_adjoint_comp_self
  rwa [hadj, hidem] at this

lemma isPositive_liftOp {A : Matrix (Occ n L) (Occ n L) ℂ} (hA : A.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) : (liftOp (n := n) A c).IsPositive := by
  have hT : (toEuclideanCLM (n := Occ n L) (𝕜 := ℂ) A).IsPositive := by
    rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isPositive_toEuclideanLin_iff.2 hA
  have h1 := hT.conj_adjoint (embJ (L := L) (n := n))
  have h2 : ((c : ℂ) • (1 - embJ ∘L (embJ (L := L)).adjoint :
      Fock n →L[ℂ] Fock n)).IsPositive :=
    (isPositive_one_sub (n := n) (L := L)).smul_of_nonneg (by exact_mod_cast hc)
  exact h1.add h2

/-! ### Loss on embedded vectors -/

lemma lossOp_embJ {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (ℓ : Occ n L)
    (v : EuclideanSpace ℂ (Occ n L)) :
    lossOp hη ℓ.1 (embJ v) = embJ (toLp 2 (lossKraus η ℓ *ᵥ ofLp v)) := by
  ext m
  by_cases h : photons m ≤ L
  · have := lossOp_eq_lossKraus hη ℓ (embJ v) (fun m hm => embJ_of_gt v hm)
      ⟨m, mem_occSet.2 h⟩
    simp only [embJ_occ] at this
    rw [this]
    exact (embJ_occ (toLp 2 (lossKraus η ℓ *ᵥ ofLp v)) ⟨m, mem_occSet.2 h⟩).symm
  · have hgt : L < photons m := not_le.1 h
    have hgt' : L < photons (m + ℓ.1) := by
      rw [photons_add]; omega
    rw [lossOp_apply, embJ_of_gt v hgt', embJ_of_gt _ hgt, mul_zero]

lemma lossOp_embJ_of_gt {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) {ℓ : Idx n} (hℓ : L < photons ℓ)
    (v : EuclideanSpace ℂ (Occ n L)) : lossOp hη ℓ (embJ v) = 0 := by
  ext m
  have hgt' : L < photons (m + ℓ) := by
    rw [photons_add]; omega
  rw [lossOp_apply, embJ_of_gt v hgt', mul_zero]
  rfl

/-- A branch term of the lifted code, in matrix form. -/
lemma branch_term {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (A : Matrix (Occ n L) (Occ n L) ℂ)
    (c : ℝ) (ℓ : Occ n L) (v : Occ n L → ℂ) :
    (⟪lossOp hη ℓ.1 (embJ (toLp 2 v)), liftOp A c (lossOp hη ℓ.1 (embJ (toLp 2 v)))⟫_ℂ).re =
      (star (lossKraus η ℓ *ᵥ v) ⬝ᵥ (A *ᵥ (lossKraus η ℓ *ᵥ v))).re := by
  rw [lossOp_embJ, liftOp_embJ, inner_embJ, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [ofLp_toLp, toEuclideanCLM_toLp]
  rw [dotProduct_comm]

/-- The sum over all Fock loss patterns reduces to the patterns in `Occ n L`. -/
lemma tsum_branch {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (A : Matrix (Occ n L) (Occ n L) ℂ)
    (c : ℝ) (v : Occ n L → ℂ) :
    ∑' ℓ : Idx n, (⟪lossOp hη ℓ (embJ (toLp 2 v)),
        liftOp A c (lossOp hη ℓ (embJ (toLp 2 v)))⟫_ℂ).re =
      ∑ ℓ : Occ n L, (star (lossKraus η ℓ *ᵥ v) ⬝ᵥ (A *ᵥ (lossKraus η ℓ *ᵥ v))).re := by
  rw [tsum_eq_sum (s := occSet n L), ← Finset.sum_coe_sort (occSet n L)]
  · exact Finset.sum_congr rfl fun ℓ _ => branch_term hη A c ℓ v
  · intro ℓ hℓ
    have : L < photons ℓ := not_le.1 fun h => hℓ (mem_occSet.2 h)
    rw [lossOp_embJ_of_gt hη this]
    simp

/-- Trace against a Kraus-conjugated rank-one operator. -/
lemma trace_kraus_ketbra (A K : Matrix (Occ n L) (Occ n L) ℂ) (v : Occ n L → ℂ) :
    (A * (K * vecMulVec v (star v) * Kᴴ)).trace = star (K *ᵥ v) ⬝ᵥ (A *ᵥ (K *ᵥ v)) := by
  have h : K * vecMulVec v (star v) * Kᴴ = vecMulVec (K *ᵥ v) (star (K *ᵥ v)) := by
    rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]
  rw [h, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

/-! ### Spectral ensembles -/

/-- The vectors `√λ_d e_d` of the spectral decomposition. -/
def specVec {A : Matrix (Occ n L) (Occ n L) ℂ} (hA : A.PosSemidef) (d : Occ n L) :
    Occ n L → ℂ :=
  fun a => ((√(hA.isHermitian.eigenvalues d) : ℝ) : ℂ) *
    ofLp (hA.isHermitian.eigenvectorBasis d) a

/-- Spectral decomposition `A = ∑_d |√λ_d e_d⟩⟨√λ_d e_d|`. -/
lemma specVec_sum {A : Matrix (Occ n L) (Occ n L) ℂ} (hA : A.PosSemidef) :
    A = ∑ d, vecMulVec (specVec hA d) (star (specVec hA d)) := by
  classical
  have hs := hA.isHermitian.spectral_theorem
  ext a b
  have h := congrFun (congrFun hs a) b
  rw [h]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.sum_apply, vecMulVec_apply, Pi.star_apply, specVec]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hl := hA.eigenvalues_nonneg d
  have hsq : ((√(hA.isHermitian.eigenvalues d) : ℝ) : ℂ) *
      ((√(hA.isHermitian.eigenvalues d) : ℝ) : ℂ) =
      ((hA.isHermitian.eigenvalues d : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl]
  simp only [Function.comp_apply, Matrix.star_apply, star_mul', Complex.star_def,
    Complex.conj_ofReal, RCLike.ofReal_eq_complex_ofReal,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  linear_combination (-(ofLp (hA.isHermitian.eigenvectorBasis d) a) *
    (starRingEnd ℂ) (ofLp (hA.isHermitian.eigenvectorBasis d) b)) * hsq

lemma diag_re_eq {A : Matrix (Occ n L) (Occ n L) ℂ} (hA : A.PosSemidef) (a : Occ n L) :
    (A a a).re = ∑ d, ‖specVec hA d a‖ ^ 2 := by
  conv_lhs => rw [specVec_sum hA]
  simp only [Matrix.sum_apply, vecMulVec_apply, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact Complex.ofReal_re _

/-- An injection of the (finite) index type into `ℕ`. -/
def occEnum (n L : ℕ) (d : Occ n L) : ℕ := (Fintype.equivFin (Occ n L) d : ℕ)

lemma occEnum_injective : Function.Injective (occEnum n L) := fun a b h =>
  (Fintype.equivFin (Occ n L)).injective (Fin.ext h)

/-- The spectral ensemble, padded with zero vectors and included into Fock space. -/
def specEns {A : Matrix (Occ n L) (Occ n L) ℂ} (hA : A.PosSemidef) : ℕ → Fock n :=
  Function.extend (occEnum n L) (fun d => embJ (toLp 2 (specVec hA d))) 0

lemma specEns_enum {A : Matrix (Occ n L) (Occ n L) ℂ} (hA : A.PosSemidef) (d : Occ n L) :
    specEns (n := n) hA (occEnum n L d) = embJ (toLp 2 (specVec hA d)) :=
  occEnum_injective.extend_apply _ _ d

lemma hasSum_specEns {A : Matrix (Occ n L) (Occ n L) ℂ} (hA : A.PosSemidef) (G : Fock n → ℝ)
    (hG : G 0 = 0) :
    HasSum (fun k => G (specEns (n := n) hA k)) (∑ d, G (embJ (toLp 2 (specVec hA d)))) := by
  refine (Function.Injective.hasSum_iff (occEnum_injective (n := n) (L := L)) fun k hk => ?_).1 ?_
  · have hne : ¬ ∃ d, occEnum n L d = k := fun ⟨d, hd⟩ => hk ⟨d, hd⟩
    change G (Function.extend (occEnum n L) _ 0 k) = 0
    rw [Function.extend_apply' _ _ _ hne]
    exact hG
  · have := hasSum_fintype fun d : Occ n L => G (embJ (toLp 2 (specVec hA d)))
    refine this.congr_fun fun d => ?_
    simp [specEns_enum]

lemma hasSum_specEns_norm {A : Matrix (Occ n L) (Occ n L) ℂ} (hA : A.PosSemidef)
    (ht : A.trace = 1) : HasSum (fun k => ‖specEns (n := n) hA k‖ ^ 2) 1 := by
  have h := hasSum_specEns (n := n) hA (fun ψ => ‖ψ‖ ^ 2) (by simp)
  have e : ∑ d, ‖embJ (n := n) (toLp 2 (specVec hA d))‖ ^ 2 = 1 := by
    simp only [norm_embJ_sq]
    rw [Finset.sum_comm]
    simp only [← diag_re_eq hA]
    exact sum_diag_re_eq_one ht
  rwa [e] at h

end

end Unbounded

noncomputable section

open Unbounded

variable {n L M : ℕ}

/-- A code has at least one message: its POVM sums to the identity on a nonzero space. -/
lemma Code.one_le_M (C : Code n L M) : 1 ≤ M := by
  by_contra h
  obtain rfl : M = 0 := by omega
  have h0 := C.povm_sum
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at h0
  let a : Occ n L := ⟨0, mem_occSet.2 (by simp [photons])⟩
  have := congrFun (congrFun h0 a) a
  simp at this

/-- The Fock-space code of a finite-support code. -/
def Code.toUCode (C : Code n L M) : UCode n M where
  ψ i := specEns (C.state_psd i)
  hψ i := hasSum_specEns_norm (C.state_psd i) (C.state_trace i)
  Λ i := liftOp (C.povm i) (1 / (M : ℝ))
  pos i := isPositive_liftOp (C.povm_psd i) (by positivity)
  povm := by
    have hM : (M : ℂ) ≠ 0 := by
      have := C.one_le_M
      exact_mod_cast (by omega : M ≠ 0)
    have hsumT : ∑ i, toEuclideanCLM (n := Occ n L) (𝕜 := ℂ) (C.povm i) = 1 := by
      rw [← map_sum, C.povm_sum, map_one]
    ext1 x
    simp only [liftOp, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h1 : ∑ i, embJ (toEuclideanCLM (n := Occ n L) (𝕜 := ℂ) (C.povm i)
        ((embJ (L := L)).adjoint x)) = embJ ((embJ (L := L)).adjoint x) := by
      rw [← map_sum, ← ContinuousLinearMap.sum_apply, hsumT]
      rfl
    rw [h1, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have h2 : (M : ℂ) * ((1 / (M : ℝ) : ℝ) : ℂ) = 1 := by
      push_cast; field_simp
    rw [h2, one_smul]
    simp

theorem Code.toUCode_lawI_eq (C : Code n L M) (i : Fin M) (t : ℕ) :
    C.toUCode.lawI i t =
      ∑ m : Occ n L, if photons (m : Fin n → ℕ) = t then (C.state i m m).re else 0 := by
  have hsec : ∀ v : Occ n L → ℂ, ‖secP t (embJ (n := n) (toLp 2 v))‖ ^ 2 =
      ∑ m : Occ n L, if photons (m : Fin n → ℕ) = t then ‖v m‖ ^ 2 else 0 := by
    intro v
    have e : secP t (embJ (n := n) (toLp 2 v)) =
        embJ (toLp 2 fun m : Occ n L => if photons (m : Fin n → ℕ) = t then v m else 0) := by
      ext m
      simp only [secP, cut_apply, embJ_apply, embFun]
      by_cases h : photons m ≤ L <;> by_cases h' : photons m = t <;> simp [h, h']
    rw [e, norm_embJ_sq]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h : photons (m : Fin n → ℕ) = t <;> simp [h]
  have h := hasSum_specEns (n := n) (C.state_psd i) (fun ψ => ‖secP t ψ‖ ^ 2) (by
    have : secP t (0 : Fock n) = 0 := by ext m; simp [secP]
    simp [this])
  change ∑' k, ‖secP t (specEns (C.state_psd i) k)‖ ^ 2 = _
  rw [h.tsum_eq]
  simp only [hsec]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : photons (m : Fin n → ℕ) = t
  · simp only [hm, if_true]
    exact (diag_re_eq (C.state_psd i) m).symm
  · simp [hm]

/-- The photon law is preserved, at every `t`. -/
theorem Code.toUCode_law_eq (C : Code n L M) (t : ℕ) : C.toUCode.law t = C.law t := by
  simp only [UCode.law, Code.law, Code.toUCode_lawI_eq]
  ring

/-- The photon law is preserved for `t ≤ L`. -/
theorem Code.toUCode_law (C : Code n L M) {t : ℕ} (_ht : t ≤ L) :
    C.toUCode.law t = C.law t := C.toUCode_law_eq t

/-- The law vanishes above `L`. -/
theorem Code.toUCode_law_of_gt (C : Code n L M) {t : ℕ} (ht : L < t) : C.toUCode.law t = 0 := by
  rw [C.toUCode_law_eq, Code.law]
  refine div_eq_zero_iff.2 (Or.inl (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun m _ => ?_))
  have := mem_occSet.1 m.2
  rw [if_neg (by omega)]

/-- Success probability is preserved. -/
theorem Code.toUCode_success (C : Code n L M) {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) :
    C.toUCode.success hη = C.success η := by
  have hterm : ∀ i : Fin M, ∑' k, ∑' ℓ : Idx n,
      (⟪lossOp hη ℓ (C.toUCode.ψ i k), C.toUCode.Λ i (lossOp hη ℓ (C.toUCode.ψ i k))⟫_ℂ).re =
      ((C.povm i * lossChannel η (C.state i)).trace).re := by
    intro i
    have h := hasSum_specEns (n := n) (C.state_psd i)
      (fun ψ => ∑' ℓ : Idx n, (⟪lossOp hη ℓ ψ, liftOp (C.povm i) (1 / (M : ℝ))
        (lossOp hη ℓ ψ)⟫_ℂ).re) (by simp)
    change ∑' k, ∑' ℓ : Idx n, (⟪lossOp hη ℓ (specEns (C.state_psd i) k),
      liftOp (C.povm i) (1 / (M : ℝ)) (lossOp hη ℓ (specEns (C.state_psd i) k))⟫_ℂ).re = _
    rw [h.tsum_eq]
    simp only [tsum_branch]
    conv_rhs => rw [lossChannel]
    conv_rhs => rw [specVec_sum (C.state_psd i)]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum,
      trace_kraus_ketbra]
    exact Finset.sum_comm
  rw [UCode.success, Code.success, Finset.sum_congr rfl fun i _ => hterm i]
  ring

/-- Leakage is preserved. -/
theorem Code.toUCode_leak (C : Code n L M) (L₀ : ℕ) : C.toUCode.leak L₀ = C.leak L₀ := by
  have h1 : C.toUCode.leak L₀ = ∑ t ∈ range (L + 1), C.law t * (if L₀ < t then 1 else 0) := by
    rw [UCode.leak, tsum_eq_sum (s := range (L + 1))]
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [C.toUCode_law_eq]
      split_ifs <;> simp
    · intro t ht
      have : L < t := by simpa using ht
      simp [C.toUCode_law_of_gt this]
  rw [h1, C.sum_law_mul, Code.leak]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_sub_lowProj, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Matrix.diag_apply, Matrix.diagonal_mul]
  by_cases h : L₀ < photons (m : Fin n → ℕ)
  · simp [h, not_le.2 h]
  · simp [h, not_lt.1 h]

/-- The mean series has finite support, hence is summable. -/
theorem Code.toUCode_summable_mean (C : Code n L M) :
    Summable (fun t : ℕ => (t : ℝ) * C.toUCode.law t) :=
  summable_of_ne_finset_zero (s := range (L + 1)) fun t ht => by
    have : L < t := by simpa using ht
    simp [C.toUCode_law_of_gt this]

/-- The mean photon number is preserved. -/
theorem Code.toUCode_mean (C : Code n L M) : C.toUCode.mean = C.meanPhotons := by
  rw [UCode.mean, tsum_eq_sum (s := range (L + 1)), C.meanPhotons_eq]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [C.toUCode_law_eq, mul_comm]
  · intro t ht
    have : L < t := by simpa using ht
    simp [C.toUCode_law_of_gt this]

end

end QIQCOP
