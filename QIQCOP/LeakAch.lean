import QIQCOP.MainGeneral
import QIQCOP.Counting

/-!
# Achievability with leakage above the photon cutoff

Codewords that are mixtures of condensates with two different photon numbers,

  `ρᵢ = (1 - δ) |uᵢ; L₀⟩⟨uᵢ; L₀| + δ |uᵢ; L'⟩⟨uᵢ; L'|`   in `Occ n L'`, `L₀ ≤ L'`,

model a leakage `δ` above the photon cutoff `L₀`. The decoder is that of `condensateCode`.

* `lossChannel_condensate_gen` : the loss identity for a condensate of any photon number `k ≤ L`.
* `leakCode`, `leakCode_success`, `leakCode_leak` : the two-level code, its success probability
  and its leakage.
* `exists_leakCode` : finite-block existence.
* `leak_achievability_of_threshold`, `leak_achievability` : asymptotic statements.
-/

open Finset Matrix
open scoped ComplexOrder

namespace QIQCOP

noncomputable section

variable {n L : ℕ}

/-! ### (a) The loss identity for a condensate of arbitrary photon number -/

/-- Loss acting on a `k`-photon condensate (`k ≤ L`):
`A_ℓ |u;k⟩ = √(Pr[K = k-|ℓ|]) ⟨ℓ|u;|ℓ|⟩ |u;k-|ℓ|⟩` if `|ℓ| ≤ k`, and `0` otherwise. -/
lemma lossKraus_mulVec_condensate_gen {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (u : Fin n → ℂ)
    {k : ℕ} (hk : k ≤ L) (ℓ : Occ n L) :
    lossKraus η ℓ *ᵥ condensate (L := L) u k =
      if photons (ℓ : Fin n → ℕ) ≤ k then
        ((((√(binomPMF k η (k - photons (ℓ : Fin n → ℕ)))) : ℝ) : ℂ) *
          condensate (L := L) u (photons (ℓ : Fin n → ℕ)) ℓ) •
          condensate (L := L) u (k - photons (ℓ : Fin n → ℕ))
      else 0 := by
  ext r
  by_cases ht : photons (r : Fin n → ℕ) + photons (ℓ : Fin n → ℕ) = k
  · have hs : photons (ℓ : Fin n → ℕ) ≤ k := by omega
    simp only [hs, ite_true]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    have hmem : (r : Fin n → ℕ) + ℓ ∈ occSet n L := by
      rw [mem_occSet, photons_add]; omega
    rw [Finset.sum_eq_single ⟨_, hmem⟩ (fun m _ hm => ?_) (by simp)]
    swap
    · rw [lossKraus, ite_eq_right, zero_mul]
      intro h; exact hm (Subtype.ext h)
    have hpr : photons (r : Fin n → ℕ) = k - photons (ℓ : Fin n → ℕ) := by omega
    have e1 : photons ((⟨_, hmem⟩ : Occ n L) : Fin n → ℕ) = k := by
      rw [Subtype.coe_mk, photons_add]; exact ht
    simp only [lossKraus, condensate, e1, hpr, ite_true]
    simp only [Pi.add_apply]
    have hreal := loss_coeff_identity hη0 hη1 (r : Fin n → ℕ) (ℓ : Fin n → ℕ)
    rw [ht] at hreal
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hreal
    simp only [Complex.ofReal_mul] at hc
    have hu : ∏ j, u j ^ ((r : Fin n → ℕ) j + (ℓ : Fin n → ℕ) j) =
        (∏ j, u j ^ (ℓ : Fin n → ℕ) j) * ∏ j, u j ^ (r : Fin n → ℕ) j := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => by rw [pow_add, mul_comm]
    rw [hu]
    linear_combination (∏ j, u j ^ (ℓ : Fin n → ℕ) j) * (∏ j, u j ^ (r : Fin n → ℕ) j) * hc
  · have hz : (lossKraus η ℓ *ᵥ condensate (L := L) u k) r = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro m _
      by_cases h : (m : Fin n → ℕ) = (r : Fin n → ℕ) + (ℓ : Fin n → ℕ)
      · rw [condensate_eq_zero (m := m) (by rw [h, photons_add]; exact ht), mul_zero]
      · simp [lossKraus, h]
    rw [hz]
    split_ifs with hs
    · rw [Pi.smul_apply, condensate_eq_zero (m := r) (by omega), smul_zero]
    · rfl

/-- **Loss identity for any input photon number** `k ≤ L`: for a unit vector `u`,
`𝒩_η^{⊗n}(|u;k⟩⟨u;k|) = ∑ⱼ C(k,j) ηʲ (1-η)^{k-j} |u;j⟩⟨u;j|`. -/
theorem lossChannel_condensate_gen {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (u : Fin n → ℂ)
    (hu : star u ⬝ᵥ u = 1) {k : ℕ} (hk : k ≤ L) :
    lossChannel η (ketbra (condensate (L := L) u k)) =
      ∑ j ∈ range (k + 1), (binomPMF k η j : ℂ) • ketbra (condensate (L := L) u j) := by
  have hB : ∀ j, 0 ≤ binomPMF k η j := fun j => binomPMF_nonneg hη0 hη1 j
  have hA : ∀ ℓ : Occ n L, lossKraus η ℓ * ketbra (condensate (L := L) u k) * (lossKraus η ℓ)ᴴ =
      ∑ j ∈ range (k + 1), ((binomPMF k η j : ℂ) *
        (star (condensate (L := L) u (k - j) ℓ) * condensate (L := L) u (k - j) ℓ)) •
          ketbra (condensate (L := L) u j) := by
    intro ℓ
    rw [ketbra, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec,
      lossKraus_mulVec_condensate_gen hη0 hη1 u hk]
    by_cases hs : photons (ℓ : Fin n → ℕ) ≤ k
    · simp only [hs, ite_true]
      rw [star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
      rw [Finset.sum_eq_single (k - photons (ℓ : Fin n → ℕ))]
      · rw [Nat.sub_sub_self hs, ketbra]
        congr 1
        have hsq : ((√(binomPMF k η (k - photons (ℓ : Fin n → ℕ))) : ℝ) : ℂ) *
            ((√(binomPMF k η (k - photons (ℓ : Fin n → ℕ))) : ℝ) : ℂ) =
            ((binomPMF k η (k - photons (ℓ : Fin n → ℕ)) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hB _)]
        have hst : star ((√(binomPMF k η (k - photons (ℓ : Fin n → ℕ))) : ℝ) : ℂ) =
            ((√(binomPMF k η (k - photons (ℓ : Fin n → ℕ))) : ℝ) : ℂ) := Complex.conj_ofReal _
        rw [star_mul', hst]
        linear_combination (star (condensate (L := L) u (photons (ℓ : Fin n → ℕ)) ℓ) *
          condensate (L := L) u (photons (ℓ : Fin n → ℕ)) ℓ) * hsq
      · intro j hj hne
        rw [condensate_eq_zero (m := ℓ) (k := k - j) (by rw [Finset.mem_range] at hj; omega)]
        simp
      · intro h; rw [Finset.mem_range] at h; omega
    · simp only [hs, ite_false]
      symm
      rw [Finset.sum_eq_zero]
      · ext a b; simp [vecMulVec_apply]
      · intro j _
        rw [condensate_eq_zero (m := ℓ) (k := k - j) (by omega)]
        simp
  rw [lossChannel, Finset.sum_congr rfl fun ℓ _ => hA ℓ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hnorm : ∑ ℓ : Occ n L,
      star (condensate (L := L) u (k - j) ℓ) * condensate (L := L) u (k - j) ℓ = 1 := by
    have h := condensate_inner (L := L) u u ((Nat.sub_le k j).trans hk)
    rw [hu, one_pow] at h
    simpa [dotProduct] using h
  rw [← Finset.sum_smul, ← Finset.mul_sum, hnorm, mul_one]

/-! ### Linearity of the channel -/

lemma lossChannel_add (η : ℝ) (ρ σ : Matrix (Occ n L) (Occ n L) ℂ) :
    lossChannel η (ρ + σ) = lossChannel η ρ + lossChannel η σ := by
  simp [lossChannel, mul_add, add_mul, Finset.sum_add_distrib]

lemma lossChannel_smul (η : ℝ) (c : ℂ) (ρ : Matrix (Occ n L) (Occ n L) ℂ) :
    lossChannel η (c • ρ) = c • lossChannel η ρ := by
  simp [lossChannel, Finset.smul_sum]

/-! ### (b) Per-sector analysis for input photon number `K ≤ L` -/

variable {M : ℕ}

/-- Per-message lower bound on the success probability, for an input condensate with `K ≤ L`
photons (generalizes `success_term_ge`, which is the case `K = L`). -/
lemma success_term_ge_gen {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (u : Fin M → Fin n → ℂ)
    (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) (t : ℕ) (i0 : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k))
    {K : ℕ} (hK : K ≤ L) (i : Fin M) :
    ∑ k ∈ Ico t (K + 1), binomPMF K η k * (srmDiag (L := L) u k i).re ^ 2 ≤
      ((povmMat (L := L) u t i0 i *
        lossChannel η (ketbra (condensate (L := L) (u i) K))).trace).re := by
  set Λ := povmMat (L := L) u t i0 i with hΛ
  have hΛpsd : Λ.PosSemidef := (Pmat_posSemidef u t i).add (povmMat_rest_posSemidef u t i0 i hc)
  set ψ : ℕ → Occ n L → ℂ := fun k => condensate (L := L) (u i) k with hψ
  rw [lossChannel_condensate_gen (L := L) hη0 hη1 (u i) (hu i) hK, Finset.mul_sum, trace_sum,
    Complex.re_sum]
  have hterm : ∀ k ∈ range (K + 1),
      ((Λ * ((binomPMF K η k : ℂ) • ketbra (ψ k))).trace).re =
        binomPMF K η k * (star (ψ k) ⬝ᵥ (Λ *ᵥ ψ k)).re := by
    intro k _
    rw [mul_smul_comm, trace_smul, trace_mul_ketbra, smul_eq_mul, Complex.re_ofReal_mul]
  rw [Finset.sum_congr rfl hterm]
  have hre : ∀ k, 0 ≤ (star (ψ k) ⬝ᵥ (Λ *ᵥ ψ k)).re := fun k =>
    (Complex.nonneg_iff.1 (hΛpsd.dotProduct_mulVec_nonneg (ψ k))).1
  have key : ∀ k ∈ Ico t (K + 1),
      (srmDiag (L := L) u k i).re ^ 2 ≤ (star (ψ k) ⬝ᵥ (Λ *ᵥ ψ k)).re := by
    intro k hk0
    have hk : k ∈ Ico t (L + 1) := by
      rw [mem_Ico] at hk0 ⊢; omega
    have hkL : k ≤ L := by have := (mem_Ico.1 hk).2; omega
    have hrest := (Complex.nonneg_iff.1
      ((povmMat_rest_posSemidef (L := L) u t i0 i hc).dotProduct_mulVec_nonneg (ψ k))).1
    rw [hΛ, povmMat, add_mulVec, dotProduct_add, Complex.add_re, Pmat, inner_sum_ketbra,
      Complex.ofReal_re]
    have hsingle : ‖star (meas (L := L) u k i) ⬝ᵥ ψ k‖ ^ 2 ≤
        ∑ k' ∈ Ico t (L + 1), ‖star (meas (L := L) u k' i) ⬝ᵥ ψ k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k' => ‖star (meas (L := L) u k' i) ⬝ᵥ ψ k‖ ^ 2)
        (fun _ _ => by positivity) hk
    have hz : star (meas (L := L) u k i) ⬝ᵥ ψ k = srmDiag (L := L) u k i := by
      rw [hψ, meas_condensate u hkL (hc k hk) i, srmDiag_eq u hkL]
    rw [hz] at hsingle
    have hre2 : (srmDiag (L := L) u k i).re ^ 2 ≤ ‖srmDiag (L := L) u k i‖ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
    linarith
  calc ∑ k ∈ Ico t (K + 1), binomPMF K η k * (srmDiag (L := L) u k i).re ^ 2
      ≤ ∑ k ∈ Ico t (K + 1), binomPMF K η k * (star (ψ k) ⬝ᵥ (Λ *ᵥ ψ k)).re :=
        Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_left (key k hk) (binomPMF_nonneg hη0 hη1 k)
    _ ≤ ∑ k ∈ range (K + 1), binomPMF K η k * (star (ψ k) ⬝ᵥ (Λ *ᵥ ψ k)).re := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk; simp only [mem_Ico] at hk; simp only [mem_range]; omega
        · intro k _ _; exact mul_nonneg (binomPMF_nonneg hη0 hη1 k) (hre k)

/-- The pairwise-overlap sum `∑_{i≠j} |⟨uᵢ|uⱼ⟩|^{2t}`. -/
def overlapSum (u : Fin M → Fin n → ℂ) (t : ℕ) : ℝ :=
  ∑ i, ∑ j ∈ univ.filter (· ≠ i), ‖star (u i) ⬝ᵥ u j‖ ^ (2 * t)

lemma overlapSum_nonneg (u : Fin M → Fin n → ℂ) (t : ℕ) : 0 ≤ overlapSum u t := by
  unfold overlapSum; positivity

/-- Gram-matrix bound in each sector `t ≤ k ≤ L`. -/
lemma srmDiag_sum_ge (u : Fin M → Fin n → ℂ) (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) {t k : ℕ}
    (htk : t ≤ k) (hkL : k ≤ L) :
    (M : ℝ) - overlapSum u t ≤ ∑ i, (srmDiag (L := L) u k i).re ^ 2 := by
  set Ψ := sectorMat (L := L) u k hkL
  have hdiag : ∀ i, (Ψᴴ * Ψ) i i = 1 := fun i => by rw [sectorMat_gram, hu, one_pow]
  have hb := srm_gram_bound (Ψᴴ * Ψ) (posSemidef_conjTranspose_mul_self Ψ) hdiag
  simp only [Fintype.card_fin] at hb
  have hsum : ∑ i, ∑ j, ‖(Ψᴴ * Ψ) i j‖ ^ 2 ≤ M + overlapSum u t := by
    rw [overlapSum, show (M : ℝ) = ∑ _i : Fin M, (1 : ℝ) by simp, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.add_sum_erase _ _ (mem_univ i), Finset.filter_ne']
    apply add_le_add
    · rw [hdiag]; simp
    · refine Finset.sum_le_sum fun j _ => ?_
      rw [sectorMat_gram, norm_pow, ← pow_mul]
      exact pow_le_pow_of_le_one (norm_nonneg _) (norm_inner_le_one _ _ (hu i) (hu j))
        (by omega)
  have hdiagEq : ∑ i, (srmDiag (L := L) u k i).re ^ 2 =
      ∑ i, (psdSqrt (posSemidef_conjTranspose_mul_self Ψ).isHermitian i i).re ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [srmDiag_eq u hkL]
  linarith

/-- Summed success bound for input condensates with `K` photons, `t ≤ K ≤ L`. -/
lemma sum_success_ge {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (u : Fin M → Fin n → ℂ)
    (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) {t : ℕ} (i0 : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k))
    {K : ℕ} (htK : t ≤ K) (hK : K ≤ L) :
    (M : ℝ) * (1 - binomLT K η t) - overlapSum u t ≤
      ∑ i, ((povmMat (L := L) u t i0 i *
        lossChannel η (ketbra (condensate (L := L) (u i) K))).trace).re := by
  set X := overlapSum u t with hXdef
  have hX0 : 0 ≤ X := overlapSum_nonneg u t
  have hS : ∑ k ∈ Ico t (K + 1), binomPMF K η k = 1 - binomLT K η t := by
    have := binomLT_add_tail K η (t := t) (by omega); linarith
  have hBLT : 0 ≤ binomLT K η t :=
    Finset.sum_nonneg fun k _ => binomPMF_nonneg hη0 hη1 k
  calc (M : ℝ) * (1 - binomLT K η t) - X
      ≤ ∑ k ∈ Ico t (K + 1), binomPMF K η k * ((M : ℝ) - X) := by
        rw [← Finset.sum_mul, hS]; nlinarith
    _ ≤ ∑ k ∈ Ico t (K + 1), binomPMF K η k * ∑ i, (srmDiag (L := L) u k i).re ^ 2 :=
        Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_left
            (srmDiag_sum_ge u hu (mem_Ico.1 hk).1 (by have := (mem_Ico.1 hk).2; omega))
            (binomPMF_nonneg hη0 hη1 k)
    _ = ∑ i, ∑ k ∈ Ico t (K + 1), binomPMF K η k * (srmDiag (L := L) u k i).re ^ 2 := by
        simp only [Finset.mul_sum]; exact Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun i _ => success_term_ge_gen hη0 hη1 u hu t i0 hc hK i

/-! ### The two-level code -/

lemma trace_ketbra_condensate (u : Fin n → ℂ) (hu : star u ⬝ᵥ u = 1) {k : ℕ} (hk : k ≤ L) :
    (ketbra (condensate (L := L) u k)).trace = 1 := by
  rw [ketbra, trace_vecMulVec, dotProduct_comm, condensate_inner (L := L) _ _ hk, hu, one_pow]

/-- **The two-level (leaky) condensate code**: codewords
`(1-δ) |uᵢ;L₀⟩⟨uᵢ;L₀| + δ |uᵢ;L⟩⟨uᵢ;L|` in the `≤ L`-photon space, with the decoder of
`condensateCode`. -/
def leakCode (u : Fin M → Fin n → ℂ) (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) (t : ℕ)
    (i0 : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k))
    (L₀ : ℕ) (hL₀ : L₀ ≤ L) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Code n L M where
  state i := ((1 - δ : ℝ) : ℂ) • ketbra (condensate (L := L) (u i) L₀) +
    ((δ : ℝ) : ℂ) • ketbra (condensate (L := L) (u i) L)
  state_psd i :=
    ((ketbra_posSemidef _).smul (Complex.zero_le_real.2 (sub_nonneg.2 hδ1))).add
      ((ketbra_posSemidef _).smul (Complex.zero_le_real.2 hδ0))
  state_trace i := by
    rw [trace_add, trace_smul, trace_smul, trace_ketbra_condensate _ (hu i) hL₀,
      trace_ketbra_condensate _ (hu i) le_rfl]
    simp
  povm := povmMat (L := L) u t i0
  povm_psd i := (Pmat_posSemidef u t i).add (povmMat_rest_posSemidef u t i0 i hc)
  povm_sum := by
    unfold povmMat
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [Qmat]

/-- **Finite-block success bound for the two-level code** (fixed codebook):
success `≥ 1 - [(1-δ) Pr{Bin(L₀,η) < t} + δ Pr{Bin(L,η) < t}] - (1/M) ∑_{i≠j} |⟨uᵢ|uⱼ⟩|^{2t}`. -/
theorem leakCode_success {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (u : Fin M → Fin n → ℂ)
    (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) {t : ℕ} (i0 : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k))
    {L₀ : ℕ} (ht : t ≤ L₀) (hL₀ : L₀ ≤ L) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    1 - ((1 - δ) * binomLT L₀ η t + δ * binomLT L η t) -
        (∑ i, ∑ j ∈ univ.filter (· ≠ i), ‖star (u i) ⬝ᵥ u j‖ ^ (2 * t)) / M ≤
      (leakCode (L := L) u hu t i0 hc L₀ hL₀ δ hδ0 hδ1).success η := by
  change 1 - ((1 - δ) * binomLT L₀ η t + δ * binomLT L η t) - overlapSum u t / M ≤ _
  set X := overlapSum u t with hXdef
  have hM : (0 : ℝ) < M := Nat.cast_pos.2 (Fin.pos i0)
  have h0 := sum_success_ge (L := L) hη0 hη1 u hu i0 hc ht hL₀
  have h1 := sum_success_ge (L := L) hη0 hη1 u hu i0 hc (ht.trans hL₀) le_rfl
  have hsplit : ∀ i, ((povmMat (L := L) u t i0 i * lossChannel η
      (((1 - δ : ℝ) : ℂ) • ketbra (condensate (L := L) (u i) L₀) +
        ((δ : ℝ) : ℂ) • ketbra (condensate (L := L) (u i) L))).trace).re =
      (1 - δ) * ((povmMat (L := L) u t i0 i *
        lossChannel η (ketbra (condensate (L := L) (u i) L₀))).trace).re +
      δ * ((povmMat (L := L) u t i0 i *
        lossChannel η (ketbra (condensate (L := L) (u i) L))).trace).re := by
    intro i
    rw [lossChannel_add, lossChannel_smul, lossChannel_smul, mul_add, mul_smul_comm,
      mul_smul_comm, trace_add, trace_smul, trace_smul, Complex.add_re, smul_eq_mul,
      smul_eq_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  dsimp only [Code.success, leakCode]
  rw [le_div_iff₀ hM, Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have e : (1 - ((1 - δ) * binomLT L₀ η t + δ * binomLT L η t) - X / M) * M =
      (1 - δ) * ((M : ℝ) * (1 - binomLT L₀ η t) - X) +
        δ * ((M : ℝ) * (1 - binomLT L η t) - X) := by
    field_simp; ring
  rw [e]
  exact add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.2 hδ1))
    (mul_le_mul_of_nonneg_left h1 hδ0)

/-! ### Leakage above the cutoff -/

/-- Average weight of the codewords above `L₀` photons:
`(1/M) ∑ᵢ Re Tr[(1 - Π_{≤L₀}) ρᵢ]`. -/
def leakAbove (C : Code n L M) (L₀ : ℕ) : ℝ :=
  (∑ i, (((1 - lowProj (n := n) (L := L) L₀) * C.state i).trace).re) / M

lemma high_ketbra_re (ψ : Occ n L → ℂ) (r : ℕ) :
    (((1 - lowProj (n := n) (L := L) r) * ketbra ψ).trace).re =
      ∑ m : Occ n L, if photons (m : Fin n → ℕ) ≤ r then 0 else ‖ψ m‖ ^ 2 := by
  rw [one_sub_lowProj, trace_diagonal_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs
  · simp
  · rw [one_mul, ketbra, vecMulVec_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma sum_norm_sq_condensate (u : Fin n → ℂ) (hu : star u ⬝ᵥ u = 1) {k : ℕ} (hk : k ≤ L) :
    ∑ m : Occ n L, ‖condensate (L := L) u k m‖ ^ 2 = 1 := by
  have h := condensate_inner (L := L) u u hk
  rw [hu, one_pow] at h
  have h2 : star (condensate (L := L) u k) ⬝ᵥ condensate (L := L) u k =
      ((∑ m : Occ n L, ‖condensate (L := L) u k m‖ ^ 2 : ℝ) : ℂ) := by
    unfold dotProduct
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.star_apply, Complex.star_def, RCLike.conj_mul]
    rfl
  exact_mod_cast h2.symm.trans h

/-- The two-level code has leakage at most `δ` above `L₀`. -/
theorem leakCode_leak (u : Fin M → Fin n → ℂ) (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) (t : ℕ)
    (i0 : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k))
    (L₀ : ℕ) (hL₀ : L₀ ≤ L) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    leakAbove (leakCode (L := L) u hu t i0 hc L₀ hL₀ δ hδ0 hδ1) L₀ ≤ δ := by
  have hM : (0 : ℝ) < M := Nat.cast_pos.2 (Fin.pos i0)
  have hterm : ∀ i, (((1 - lowProj (n := n) (L := L) L₀) *
      (((1 - δ : ℝ) : ℂ) • ketbra (condensate (L := L) (u i) L₀) +
        ((δ : ℝ) : ℂ) • ketbra (condensate (L := L) (u i) L))).trace).re ≤ δ := by
    intro i
    rw [mul_add, mul_smul_comm, mul_smul_comm, trace_add, trace_smul, trace_smul,
      Complex.add_re, smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
      high_ketbra_re, high_ketbra_re]
    have hz : (∑ m : Occ n L, if photons (m : Fin n → ℕ) ≤ L₀ then (0 : ℝ)
        else ‖condensate (L := L) (u i) L₀ m‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      split_ifs with h
      · rfl
      · rw [condensate_eq_zero (m := m) (by omega)]; simp
    have hle : (∑ m : Occ n L, if photons (m : Fin n → ℕ) ≤ L₀ then (0 : ℝ)
        else ‖condensate (L := L) (u i) L m‖ ^ 2) ≤ 1 := by
      rw [← sum_norm_sq_condensate (L := L) (u i) (hu i) le_rfl]
      refine Finset.sum_le_sum fun m _ => ?_
      split_ifs
      · positivity
      · exact le_rfl
    rw [hz, mul_zero, zero_add]
    exact mul_le_of_le_one_right hδ0 hle
  dsimp only [leakAbove, leakCode]
  rw [div_le_iff₀ hM]
  calc _ ≤ ∑ _i : Fin M, δ := Finset.sum_le_sum fun i _ => hterm i
    _ = δ * M := by simp [mul_comm]

/-! ### (c) Existence -/

/-- **Finite-block achievability with leakage.** If `t ≤ L₀ ≤ L`, `1 ≤ M ≤ C(n+t-1, t)` and
`(1-δ) Pr{Bin(L₀,η) < t} + δ Pr{Bin(L,η) < t} + (M-1)·e / C(n+t-1,t) ≤ ε`, there is a code in the
`≤ L`-photon space with success probability at least `1 - ε` and leakage at most `δ` above
`L₀` photons. -/
theorem exists_leakCode {η ε δ : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {t M L₀ : ℕ} (hn : 1 ≤ n)
    (ht : t ≤ L₀) (hL₀ : L₀ ≤ L) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : 1 ≤ M) (hMD : M ≤ (n + t - 1).choose t)
    (herr : (1 - δ) * binomLT L₀ η t + δ * binomLT L η t +
      ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ ε) :
    ∃ C : Code n L M, 1 - ε ≤ C.success η ∧ leakAbove C L₀ ≤ δ := by
  set R := t * (n + t) + 1 with hR
  set N := t + 1 with hN
  have hsec : (Pi.single (⟨0, hn⟩ : Fin n) R : Fin n → ℕ) ∈ sector n R := by
    rw [mem_sector, photons, Finset.sum_pi_single']; simp
  have : Nonempty (Ens n R N) := ⟨(⟨_, hsec⟩, fun _ => ⟨0, by omega⟩)⟩
  obtain ⟨c, hcb⟩ := exists_codebook (S := Ens n R N)
    (fun a b => ‖star (ensVec a) ⬝ᵥ ensVec b‖ ^ (2 * t)) (fun _ _ => by positivity) M
  have hmom := ensemble_moment (n := n) (t := t) (R := R) (N := N) hn (by omega) (by omega)
    (by omega)
  set u : Fin M → Fin n → ℂ := fun i => ensVec (c i) with hudef
  have hu : ∀ i, star (u i) ⬝ᵥ u i = 1 := fun i => ensVec_norm (by omega) _
  have hcard : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k) := by
    intro k hk
    rw [Fintype.card_fin, Fintype.card_coe, card_sector]
    exact hMD.trans (choose_mono hn (mem_Ico.1 hk).1)
  refine ⟨leakCode (L := L) u hu t ⟨0, hM⟩ hcard L₀ hL₀ δ hδ0 hδ1, ?_,
    leakCode_leak u hu t ⟨0, hM⟩ hcard L₀ hL₀ δ hδ0 hδ1⟩
  have hs := leakCode_success hη0 hη1 u hu ⟨0, hM⟩ hcard ht hL₀ hδ0 hδ1
  set X := ∑ i, ∑ j ∈ univ.filter (· ≠ i), ‖star (u i) ⬝ᵥ u j‖ ^ (2 * t)
  have hD : 0 < sectorDim n t := by
    unfold sectorDim; exact_mod_cast Nat.choose_pos (by omega)
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hS : (0 : ℝ) < (Fintype.card (Ens n R N) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hX : X ≤ (M : ℝ) * (M - 1) * Real.exp 1 / sectorDim n t := by
    calc X ≤ (M : ℝ) * (M - 1) *
          (∑ a : Ens n R N, ∑ b : Ens n R N, ‖star (ensVec a) ⬝ᵥ ensVec b‖ ^ (2 * t)) /
            (Fintype.card (Ens n R N) : ℝ) ^ 2 := hcb
      _ ≤ (M : ℝ) * (M - 1) * (Real.exp 1 / sectorDim n t *
            (Fintype.card (Ens n R N) : ℝ) ^ 2) / (Fintype.card (Ens n R N) : ℝ) ^ 2 := by
          gcongr
      _ = (M : ℝ) * (M - 1) * Real.exp 1 / sectorDim n t := by
          field_simp
  have hXM : X / M ≤ ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t := by
    rw [div_le_iff₀ (by linarith)]
    calc X ≤ (M : ℝ) * (M - 1) * Real.exp 1 / sectorDim n t := hX
      _ = ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t * M := by ring
  linarith

end

/-! ### (d) Asymptotics -/

open Real Filter Topology

lemma binomLT_mono_right {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (L : ℕ) {t t' : ℕ} (h : t ≤ t') :
    binomLT L η t ≤ binomLT L η t' := by
  unfold binomLT
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    fun k _ _ => binomPMF_nonneg hη0 hη1 k

/-- For `L' = c · L₀` with `c η ≥ 2` and `L₀ ≥ (2/γ) c η(1-η)`, Chebyshev gives
`Pr{Bin(L', η) < t} ≤ γ/2` for every `t ≤ L₀`. -/
lemma binomLT_far_le {η γ : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hγ0 : 0 < γ) {L₀ c t : ℕ}
    (hL₀ : 1 ≤ L₀) (hc : 2 ≤ η * c) (hbig : 2 / γ * (c * (η * (1 - η))) ≤ L₀) (ht : t ≤ L₀) :
    binomLT (c * L₀) η t ≤ γ / 2 := by
  set a := η * (1 - η) with ha
  have ha0 : 0 < a := mul_pos hη0 (by linarith)
  have hc0 : (0 : ℝ) < c := by
    by_contra h
    have : (c : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg c)
    rw [this] at hc; linarith
  have hc1 : 1 ≤ c := by exact_mod_cast hc0
  have hLr : (1 : ℝ) ≤ L₀ := by exact_mod_cast hL₀
  set s' := √(2 / γ) with hs'
  have hs'0 : 0 < s' := Real.sqrt_pos.2 (by positivity)
  have hs'2 : s' ^ 2 = 2 / γ := Real.sq_sqrt (by positivity)
  have hL1 : 1 ≤ c * L₀ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hcheb := binomLT_chebyshev (L := c * L₀) hη0 hη1 hs'0 hL1
  rw [hs'2, show (1 : ℝ) / (2 / γ) = γ / 2 by field_simp] at hcheb
  refine le_trans (binomLT_mono_right hη0.le hη1.le _ ?_) hcheb
  refine ht.trans ?_
  have hsq : s' * √(((c * L₀ : ℕ) : ℝ) * a) ≤ L₀ := by
    rw [hs', ← Real.sqrt_mul (by positivity)]
    calc √(2 / γ * (((c * L₀ : ℕ) : ℝ) * a)) ≤ √((L₀ : ℝ) * L₀) := by
          apply Real.sqrt_le_sqrt
          push_cast
          calc 2 / γ * ((c : ℝ) * L₀ * a) = (2 / γ * (c * a)) * L₀ := by ring
            _ ≤ (L₀ : ℝ) * L₀ := mul_le_mul_of_nonneg_right hbig (by positivity)
      _ = L₀ := Real.sqrt_mul_self (by positivity)
  have hy : (L₀ : ℝ) ≤ η * ((c * L₀ : ℕ) : ℝ) - s' * √(((c * L₀ : ℕ) : ℝ) * a) := by
    have : 2 * (L₀ : ℝ) ≤ η * ((c * L₀ : ℕ) : ℝ) := by
      push_cast
      calc 2 * (L₀ : ℝ) ≤ (η * c) * L₀ := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = η * (c * L₀) := by ring
    linarith
  exact_mod_cast hy.trans (Nat.le_ceil _)

set_option maxHeartbeats 2000000 in
/-- Second-order achievability with leakage, from a threshold bound (version with `γ ≤ 1`). -/
theorem leak_achievability_of_threshold_aux {η Ns ε γ s δ : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hNs : 0 < Ns) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hs0 : 0 ≤ s) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hth : ∀ᶠ n : ℕ in atTop, (1 - δ) * binomLT (cutoff Ns n) η
      ⌈η * (cutoff Ns n : ℝ) - s * √((cutoff Ns n : ℝ) * (η * (1 - η)))⌉₊ ≤ ε - γ) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, ∃ L' M : ℕ, 1 ≤ M ∧ cutoff Ns n ≤ L' ∧
      (∃ code : Code n L' M, 1 - ε ≤ code.success η ∧ leakAbove code (cutoff Ns n) ≤ δ) ∧
      n * g (η * Ns) - √(n : ℝ) * (s * √(Vocc η Ns)) - A * log n ≤ logb 2 M := by
  set x := η * Ns with hx
  set a := η * (1 - η) with ha
  have hx0 : 0 < x := mul_pos hη0 hNs
  have ha0 : 0 < a := mul_pos hη0 (by linarith)
  have hgp := gp_pos hx0
  set R := s * √(Ns * a) + s * √a + η + 1 with hR
  obtain ⟨B, hB0, hB⟩ := stirlingExpansion hx0 R
  set c0 := s * √a * gp x with hc0
  set c1 := logb 2 (γ / (4 * Real.exp 1)) with hc1
  -- the multiplier c for the high photon number L' = c L
  set c : ℕ := ⌈2 / η⌉₊ with hcdef
  have hcη : 2 ≤ η * c := by
    have h : 2 / η ≤ c := Nat.le_ceil _
    rw [div_le_iff₀ hη0] at h; linarith
  set N₀ : ℕ := ⌈2 / γ * (c * a) / Ns⌉₊ with hN₀
  refine ⟨B + |c0| + |c1| + 1, ?_⟩
  filter_upwards [hB, hth, eventually_ge_atTop 3, eventually_ge_atTop N₀] with n hSt hPt0 hn3 hnN
  rw [← hx] at hSt
  -- basic facts about n
  have hn : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hsn : 1 ≤ √(n : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hlog : 1 ≤ log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  -- the cutoff L
  set L := cutoff Ns n with hLdef
  set Lr : ℝ := (L : ℝ) with hLr
  have hL1 : (n : ℝ) * Ns ≤ Lr := Nat.le_ceil _
  have hL2 : Lr < n * Ns + 1 := Nat.ceil_lt_add_one (by positivity)
  have hLpos : 1 ≤ L := by
    have : (0 : ℝ) < Lr := lt_of_lt_of_le (by positivity) hL1
    exact_mod_cast (show (0 : ℝ) < L from this)
  have hbig : 2 / γ * (c * a) ≤ Lr := by
    have h1 : 2 / γ * (c * a) / Ns ≤ (N₀ : ℝ) := Nat.le_ceil _
    have h2 : (N₀ : ℝ) ≤ n := by exact_mod_cast hnN
    have h3 : 2 / γ * (c * a) / Ns ≤ n := h1.trans h2
    rw [div_le_iff₀ hNs] at h3
    linarith
  -- the threshold
  set y := η * Lr - s * √(Lr * a) with hy
  set t := ⌈y⌉₊ with ht
  have hPt : (1 - δ) * binomLT L η t ≤ ε - γ := hPt0
  have htL : t ≤ L := by
    rw [ht, Nat.ceil_le]
    have : 0 ≤ s * √(Lr * a) := mul_nonneg hs0 (Real.sqrt_nonneg _)
    have : η * Lr ≤ Lr := by nlinarith
    linarith
  have hfar : binomLT (c * L) η t ≤ γ / 2 :=
    binomLT_far_le hη0 hη1 hγ0 hLpos hcη hbig htL
  have hfar0 : 0 ≤ binomLT (c * L) η t :=
    Finset.sum_nonneg fun k _ => binomPMF_nonneg hη0.le hη1.le k
  have hLL' : L ≤ c * L := by
    have : 1 ≤ c := by
      have : (0 : ℝ) < c := by
        by_contra h
        have h0 : (c : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg c)
        rw [h0] at hcη; linarith
      exact_mod_cast this
    exact Nat.le_mul_of_pos_left L this
  have hty : y ≤ t := Nat.le_ceil y
  have htup : (t : ℝ) < η * Lr + 1 := by
    have hyle : y ≤ η * Lr := by
      have : 0 ≤ s * √(Lr * a) := mul_nonneg hs0 (Real.sqrt_nonneg _)
      linarith
    have h1 : t ≤ ⌈η * Lr⌉₊ := Nat.ceil_mono hyle
    have h2 : (⌈η * Lr⌉₊ : ℝ) < η * Lr + 1 := Nat.ceil_lt_add_one (by positivity)
    have h3 : (t : ℝ) ≤ ⌈η * Lr⌉₊ := by exact_mod_cast h1
    linarith
  -- √(L a) ≤ √n √(N_S a) + √a
  have hsqn : √((n : ℝ) * Ns * a) = √(n : ℝ) * √(Ns * a) := by
    rw [mul_assoc]; exact Real.sqrt_mul hn0 _
  have hsqL : √(Lr * a) ≤ √(n : ℝ) * √(Ns * a) + √a := by
    rw [← hsqn]
    calc √(Lr * a) ≤ √(n * Ns * a + a) := Real.sqrt_le_sqrt (by nlinarith)
      _ ≤ _ := sqrt_add_le _ _ (by positivity) ha0.le
  have hsNa : 0 ≤ √(Ns * a) := Real.sqrt_nonneg _
  have hsa : 0 ≤ √a := Real.sqrt_nonneg _
  -- bounds on t - n x
  have htlow : -(s * (√(n : ℝ) * √(Ns * a))) - s * √a ≤ (t : ℝ) - n * x := by
    have e1 : s * √(Lr * a) ≤ s * (√(n : ℝ) * √(Ns * a)) + s * √a := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left hsqL hs0
    have e2 : η * (n * Ns) ≤ η * Lr := mul_le_mul_of_nonneg_left hL1 hη0.le
    have e3 : (n : ℝ) * x = η * (n * Ns) := by rw [hx]; ring
    linarith
  have hthigh : (t : ℝ) - n * x ≤ η + 1 := by
    have e2 : η * Lr ≤ η * (n * Ns + 1) := mul_le_mul_of_nonneg_left hL2.le hη0.le
    have e3 : (n : ℝ) * x = η * (n * Ns) := by rw [hx]; ring
    linarith
  have hwin : |(t : ℝ) - n * x| ≤ R * √(n : ℝ) := by
    rw [abs_le]
    have e : R * √(n : ℝ) = s * (√(n : ℝ) * √(Ns * a)) + (s * √a + η + 1) * √(n : ℝ) := by
      rw [hR]; ring
    have hk0 : 0 ≤ s * √a + η + 1 := by
      have := mul_nonneg hs0 hsa; linarith
    have k1 : s * √a + η + 1 ≤ (s * √a + η + 1) * √(n : ℝ) := le_mul_of_one_le_right hk0 hsn
    have k2 : 0 ≤ s * (√(n : ℝ) * √(Ns * a)) :=
      mul_nonneg hs0 (mul_nonneg (Real.sqrt_nonneg _) hsNa)
    have k3 : 0 ≤ s * √a := mul_nonneg hs0 hsa
    constructor <;> linarith
  have hSt' := hSt t hwin
  have hVocc : √(n : ℝ) * (s * √(Vocc η Ns)) = s * (√(n : ℝ) * √(Ns * a)) * gp x := by
    have : √(Vocc η Ns) = √(Ns * a) * gp x := by
      rw [show Vocc η Ns = (Ns * a) * gp x ^ 2 by simp only [Vocc, ha, hx]; ring]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hgp.le]
    rw [this]; ring
  have hcoef : -(√(n : ℝ) * (s * √(Vocc η Ns))) - c0 ≤ ((t : ℝ) - n * x) * gp x := by
    have := mul_le_mul_of_nonneg_right htlow hgp.le
    rw [hVocc, hc0]; linarith
  -- the code size M = max 1 ⌊(γ/2) D / e⌋
  have hn1 : 1 ≤ n := by omega
  have hD1 : (1 : ℝ) ≤ sectorDim n t := by
    unfold sectorDim; exact_mod_cast Nat.choose_pos (by omega)
  have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set z := γ / 2 * sectorDim n t / Real.exp 1 with hz
  have hz0 : 0 < z := by positivity
  have hzD : z ≤ sectorDim n t := by
    rw [hz, div_le_iff₀ he0]; nlinarith
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
  have herr : (1 - δ) * binomLT L η t + δ * binomLT (c * L) η t +
      ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ ε := by
    have h1 : ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ γ / 2 := by
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_right hMz he0.le
      rw [hz] at this; field_simp at this; linarith
    have h2 : δ * binomLT (c * L) η t ≤ γ / 2 := by nlinarith
    linarith
  refine ⟨c * L, M, hM1, hLL',
    exists_leakCode (L := c * L) hη0.le hη1.le hn1 htL hLL' hδ0 hδ1 hM1 hMD herr, ?_⟩
  -- log₂ M ≥ log₂ (z/2) = log₂ D + log₂ (γ/(4e))
  have hlogM : logb 2 (z / 2) ≤ logb 2 M :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hMz2
  have hsplit : logb 2 (z / 2) = logb 2 (sectorDim n t) + c1 := by
    rw [hc1, ← Real.logb_mul (by positivity) (by positivity)]
    congr 1; rw [hz]; field_simp; ring
  have habs0 : c0 ≤ |c0| := le_abs_self c0
  have habs1 : -|c1| ≤ c1 := neg_abs_le c1
  have hc : |c0| + |c1| + 1 ≤ (|c0| + |c1| + 1) * log n :=
    le_mul_of_one_le_right (by positivity) hlog
  rw [hsplit] at hlogM
  have hexp : (B + |c0| + |c1| + 1) * log n = B * log n + (|c0| + |c1| + 1) * log n := by ring
  have h1 : (n : ℝ) * g x - √(n : ℝ) * (s * √(Vocc η Ns)) - c0 - B * log n ≤
      logb 2 (sectorDim n t) := by linarith
  have h2 : (n : ℝ) * g x - √(n : ℝ) * (s * √(Vocc η Ns)) - c0 - B * log n + c1 ≤
      logb 2 M := by linarith
  rw [hexp]
  linarith

/-- **Second-order achievability with leakage, from a threshold bound.** Let `γ > 0`, `s ≥ 0`,
`0 ≤ δ ≤ 1`, and suppose that for large `n`,
`(1-δ) Pr{K < η L - s √(L η(1-η))} ≤ ε - γ` with `K ~ Bin(L, η)`, `L = ⌈n N_S⌉`.
Then for all large `n` there is a code (in some `≤ L'`-photon space, `L' ≥ L`) with success
`≥ 1 - ε`, leakage `≤ δ` above `L` photons, and
`log₂ M ≥ n g(η N_S) - √n · s √V_occ - O(log n)`. -/
theorem leak_achievability_of_threshold {η Ns ε γ s δ : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hNs : 0 < Ns) (hγ0 : 0 < γ) (hs0 : 0 ≤ s) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hth : ∀ᶠ n : ℕ in atTop, (1 - δ) * binomLT (cutoff Ns n) η
      ⌈η * (cutoff Ns n : ℝ) - s * √((cutoff Ns n : ℝ) * (η * (1 - η)))⌉₊ ≤ ε - γ) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, ∃ L' M : ℕ, 1 ≤ M ∧ cutoff Ns n ≤ L' ∧
      (∃ code : Code n L' M, 1 - ε ≤ code.success η ∧ leakAbove code (cutoff Ns n) ≤ δ) ∧
      n * g (η * Ns) - √(n : ℝ) * (s * √(Vocc η Ns)) - A * log n ≤ logb 2 M := by
  refine leak_achievability_of_threshold_aux (γ := min γ 1) hη0 hη1 hNs (lt_min hγ0 one_pos)
    (min_le_right _ _) hs0 hδ0 hδ1 ?_
  filter_upwards [hth] with n hn
  have := min_le_left γ 1
  linarith

/-- `K log n ≤ c √n` for large `n`, for any `c > 0`. -/
lemma eventually_log_le_sqrt (K : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, K * log n ≤ c * √(n : ℝ) := by
  have ho := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hc' : 0 < c / (|K| + 1) := by positivity
  filter_upwards [ho.def hc', eventually_ge_atTop 1] with n h2 h3
  simp only [Function.comp_apply] at h2
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h3
  have hs : √(n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hlog : 0 ≤ log (n : ℝ) := Real.log_nonneg hn
  have hspos : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (by positivity), ← hs] at h2
  have hK : K * log n ≤ |K| * log n := mul_le_mul_of_nonneg_right (le_abs_self K) hlog
  have hK' : |K| * log n ≤ |K| * (c / (|K| + 1) * √(n : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
  have key : |K| * (c / (|K| + 1)) ≤ c := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg K]
  have : |K| * (c / (|K| + 1) * √(n : ℝ)) ≤ c * √(n : ℝ) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right key hspos.le
  linarith

/-- **Second-order achievability with leakage `δ` above the cutoff.** For `0 < η < 1`,
`N_S > 0`, `0 ≤ δ ≤ 1`, every `q ≤ 0` with `(1-δ) Φ(q) < ε` and every `τ > 0`: for all large
`n` there are `L' ≥ ⌈n N_S⌉`, `M ≥ 1` and a code with `M` messages in the `≤ L'`-photon space
with success `≥ 1 - ε`, leakage at most `δ` above `⌈n N_S⌉` photons, and
`log₂ M ≥ n g(η N_S) + (q √V_occ - τ) √n`. -/
theorem leak_achievability {η Ns ε δ q τ : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hq : q ≤ 0) (hΦ : (1 - δ) * Φ q < ε) (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop, ∃ L' M : ℕ, 1 ≤ M ∧ cutoff Ns n ≤ L' ∧
      (∃ code : Code n L' M, 1 - ε ≤ code.success η ∧ leakAbove code (cutoff Ns n) ≤ δ) ∧
      n * g (η * Ns) + (q * √(Vocc η Ns) - τ) * √(n : ℝ) ≤ logb 2 M := by
  have hV := Vocc_pos hη0 hη1 hNs
  have hsV : 0 < √(Vocc η Ns) := Real.sqrt_pos.2 hV
  set s := -q + τ / (2 * √(Vocc η Ns)) with hs
  have hpos : 0 < τ / (2 * √(Vocc η Ns)) := by positivity
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsq : -s < q := by rw [hs]; linarith
  have hΦs : Φ (-s) < Φ q := Φ_strictMono hsq
  have hlt0 : (1 - δ) * Φ (-s) < ε :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hΦs.le (sub_nonneg.2 hδ1)) hΦ
  set γ := (ε - (1 - δ) * Φ (-s)) / 2 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hlt : (1 - δ) * Φ (-s) < ε - γ := by rw [hγ]; linarith
  have hth : ∀ᶠ n : ℕ in atTop, (1 - δ) * binomLT (cutoff Ns n) η
      ⌈η * (cutoff Ns n : ℝ) - s * √((cutoff Ns n : ℝ) * (η * (1 - η)))⌉₊ ≤ ε - γ := by
    have h := ((((binomLT_tendsto hη0 hη1 (-s)).comp (tendsto_cutoff hNs)).const_mul
      (1 - δ)).eventually (gt_mem_nhds hlt))
    filter_upwards [h] with n hn
    simp only [Function.comp_apply, neg_mul, ← sub_eq_add_neg] at hn
    exact hn.le
  obtain ⟨A, hA⟩ := leak_achievability_of_threshold hη0 hη1 hNs hγ0 hs0 hδ0 hδ1 hth
  filter_upwards [hA, eventually_log_le_sqrt A (half_pos hτ)] with n hAn hlog
  obtain ⟨L', M, hM1, hLL', hcode, hlow⟩ := hAn
  refine ⟨L', M, hM1, hLL', hcode, le_trans ?_ hlow⟩
  have e : s * √(Vocc η Ns) = -q * √(Vocc η Ns) + τ / 2 := by
    rw [hs]; field_simp
  rw [e]
  nlinarith

end QIQCOP
