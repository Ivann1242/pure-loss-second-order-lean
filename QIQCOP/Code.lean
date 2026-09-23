import QIQCOP.Fock
import QIQCOP.Polar
import QIQCOP.Ensemble
import QIQCOP.Binomial

/-!
# Codes for the pure-loss channel and the fixed-photon condensate code (proof.md §1)

A `Code n L M` sends one of `M` messages through `n` uses of the pure-loss channel,
with input density matrices supported on the `≤ L`-photon space. With `L = ⌈n N_S⌉` every such
code satisfies the problem's occupation constraint Eq. (2) with `δ_n = 0`, so it is admissible.

`exists_code` is the finite-block achievability bound Eq. (5): threshold photon counting plus a
square-root measurement in each photon sector, with codewords `|uᵢ;L⟩` drawn from the finite
ensemble of `QIQCOP.Ensemble`.
-/

open Finset Matrix
open scoped ComplexOrder

namespace QIQCOP

/-- A code with `M` messages for `n` channel uses, inputs in the `≤ L`-photon space. -/
structure Code (n L M : ℕ) where
  /-- input density matrices -/
  state : Fin M → Matrix (Occ n L) (Occ n L) ℂ
  state_psd : ∀ i, (state i).PosSemidef
  state_trace : ∀ i, (state i).trace = 1
  /-- decoding POVM on the output space -/
  povm : Fin M → Matrix (Occ n L) (Occ n L) ℂ
  povm_psd : ∀ i, (povm i).PosSemidef
  povm_sum : ∑ i, povm i = 1

noncomputable section

/-- Average success probability `(1/M) ∑ᵢ Tr[Λᵢ 𝒩_η^{⊗n}(ρᵢ)]`. -/
def Code.success {n L M : ℕ} (C : Code n L M) (η : ℝ) : ℝ :=
  (∑ i, ((C.povm i * lossChannel η (C.state i)).trace).re) / M

variable {n L : ℕ}

/-! ### Embedding a photon sector into the `≤ L` space -/

/-- Inclusion of the `k`-photon sector basis into the `≤ L` basis. -/
def secIncl {k : ℕ} (hk : k ≤ L) (m : ↥(sector n k)) : Occ n L :=
  ⟨m.1, mem_occSet.2 (by rw [mem_sector.1 m.2]; exact hk)⟩

lemma secIncl_injective {k : ℕ} (hk : k ≤ L) : Function.Injective (secIncl (n := n) hk) := by
  intro a b h
  exact Subtype.ext (congrArg Subtype.val h :)

/-- Extension by zero of a sector vector. -/
def secExt (k : ℕ) (v : ↥(sector n k) → ℂ) : Occ n L → ℂ := fun x =>
  if h : photons (x : Fin n → ℕ) = k then v ⟨x.1, mem_sector.2 h⟩ else 0

lemma secExt_incl {k : ℕ} (hk : k ≤ L) (v : ↥(sector n k) → ℂ) (m : ↥(sector n k)) :
    secExt (L := L) k v (secIncl hk m) = v m := by
  have h : photons ((secIncl hk m : Occ n L) : Fin n → ℕ) = k := mem_sector.1 m.2
  simp only [secExt, h]
  rfl

lemma secExt_eq_zero {k : ℕ} (v : ↥(sector n k) → ℂ) {x : Occ n L}
    (h : photons (x : Fin n → ℕ) ≠ k) : secExt k v x = 0 := by
  simp [secExt, h]

/-- A sum over the `≤ L` basis of a function supported on the `k`-sector is a sum over the
sector. -/
lemma sum_occ_eq_sum_sector {k : ℕ} (hk : k ≤ L) (F : Occ n L → ℂ)
    (hF : ∀ x : Occ n L, photons (x : Fin n → ℕ) ≠ k → F x = 0) :
    ∑ x, F x = ∑ m : ↥(sector n k), F (secIncl hk m) := by
  refine (Fintype.sum_of_injective (secIncl hk) (secIncl_injective hk) _ F ?_ ?_).symm
  · intro x hx
    apply hF
    intro hxk
    exact hx ⟨⟨x.1, mem_sector.2 hxk⟩, rfl⟩
  · intro m; rfl

lemma inner_secExt {k : ℕ} (hk : k ≤ L) (v w : ↥(sector n k) → ℂ) :
    star (secExt (L := L) k v) ⬝ᵥ secExt k w = star v ⬝ᵥ w := by
  unfold dotProduct
  rw [sum_occ_eq_sum_sector hk]
  · simp only [Pi.star_apply, secExt_incl]
  · intro x hx; simp [secExt_eq_zero _ hx]

lemma inner_secExt_ne {k k' : ℕ} (hkk : k ≠ k') (v : ↥(sector n k) → ℂ)
    (w : ↥(sector n k') → ℂ) : star (secExt (L := L) k v) ⬝ᵥ secExt k' w = 0 := by
  unfold dotProduct
  apply Finset.sum_eq_zero
  intro x _
  by_cases h : photons (x : Fin n → ℕ) = k
  · have h' : photons (x : Fin n → ℕ) ≠ k' := h ▸ hkk
    simp [secExt_eq_zero w h']
  · simp [secExt_eq_zero v h]

lemma inner_secExt_condensate {k : ℕ} (hk : k ≤ L) (v : ↥(sector n k) → ℂ) (u : Fin n → ℂ) :
    star (secExt (L := L) k v) ⬝ᵥ condensate u k =
      star v ⬝ᵥ fun m => condensate (L := L) u k (secIncl hk m) := by
  unfold dotProduct
  rw [sum_occ_eq_sum_sector hk]
  · simp only [Pi.star_apply, secExt_incl]
  · intro x hx; simp [secExt_eq_zero _ hx]

lemma inner_secExt_condensate_ne {k k' : ℕ} (hkk : k ≠ k') (v : ↥(sector n k) → ℂ)
    (u : Fin n → ℂ) : star (secExt (L := L) k v) ⬝ᵥ condensate u k' = 0 := by
  unfold dotProduct
  apply Finset.sum_eq_zero
  intro x _
  by_cases h : photons (x : Fin n → ℕ) = k
  · have h' : photons (x : Fin n → ℕ) ≠ k' := h ▸ hkk
    simp [condensate_eq_zero h']
  · simp [secExt_eq_zero v h]

/-! ### Small linear-algebra facts -/

lemma ketbra_posSemidef {D : Type*} [Fintype D] (ψ : D → ℂ) : (ketbra ψ).PosSemidef :=
  posSemidef_vecMulVec_self_star ψ

lemma ketbra_mulVec {D : Type*} [Fintype D] (φ ψ : D → ℂ) :
    ketbra φ *ᵥ ψ = (star φ ⬝ᵥ ψ) • φ := by
  ext a
  simp [ketbra, mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]

lemma ketbra_mul_ketbra {D : Type*} [Fintype D] (φ ψ : D → ℂ) :
    ketbra φ * ketbra ψ = (star φ ⬝ᵥ ψ) • vecMulVec φ (star ψ) := by
  rw [ketbra, ketbra, vecMulVec_mul_vecMulVec]
  ext a b
  simp [vecMulVec_apply, mul_left_comm]

lemma trace_mul_ketbra {D : Type*} [Fintype D] (A : Matrix D D ℂ) (ψ : D → ℂ) :
    (A * ketbra ψ).trace = star ψ ⬝ᵥ (A *ᵥ ψ) := by
  rw [ketbra, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

lemma inner_ketbra_self {D : Type*} [Fintype D] (φ ψ : D → ℂ) :
    star ψ ⬝ᵥ (ketbra φ *ᵥ ψ) = ((‖star φ ⬝ᵥ ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [ketbra_mulVec, dotProduct_smul, smul_eq_mul]
  have : star ψ ⬝ᵥ φ = star (star φ ⬝ᵥ ψ) := by
    simp [dotProduct, star_sum, mul_comm]
  rw [this, Complex.star_def, RCLike.mul_conj]
  push_cast; rfl

/-- Cauchy–Schwarz for unit vectors. -/
lemma norm_inner_le_one {m : ℕ} (u v : Fin m → ℂ) (hu : star u ⬝ᵥ u = 1)
    (hv : star v ⬝ᵥ v = 1) : ‖star u ⬝ᵥ v‖ ≤ 1 := by
  have key : ∀ w : Fin m → ℂ, star w ⬝ᵥ w = ((∑ j, ‖w j‖ ^ 2 : ℝ) : ℂ) := by
    intro w
    unfold dotProduct
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.star_apply, Complex.star_def, RCLike.conj_mul]
    rfl
  have hu' : ∑ j, ‖u j‖ ^ 2 = 1 := by exact_mod_cast (key u).symm.trans hu
  have hv' : ∑ j, ‖v j‖ ^ 2 = 1 := by exact_mod_cast (key v).symm.trans hv
  calc ‖star u ⬝ᵥ v‖ ≤ ∑ j, ‖u j‖ * ‖v j‖ := by
        unfold dotProduct
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ √(∑ j, ‖u j‖ ^ 2) * √(∑ j, ‖v j‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = 1 := by rw [hu', hv', Real.sqrt_one, one_mul]

lemma choose_mono {n t k : ℕ} (hn : 1 ≤ n) (htk : t ≤ k) :
    (n + t - 1).choose t ≤ (n + k - 1).choose k := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have e1 : n' + 1 + t - 1 = n' + t := by omega
  have e2 : n' + 1 + k - 1 = n' + k := by omega
  rw [e1, e2, ← Nat.choose_symm_add, ← Nat.choose_symm_add]
  exact Nat.choose_le_choose n' (by omega)


/-! ### Square-root measurement in each photon sector -/

variable {M : ℕ}

/-- Columns: the `k`-photon condensates `|uᵢ;k⟩` in sector coordinates. -/
def sectorMat (u : Fin M → Fin n → ℂ) (k : ℕ) (hk : k ≤ L) : Matrix ↥(sector n k) (Fin M) ℂ :=
  fun m i => condensate (L := L) (u i) k (secIncl hk m)

lemma sectorMat_gram (u : Fin M → Fin n → ℂ) {k : ℕ} (hk : k ≤ L) (i j : Fin M) :
    ((sectorMat (L := L) u k hk)ᴴ * sectorMat u k hk) i j = (star (u i) ⬝ᵥ u j) ^ k := by
  rw [mul_apply, ← condensate_inner (L := L) (u i) (u j) hk]
  unfold dotProduct
  rw [sum_occ_eq_sum_sector hk]
  · simp [sectorMat, conjTranspose_apply]
  · intro x hx; simp [condensate_eq_zero hx]

/-- The square-root-measurement isometry of sector `k` (junk outside the valid range). -/
def srmMat (u : Fin M → Fin n → ℂ) (k : ℕ) : Matrix ↥(sector n k) (Fin M) ℂ :=
  if h : k ≤ L ∧ Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k) then
    Classical.choose (exists_isometry_polar (sectorMat (L := L) u k h.1) h.2)
  else 0

lemma srmMat_spec (u : Fin M → Fin n → ℂ) {k : ℕ} (hk : k ≤ L)
    (hc : Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k)) :
    (srmMat (L := L) u k)ᴴ * srmMat (L := L) u k = 1 ∧
      (srmMat (L := L) u k)ᴴ * sectorMat u k hk =
        psdSqrt (isHermitian_conjTranspose_mul_self (sectorMat (L := L) u k hk)) := by
  unfold srmMat
  split_ifs with h
  · exact Classical.choose_spec (exists_isometry_polar (sectorMat (L := L) u k hk) hc)
  · exact absurd ⟨hk, hc⟩ h

/-- Measurement vector for message `i` in sector `k`, as a vector of the `≤ L` space. -/
def meas (u : Fin M → Fin n → ℂ) (k : ℕ) (i : Fin M) : Occ n L → ℂ :=
  secExt k fun m => srmMat (L := L) u k m i

lemma meas_inner (u : Fin M → Fin n → ℂ) {k : ℕ} (hk : k ≤ L)
    (hc : Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k)) (i j : Fin M) :
    star (meas (L := L) u k i) ⬝ᵥ meas u k j = if i = j then 1 else 0 := by
  rw [meas, meas, inner_secExt hk, ← Matrix.one_apply, ← (srmMat_spec u hk hc).1, mul_apply]
  simp [dotProduct, conjTranspose_apply]

lemma meas_inner_ne (u : Fin M → Fin n → ℂ) {k k' : ℕ} (h : k ≠ k') (i j : Fin M) :
    star (meas (L := L) u k i) ⬝ᵥ meas u k' j = 0 :=
  inner_secExt_ne h _ _

lemma meas_condensate (u : Fin M → Fin n → ℂ) {k : ℕ} (hk : k ≤ L)
    (hc : Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k)) (i : Fin M) :
    star (meas (L := L) u k i) ⬝ᵥ condensate (u i) k =
      psdSqrt (isHermitian_conjTranspose_mul_self (sectorMat (L := L) u k hk)) i i := by
  rw [meas, inner_secExt_condensate hk, ← (srmMat_spec u hk hc).2, mul_apply]
  simp [dotProduct, conjTranspose_apply, sectorMat]

lemma meas_condensate_ne (u : Fin M → Fin n → ℂ) {k k' : ℕ} (h : k ≠ k') (i : Fin M)
    (v : Fin n → ℂ) : star (meas (L := L) u k i) ⬝ᵥ condensate v k' = 0 :=
  inner_secExt_condensate_ne h _ _

/-! ### The decoding POVM -/

/-- `Pᵢ = ∑_{t ≤ k ≤ L} |φᵢₖ⟩⟨φᵢₖ|`. -/
def Pmat (u : Fin M → Fin n → ℂ) (t : ℕ) (i : Fin M) : Matrix (Occ n L) (Occ n L) ℂ :=
  ∑ k ∈ Ico t (L + 1), ketbra (meas (L := L) u k i)

/-- `Q = ∑ᵢ Pᵢ`, a projection when the `φᵢₖ` are orthonormal. -/
def Qmat (u : Fin M → Fin n → ℂ) (t : ℕ) : Matrix (Occ n L) (Occ n L) ℂ :=
  ∑ i, Pmat (L := L) u t i

lemma Pmat_posSemidef (u : Fin M → Fin n → ℂ) (t : ℕ) (i : Fin M) :
    (Pmat (L := L) u t i).PosSemidef :=
  posSemidef_sum _ fun _ _ => ketbra_posSemidef _

lemma Qmat_isHermitian (u : Fin M → Fin n → ℂ) (t : ℕ) : (Qmat (L := L) u t).IsHermitian :=
  (posSemidef_sum _ fun i _ => Pmat_posSemidef (L := L) u t i).isHermitian

lemma Qmat_idem (u : Fin M → Fin n → ℂ) (t : ℕ)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k)) :
    Qmat (L := L) u t * Qmat (L := L) u t = Qmat (L := L) u t := by
  set S := (univ : Finset (Fin M)) ×ˢ Ico t (L + 1)
  have hQ : Qmat (L := L) u t = ∑ p ∈ S, ketbra (meas (L := L) u p.2 p.1) := by
    rw [Qmat, Finset.sum_product]; rfl
  have hinner : ∀ p ∈ S, ∀ p' ∈ S,
      star (meas (L := L) u p.2 p.1) ⬝ᵥ meas u p'.2 p'.1 = if p = p' then 1 else 0 := by
    intro p hp p' hp'
    have hk : p.2 ≤ L := by have := (mem_product.1 hp).2; simp at this; omega
    by_cases hkk : p.2 = p'.2
    · rw [← hkk, meas_inner u hk (hc _ (mem_product.1 hp).2)]
      by_cases hij : p.1 = p'.1
      · simp [hij, Prod.ext_iff, hkk]
      · simp [hij, Prod.ext_iff]
    · rw [meas_inner_ne u hkk]
      simp [Prod.ext_iff, hkk]
  rw [hQ, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_congr rfl fun p' hp' => by
    rw [ketbra_mul_ketbra, hinner p hp p' hp']]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, hp, ite_true]
  rfl

lemma one_sub_Qmat_posSemidef (u : Fin M → Fin n → ℂ) (t : ℕ)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k)) :
    (1 - Qmat (L := L) u t).PosSemidef := by
  have hH : (1 - Qmat (L := L) u t)ᴴ = 1 - Qmat (L := L) u t := by
    rw [conjTranspose_sub, conjTranspose_one, (Qmat_isHermitian u t).eq]
  have : 1 - Qmat (L := L) u t = (1 - Qmat (L := L) u t)ᴴ * (1 - Qmat (L := L) u t) := by
    rw [hH, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, Qmat_idem u t hc]
    abel
  rw [this]
  exact posSemidef_conjTranspose_mul_self _


/-- The decoding POVM: `Λᵢ = Pᵢ`, plus the leftover `1 - Q` assigned to message `i₀`. -/
def povmMat (u : Fin M → Fin n → ℂ) (t : ℕ) (i0 i : Fin M) : Matrix (Occ n L) (Occ n L) ℂ :=
  Pmat (L := L) u t i + if i = i0 then 1 - Qmat (L := L) u t else 0

lemma povmMat_rest_posSemidef (u : Fin M → Fin n → ℂ) (t : ℕ) (i0 i : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k)) :
    (if i = i0 then 1 - Qmat (L := L) u t else 0).PosSemidef := by
  split_ifs
  · exact one_sub_Qmat_posSemidef u t hc
  · exact PosSemidef.zero

/-- **The fixed-photon condensate code** (proof.md §1): codewords `|uᵢ;L⟩`, decoder = photon
counting followed by the square-root measurement in each sector `k ≥ t`. -/
def condensateCode (u : Fin M → Fin n → ℂ) (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) (t : ℕ)
    (i0 : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k)) :
    Code n L M where
  state i := ketbra (condensate (L := L) (u i) L)
  state_psd i := ketbra_posSemidef _
  state_trace i := by
    rw [ketbra, trace_vecMulVec, dotProduct_comm, condensate_inner (L := L) _ _ le_rfl, hu,
      one_pow]
  povm := povmMat (L := L) u t i0
  povm_psd i := (Pmat_posSemidef u t i).add (povmMat_rest_posSemidef u t i0 i hc)
  povm_sum := by
    unfold povmMat
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [Qmat]

lemma inner_sum_ketbra {D ι : Type*} [Fintype D] (K : Finset ι) (φ : ι → D → ℂ) (ψ : D → ℂ) :
    star ψ ⬝ᵥ ((∑ k ∈ K, ketbra (φ k)) *ᵥ ψ) = ((∑ k ∈ K, ‖star (φ k) ⬝ᵥ ψ‖ ^ 2 : ℝ) : ℂ) := by
  classical
  induction K using Finset.induction_on with
  | empty => simp
  | insert a K ha ih =>
    rw [Finset.sum_insert ha, add_mulVec, dotProduct_add, ih, inner_ketbra_self,
      Finset.sum_insert ha]
    push_cast; ring

/-- Diagonal entries `(√G_k)ᵢᵢ` of the sector Gram square root (junk for `k > L`). -/
def srmDiag (u : Fin M → Fin n → ℂ) (k : ℕ) (i : Fin M) : ℂ :=
  if hk : k ≤ L then psdSqrt (isHermitian_conjTranspose_mul_self (sectorMat (L := L) u k hk)) i i
  else 0

lemma srmDiag_eq (u : Fin M → Fin n → ℂ) {k : ℕ} (hk : k ≤ L) (i : Fin M) :
    srmDiag (L := L) u k i =
      psdSqrt (isHermitian_conjTranspose_mul_self (sectorMat (L := L) u k hk)) i i := by
  simp [srmDiag, hk]

/-- Per-message lower bound on the success probability. -/
lemma success_term_ge {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (u : Fin M → Fin n → ℂ)
    (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) (t : ℕ) (i0 : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k)) (i : Fin M) :
    ∑ k ∈ Ico t (L + 1), binomPMF L η k * (srmDiag (L := L) u k i).re ^ 2 ≤
      ((povmMat (L := L) u t i0 i *
        lossChannel η (ketbra (condensate (L := L) (u i) L))).trace).re := by
  set Λ := povmMat (L := L) u t i0 i with hΛ
  have hΛpsd : Λ.PosSemidef := (Pmat_posSemidef u t i).add (povmMat_rest_posSemidef u t i0 i hc)
  set ψ : ℕ → Occ n L → ℂ := fun k => condensate (L := L) (u i) k with hψ
  rw [lossChannel_condensate (L := L) hη0 hη1 (u i) (hu i), Finset.mul_sum, trace_sum,
    Complex.re_sum]
  have hterm : ∀ k ∈ range (L + 1),
      ((Λ * ((binomPMF L η k : ℂ) • ketbra (ψ k))).trace).re =
        binomPMF L η k * (star (ψ k) ⬝ᵥ (Λ *ᵥ ψ k)).re := by
    intro k _
    rw [mul_smul_comm, trace_smul, trace_mul_ketbra, smul_eq_mul, Complex.re_ofReal_mul]
  rw [Finset.sum_congr rfl hterm]
  have hre : ∀ k, 0 ≤ (star (ψ k) ⬝ᵥ (Λ *ᵥ ψ k)).re := fun k =>
    (Complex.nonneg_iff.1 (hΛpsd.dotProduct_mulVec_nonneg (ψ k))).1
  have key : ∀ k ∈ Ico t (L + 1),
      (srmDiag (L := L) u k i).re ^ 2 ≤ (star (ψ k) ⬝ᵥ (Λ *ᵥ ψ k)).re := by
    intro k hk
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
  calc ∑ k ∈ Ico t (L + 1), binomPMF L η k * (srmDiag (L := L) u k i).re ^ 2
      ≤ ∑ k ∈ Ico t (L + 1), binomPMF L η k * (star (ψ k) ⬝ᵥ (Λ *ᵥ ψ k)).re :=
        Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_left (key k hk) (binomPMF_nonneg hη0 hη1 k)
    _ ≤ ∑ k ∈ range (L + 1), binomPMF L η k * (star (ψ k) ⬝ᵥ (Λ *ᵥ ψ k)).re := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk; simp only [mem_Ico] at hk; simp only [mem_range]; omega
        · intro k _ _; exact mul_nonneg (binomPMF_nonneg hη0 hη1 k) (hre k)

/-- **Finite-block achievability for the condensate code** (proof.md Eq. (5), for a fixed
codebook): success `≥ 1 - Pr{K < t} - (1/M) ∑_{i≠j} |⟨uᵢ|uⱼ⟩|^{2t}`. -/
theorem condensateCode_success {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (u : Fin M → Fin n → ℂ)
    (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) {t : ℕ} (ht : t ≤ L) (i0 : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k)) :
    1 - binomLT L η t -
        (∑ i, ∑ j ∈ univ.filter (· ≠ i), ‖star (u i) ⬝ᵥ u j‖ ^ (2 * t)) / M ≤
      (condensateCode (L := L) u hu t i0 hc).success η := by
  set X := ∑ i, ∑ j ∈ univ.filter (· ≠ i), ‖star (u i) ⬝ᵥ u j‖ ^ (2 * t) with hXdef
  have hM : (0 : ℝ) < M := Nat.cast_pos.2 (Fin.pos i0)
  have hX0 : 0 ≤ X := by positivity
  -- Gram-matrix bound in each sector k ≥ t
  have hgram : ∀ k ∈ Ico t (L + 1), (M : ℝ) - X ≤ ∑ i, (srmDiag (L := L) u k i).re ^ 2 := by
    intro k hk
    have hkL : k ≤ L := by have := (mem_Ico.1 hk).2; omega
    have htk : t ≤ k := (mem_Ico.1 hk).1
    set Ψ := sectorMat (L := L) u k hkL
    have hdiag : ∀ i, (Ψᴴ * Ψ) i i = 1 := fun i => by rw [sectorMat_gram, hu, one_pow]
    have hb := srm_gram_bound (Ψᴴ * Ψ) (posSemidef_conjTranspose_mul_self Ψ) hdiag
    simp only [Fintype.card_fin] at hb
    have hsum : ∑ i, ∑ j, ‖(Ψᴴ * Ψ) i j‖ ^ 2 ≤ M + X := by
      rw [hXdef, show (M : ℝ) = ∑ _i : Fin M, (1 : ℝ) by simp, ← Finset.sum_add_distrib]
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
  -- assemble
  have hS : ∑ k ∈ Ico t (L + 1), binomPMF L η k = 1 - binomLT L η t := by
    have := binomLT_add_tail L η (t := t) (by omega); linarith
  have hBLT : 0 ≤ binomLT L η t :=
    Finset.sum_nonneg fun k _ => binomPMF_nonneg hη0 hη1 k
  have hmain : (M : ℝ) * (1 - binomLT L η t) - X ≤
      ∑ i, ((povmMat (L := L) u t i0 i *
        lossChannel η (ketbra (condensate (L := L) (u i) L))).trace).re := by
    calc (M : ℝ) * (1 - binomLT L η t) - X
        ≤ ∑ k ∈ Ico t (L + 1), binomPMF L η k * ((M : ℝ) - X) := by
          rw [← Finset.sum_mul, hS]; nlinarith
      _ ≤ ∑ k ∈ Ico t (L + 1), binomPMF L η k * ∑ i, (srmDiag (L := L) u k i).re ^ 2 :=
          Finset.sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_left (hgram k hk) (binomPMF_nonneg hη0 hη1 k)
      _ = ∑ i, ∑ k ∈ Ico t (L + 1), binomPMF L η k * (srmDiag (L := L) u k i).re ^ 2 := by
          simp only [Finset.mul_sum]; exact Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun i _ => success_term_ge hη0 hη1 u hu t i0 hc i
  dsimp only [Code.success, condensateCode]
  rw [le_div_iff₀ hM]
  have : (1 - binomLT L η t - X / M) * M = (M : ℝ) * (1 - binomLT L η t) - X := by
    field_simp
  linarith


/-- **Eq. (5), existence form.** If `t ≤ L`, `1 ≤ M ≤ C(n+t-1, t)` and
`Pr{K < t} + (M-1)·e / C(n+t-1,t) ≤ ε`, there is a code (inputs with exactly `L` photons)
with success probability at least `1 - ε`. -/
theorem exists_code {η ε : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {t M : ℕ} (hn : 1 ≤ n) (ht : t ≤ L)
    (hM : 1 ≤ M) (hMD : M ≤ (n + t - 1).choose t)
    (herr : binomLT L η t + ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ ε) :
    ∃ C : Code n L M, 1 - ε ≤ C.success η := by
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
  refine ⟨condensateCode (L := L) u hu t ⟨0, hM⟩ hcard, ?_⟩
  have hs := condensateCode_success hη0 hη1 u hu ht ⟨0, hM⟩ hcard
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

end QIQCOP
