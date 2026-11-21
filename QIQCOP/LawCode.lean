import QIQCOP.ConverseMain
import QIQCOP.LeakAch

/-!
# Codes with a general photon-number law

For a code `C` in the `≤ L`-photon space, `C.law ℓ` is the weight of the average input state on
exactly `ℓ` photons.

* `Code.law`, `Code.meanPhotons`, `Code.law_nonneg`, `Code.sum_law`, `Code.meanPhotons_eq`.
* `converse_law` : finite-block converse in terms of the thinned law
  `∑_ℓ law ℓ · Pr{Bin(ℓ,η) > r}`.
* `lawCode`, `lawCode_success`, `lawCode_law`, `exists_lawCode` : achievability with codewords
  `ρᵢ = ∑_ℓ p ℓ |uᵢ;ℓ⟩⟨uᵢ;ℓ|` for an arbitrary law `p` on `≤ L` photons.
* `thinLT`, `quantile_ach`, `quantile_conv` : the photon-number quantile principle in
  threshold form.
-/

open Finset Matrix
open scoped ComplexOrder

namespace QIQCOP

noncomputable section

variable {n L M : ℕ}

/-! ### The photon-number law of a code -/

/-- Photon-number law of the average input state: weight on exactly `ℓ` photons. -/
def Code.law {n L M : ℕ} (C : Code n L M) (ℓ : ℕ) : ℝ :=
  (∑ i, ∑ m : Occ n L, if photons (m : Fin n → ℕ) = ℓ then (C.state i m m).re else 0) / M

/-- Mean total photon number of the average input state. -/
def Code.meanPhotons {n L M : ℕ} (C : Code n L M) : ℝ :=
  (∑ i, ∑ m : Occ n L, (photons (m : Fin n → ℕ) : ℝ) * (C.state i m m).re) / M

theorem Code.law_nonneg (C : Code n L M) (ℓ : ℕ) : 0 ≤ C.law ℓ := by
  unfold Code.law
  refine div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun m _ => ?_)
    (Nat.cast_nonneg M)
  split_ifs
  · exact posSemidef_diag_re_nonneg (C.state_psd i) m
  · exact le_rfl

/-- Expectation of a function of the photon number under the law of the code. -/
theorem Code.sum_law_mul (C : Code n L M) (f : ℕ → ℝ) :
    ∑ ℓ ∈ range (L + 1), C.law ℓ * f ℓ =
      (∑ i, ∑ m : Occ n L, (C.state i m m).re * f (photons (m : Fin n → ℕ))) / M := by
  unfold Code.law
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm : photons (m : Fin n → ℕ) ∈ range (L + 1) := by
    rw [mem_range]; have := mem_occSet.1 m.2; omega
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [hm, ↓reduceIte]

/-- The law is a probability distribution on `{0, …, L}`. -/
theorem Code.sum_law (C : Code n L M) (hM : 1 ≤ M) : ∑ ℓ ∈ range (L + 1), C.law ℓ = 1 := by
  have h := C.sum_law_mul (fun _ => 1)
  simp only [mul_one] at h
  rw [h, Finset.sum_congr rfl fun i _ => sum_diag_re_eq_one (C.state_trace i)]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  simp [hMr.ne']

theorem Code.meanPhotons_eq (C : Code n L M) :
    C.meanPhotons = ∑ ℓ ∈ range (L + 1), C.law ℓ * ℓ := by
  rw [C.sum_law_mul, Code.meanPhotons]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => mul_comm _ _

/-! ### Converse for a general law -/

/-- The average output weight above `r` photons is the thinned law's upper tail. -/
theorem Code.high_weight_eq {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (C : Code n L M) (r : ℕ) :
    (∑ i, (((1 - lowProj r) * lossChannel η (C.state i)).trace).re) / M =
      ∑ ℓ ∈ range (L + 1), C.law ℓ * binomGT ℓ η r := by
  rw [C.sum_law_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_high_lossChannel hη0 hη1, Complex.re_sum]
  exact Finset.sum_congr rfl fun m _ => Complex.re_mul_ofReal _ _

private lemma rearrange' {s D M q Q e ch : ℝ} (hM : 0 < M)
    (h : s ≤ (√(D / M) + √q) ^ 2) (hs : e ≤ s) (hqQ : q ≤ Q) (hQ0 : 0 ≤ Q) (hQ : Q < e)
    (hD : D ≤ ch) : M ≤ ch / (√e - √Q) ^ 2 := by
  have h1 : √e ≤ √(D / M) + √q := by
    rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg (D / M)) (Real.sqrt_nonneg q))]
    exact Real.sqrt_le_sqrt (hs.trans h)
  have h2 : √q ≤ √Q := Real.sqrt_le_sqrt hqQ
  have hc : 0 < √e - √Q := sub_pos.2 (Real.sqrt_lt_sqrt hQ0 hQ)
  have h3 : √e - √Q ≤ √(D / M) := by linarith
  have hDM : 0 ≤ D / M := by
    by_contra hneg
    rw [not_le] at hneg
    rw [Real.sqrt_eq_zero_of_nonpos hneg.le] at h3
    linarith
  have h4 : (√e - √Q) ^ 2 ≤ D / M := by
    have := pow_le_pow_left₀ hc.le h3 2
    rwa [Real.sq_sqrt hDM] at this
  rw [le_div_iff₀ (pow_pos hc 2)]
  rw [le_div_iff₀ hM] at h4
  nlinarith

/-- **Finite-blocklength converse for a general photon-number law.** -/
theorem converse_law {η ε : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {n L M : ℕ} (hM : 1 ≤ M)
    (C : Code n L M) (r : ℕ) (hs : 1 - ε ≤ C.success η)
    (hq : ∑ ℓ ∈ Finset.range (L + 1), C.law ℓ * binomGT ℓ η r < 1 - ε) :
    (M : ℝ) ≤ ((n + r).choose r : ℝ) /
      (√(1 - ε) - √(∑ ℓ ∈ Finset.range (L + 1), C.law ℓ * binomGT ℓ η r)) ^ 2 := by
  have hMpos : 0 < M := hM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hpb := projector_bound hMpos (fun i => lossChannel η (C.state i)) C.povm
    (fun i => lossChannel_posSemidef η (C.state_psd i))
    (fun i => by rw [lossChannel_trace hη0 hη1, C.state_trace])
    C.povm_psd C.povm_sum (lowProj r) (lowProj_isHermitian r) (lowProj_idem r)
  have hQ0 : 0 ≤ ∑ ℓ ∈ Finset.range (L + 1), C.law ℓ * binomGT ℓ η r :=
    Finset.sum_nonneg fun ℓ _ => mul_nonneg (C.law_nonneg ℓ) (binomGT_nonneg hη0 hη1 ℓ r)
  exact rearrange' hMr hpb hs (C.high_weight_eq hη0 hη1 r).le hQ0 hq (lowProj_trace_re_le r)

/-- The success probability of any code is at most `1`. -/
theorem Code.success_le_one {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hM : 1 ≤ M) (C : Code n L M) :
    C.success η ≤ 1 := by
  have hMpos : 0 < M := hM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hσt : ∀ i, (lossChannel η (C.state i)).trace = 1 := fun i => by
    rw [lossChannel_trace hη0 hη1, C.state_trace]
  have hpb := projector_bound hMpos (fun i => lossChannel η (C.state i)) C.povm
    (fun i => lossChannel_posSemidef η (C.state_psd i)) hσt
    C.povm_psd C.povm_sum 0 Matrix.isHermitian_zero (mul_zero 0)
  simp only [sub_zero, one_mul, hσt, Matrix.trace_zero, Complex.zero_re, zero_div,
    Real.sqrt_zero, zero_add, Complex.one_re, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, div_self hMr.ne', Real.sqrt_one, one_pow] at hpb
  exact hpb

/-! ### Achievability for a general law -/

lemma lossChannel_sum {ι : Type*} (η : ℝ) (s : Finset ι)
    (f : ι → Matrix (Occ n L) (Occ n L) ℂ) :
    lossChannel η (∑ k ∈ s, f k) = ∑ k ∈ s, lossChannel η (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lossChannel]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lossChannel_add, ih]

/-- `Pr{Bin(ℓ,η) < t} = 1` when `ℓ < t`. -/
lemma binomLT_eq_one_of_lt (η : ℝ) {ℓ t : ℕ} (h : ℓ < t) : binomLT ℓ η t = 1 := by
  unfold binomLT
  rw [← sum_binomPMF ℓ η]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_of_lt h)) fun k _ hk => ?_
  rw [mem_range, not_lt] at hk
  unfold binomPMF
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- Summed success bound for input condensates with any photon number `K ≤ L` (for `K < t`
the bound is trivial since `Pr{Bin(K,η) < t} = 1`). -/
lemma sum_success_ge_all {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (u : Fin M → Fin n → ℂ)
    (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) {t : ℕ} (i0 : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k))
    {K : ℕ} (hK : K ≤ L) :
    (M : ℝ) * (1 - binomLT K η t) - overlapSum u t ≤
      ∑ i, ((povmMat (L := L) u t i0 i *
        lossChannel η (ketbra (condensate (L := L) (u i) K))).trace).re := by
  rcases le_or_gt t K with h | h
  · exact sum_success_ge hη0 hη1 u hu i0 hc h hK
  · rw [binomLT_eq_one_of_lt η h]
    have h0 : ∀ i, 0 ≤ ((povmMat (L := L) u t i0 i *
        lossChannel η (ketbra (condensate (L := L) (u i) K))).trace).re := fun i => by
      have := success_term_ge_gen hη0 hη1 u hu t i0 hc hK i
      rwa [Finset.Ico_eq_empty (by omega), Finset.sum_empty] at this
    have h1 := Finset.sum_nonneg fun i (_ : i ∈ (univ : Finset (Fin M))) => h0 i
    have h2 := overlapSum_nonneg u t
    linarith

/-- **The condensate code with photon-number law `p`**: codewords
`∑_{ℓ ≤ L} p ℓ |uᵢ;ℓ⟩⟨uᵢ;ℓ|`, with the decoder of `condensateCode`. -/
def lawCode (u : Fin M → Fin n → ℂ) (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) (t : ℕ)
    (i0 : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k))
    (p : ℕ → ℝ) (hp0 : ∀ ℓ, 0 ≤ p ℓ) (hp1 : ∑ ℓ ∈ range (L + 1), p ℓ = 1) :
    Code n L M where
  state i := ∑ ℓ ∈ range (L + 1), ((p ℓ : ℝ) : ℂ) • ketbra (condensate (L := L) (u i) ℓ)
  state_psd i := posSemidef_sum _ fun ℓ _ =>
    (ketbra_posSemidef _).smul (Complex.zero_le_real.2 (hp0 ℓ))
  state_trace i := by
    rw [trace_sum, Finset.sum_congr rfl fun ℓ hℓ => by
      rw [trace_smul, trace_ketbra_condensate _ (hu i)
        (by have := mem_range.1 hℓ; omega : ℓ ≤ L), smul_eq_mul, mul_one],
      ← Complex.ofReal_sum, hp1]
    simp
  povm := povmMat (L := L) u t i0
  povm_psd i := (Pmat_posSemidef u t i).add (povmMat_rest_posSemidef u t i0 i hc)
  povm_sum := by
    unfold povmMat
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [Qmat]

/-- **Finite-block success bound for the law code** (fixed codebook):
success `≥ 1 - ∑_ℓ p ℓ Pr{Bin(ℓ,η) < t} - (1/M) ∑_{i≠j} |⟨uᵢ|uⱼ⟩|^{2t}`. -/
theorem lawCode_success {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (u : Fin M → Fin n → ℂ)
    (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) {t : ℕ} (i0 : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k))
    (p : ℕ → ℝ) (hp0 : ∀ ℓ, 0 ≤ p ℓ) (hp1 : ∑ ℓ ∈ range (L + 1), p ℓ = 1) :
    1 - ∑ ℓ ∈ range (L + 1), p ℓ * binomLT ℓ η t -
        (∑ i, ∑ j ∈ univ.filter (· ≠ i), ‖star (u i) ⬝ᵥ u j‖ ^ (2 * t)) / M ≤
      (lawCode (L := L) u hu t i0 hc p hp0 hp1).success η := by
  change 1 - ∑ ℓ ∈ range (L + 1), p ℓ * binomLT ℓ η t - overlapSum u t / M ≤ _
  set X := overlapSum u t with hXdef
  have hM : (0 : ℝ) < M := Nat.cast_pos.2 (Fin.pos i0)
  have hsplit : ∀ i, ((povmMat (L := L) u t i0 i * lossChannel η
      (∑ ℓ ∈ range (L + 1), ((p ℓ : ℝ) : ℂ) • ketbra (condensate (L := L) (u i) ℓ))).trace).re =
      ∑ ℓ ∈ range (L + 1), p ℓ * ((povmMat (L := L) u t i0 i *
        lossChannel η (ketbra (condensate (L := L) (u i) ℓ))).trace).re := by
    intro i
    rw [lossChannel_sum, Finset.mul_sum, trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [lossChannel_smul, mul_smul_comm, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  dsimp only [Code.success, lawCode]
  rw [le_div_iff₀ hM, Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_comm]
  have e : (1 - ∑ ℓ ∈ range (L + 1), p ℓ * binomLT ℓ η t - X / M) * M =
      ∑ ℓ ∈ range (L + 1), p ℓ * ((M : ℝ) * (1 - binomLT ℓ η t) - X) := by
    have e1 : ∑ ℓ ∈ range (L + 1), p ℓ * ((M : ℝ) * (1 - binomLT ℓ η t) - X) =
        (M - X) * ∑ ℓ ∈ range (L + 1), p ℓ -
          M * ∑ ℓ ∈ range (L + 1), p ℓ * binomLT ℓ η t := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
    rw [e1, hp1]
    field_simp
    ring
  rw [e]
  refine Finset.sum_le_sum fun ℓ hℓ => ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_success_ge_all hη0 hη1 u hu i0 hc (by have := mem_range.1 hℓ; omega)) (hp0 ℓ)

lemma ketbra_diag_re {D : Type*} (ψ : D → ℂ) (m : D) : ((ketbra ψ) m m).re = ‖ψ m‖ ^ 2 := by
  rw [ketbra, vecMulVec_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The law code has photon-number law exactly `p`. -/
theorem lawCode_law (u : Fin M → Fin n → ℂ) (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) (t : ℕ)
    (i0 : Fin M)
    (hc : ∀ k ∈ Ico t (L + 1), Fintype.card (Fin M) ≤ Fintype.card ↥(sector n k))
    (p : ℕ → ℝ) (hp0 : ∀ ℓ, 0 ≤ p ℓ) (hp1 : ∑ ℓ ∈ range (L + 1), p ℓ = 1)
    {ℓ : ℕ} (hℓ : ℓ ≤ L) :
    (lawCode (L := L) u hu t i0 hc p hp0 hp1).law ℓ = p ℓ := by
  have hM : (0 : ℝ) < M := Nat.cast_pos.2 (Fin.pos i0)
  have hd : ∀ (i : Fin M) (m : Occ n L),
      ((∑ k ∈ range (L + 1), ((p k : ℝ) : ℂ) • ketbra (condensate (L := L) (u i) k)) m m).re =
        p (photons (m : Fin n → ℕ)) *
          ‖condensate (L := L) (u i) (photons (m : Fin n → ℕ)) m‖ ^ 2 := by
    intro i m
    rw [Matrix.sum_apply, Complex.re_sum, Finset.sum_eq_single (photons (m : Fin n → ℕ))]
    · rw [Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul, ketbra_diag_re]
    · intro k _ hk
      rw [Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul, ketbra_diag_re,
        condensate_eq_zero (Ne.symm hk)]
      simp
    · intro h
      exact absurd (mem_range.2 (by have := mem_occSet.1 m.2; omega)) h
  have hin : ∀ i : Fin M, (∑ m : Occ n L, if photons (m : Fin n → ℕ) = ℓ then
      ((∑ k ∈ range (L + 1), ((p k : ℝ) : ℂ) • ketbra (condensate (L := L) (u i) k)) m m).re
        else 0) = p ℓ := by
    intro i
    rw [← mul_one (p ℓ), ← sum_norm_sq_condensate (L := L) (u i) (hu i) hℓ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · rw [hd, h]
    · rw [condensate_eq_zero h]; simp
  dsimp only [Code.law, lawCode]
  rw [Finset.sum_congr rfl fun i _ => hin i]
  simp [hM.ne']

/-- **Finite-block achievability for a general photon-number law.** -/
theorem exists_lawCode {η ε : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {n L t M : ℕ} (hn : 1 ≤ n)
    (_ht : t ≤ L) (p : ℕ → ℝ) (hp0 : ∀ ℓ, 0 ≤ p ℓ) (hp1 : ∑ ℓ ∈ Finset.range (L + 1), p ℓ = 1)
    (hM : 1 ≤ M) (hMD : M ≤ (n + t - 1).choose t)
    (herr : ∑ ℓ ∈ Finset.range (L + 1), p ℓ * binomLT ℓ η t +
      ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ ε) :
    ∃ C : Code n L M, 1 - ε ≤ C.success η ∧ (∀ ℓ, ℓ ≤ L → C.law ℓ = p ℓ) ∧
      C.meanPhotons = ∑ ℓ ∈ Finset.range (L + 1), p ℓ * ℓ := by
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
  have hlaw : ∀ ℓ, ℓ ≤ L → (lawCode (L := L) u hu t ⟨0, hM⟩ hcard p hp0 hp1).law ℓ = p ℓ :=
    fun ℓ hℓ => lawCode_law u hu t ⟨0, hM⟩ hcard p hp0 hp1 hℓ
  refine ⟨lawCode (L := L) u hu t ⟨0, hM⟩ hcard p hp0 hp1, ?_, hlaw, ?_⟩
  · have hs := lawCode_success hη0 hη1 u hu ⟨0, hM⟩ hcard p hp0 hp1
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
  · rw [Code.meanPhotons_eq]
    exact Finset.sum_congr rfl fun ℓ hℓ => by
      rw [hlaw ℓ (by have := mem_range.1 hℓ; omega)]

/-! ### The photon-number quantile principle, threshold form -/

/-- `Pr{K_P < t}` for the thinned law: `∑_ℓ p ℓ · Pr{Bin(ℓ,η) < t}`. -/
def thinLT (η : ℝ) (p : ℕ → ℝ) (L t : ℕ) : ℝ := ∑ ℓ ∈ Finset.range (L + 1), p ℓ * binomLT ℓ η t

/-- **Quantile principle, achievability.** If `Pr{K_P < t} ≤ ε - γ` for the thinned law of `p`,
there is a code with law `p`, success `≥ 1 - ε` and `M ≥ γ · C(n+t-1,t) / e - 1` messages. -/
theorem quantile_ach {η ε γ : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {n L t : ℕ} (hn : 1 ≤ n)
    (ht : t ≤ L) (p : ℕ → ℝ) (hp0 : ∀ ℓ, 0 ≤ p ℓ) (hp1 : ∑ ℓ ∈ Finset.range (L + 1), p ℓ = 1)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hth : thinLT η p L t ≤ ε - γ) :
    ∃ M : ℕ, M = max 1 ⌊γ * sectorDim n t / Real.exp 1⌋₊ ∧ 1 ≤ M ∧
      γ * sectorDim n t / Real.exp 1 - 1 ≤ (M : ℝ) ∧
      ∃ C : Code n L M, 1 - ε ≤ C.success η ∧ (∀ ℓ, ℓ ≤ L → C.law ℓ = p ℓ) ∧
        C.meanPhotons = ∑ ℓ ∈ Finset.range (L + 1), p ℓ * ℓ := by
  have hD1 : (1 : ℝ) ≤ sectorDim n t := by
    unfold sectorDim; exact_mod_cast Nat.choose_pos (by omega)
  have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set z := γ * sectorDim n t / Real.exp 1 with hz
  have hz0 : 0 < z := by positivity
  have hzD : z ≤ sectorDim n t := by
    rw [hz, div_le_iff₀ he0]; nlinarith
  set M : ℕ := max 1 ⌊z⌋₊ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMz : (M : ℝ) - 1 ≤ z := by
    rcases le_total 1 ⌊z⌋₊ with h | h
    · rw [hM, max_eq_right h]; have := Nat.floor_le hz0.le; linarith
    · rw [hM, max_eq_left h]; push_cast; linarith
  have hMlow : z - 1 ≤ (M : ℝ) := by
    have h2 : (⌊z⌋₊ : ℝ) ≤ M := by exact_mod_cast le_max_right 1 ⌊z⌋₊
    have h3 := Nat.sub_one_lt_floor z
    linarith
  have hMD : M ≤ (n + t - 1).choose t := by
    have : (M : ℝ) ≤ sectorDim n t := by
      rcases le_total 1 ⌊z⌋₊ with h | h
      · rw [hM, max_eq_right h]; exact (Nat.floor_le hz0.le).trans hzD
      · rw [hM, max_eq_left h]; push_cast; exact hD1
    unfold sectorDim at this; exact_mod_cast this
  have herr : ∑ ℓ ∈ Finset.range (L + 1), p ℓ * binomLT ℓ η t +
      ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ ε := by
    have h1 : ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ γ := by
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_right hMz he0.le
      rw [hz] at this; field_simp at this; linarith
    unfold thinLT at hth
    linarith
  exact ⟨M, rfl, hM1, hMlow, exists_lawCode hη0 hη1 hn ht p hp0 hp1 hM1 hMD herr⟩

/-- The thinned upper tail of the law of a code is `1 - Pr{K_P ≤ r}`. -/
theorem Code.sum_law_binomGT (C : Code n L M) (hM : 1 ≤ M) (η : ℝ) (r : ℕ) :
    ∑ ℓ ∈ Finset.range (L + 1), C.law ℓ * binomGT ℓ η r = 1 - thinLT η C.law L (r + 1) := by
  unfold thinLT binomGT
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, C.sum_law hM]

/-- **Quantile principle, converse.** If the thinned law of a code with success `≥ 1 - ε`
satisfies `Pr{K_P ≤ r} ≥ ε + γ`, then `M ≤ (4/γ²) · C(n+r, r)`. -/
theorem quantile_conv {η ε γ : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {n L M : ℕ} (hM : 1 ≤ M)
    (C : Code n L M) (r : ℕ) (hs : 1 - ε ≤ C.success η) (hγ0 : 0 < γ)
    (hth : ε + γ ≤ thinLT η C.law L (r + 1)) :
    (M : ℝ) ≤ 4 / γ ^ 2 * ((n + r).choose r : ℝ) := by
  set Q := ∑ ℓ ∈ Finset.range (L + 1), C.law ℓ * binomGT ℓ η r with hQ
  have hQe : Q = 1 - thinLT η C.law L (r + 1) := C.sum_law_binomGT hM η r
  have hQ0 : 0 ≤ Q :=
    Finset.sum_nonneg fun ℓ _ => mul_nonneg (C.law_nonneg ℓ) (binomGT_nonneg hη0 hη1 ℓ r)
  have hQle : Q ≤ 1 - ε - γ := by linarith
  have ha1 : 1 - ε ≤ 1 := hs.trans (C.success_le_one hη0 hη1 hM)
  have hconv := converse_law hη0 hη1 hM C r hs (by linarith)
  rw [← hQ] at hconv
  have ha0 : 0 ≤ 1 - ε := by linarith
  have hsa1 : √(1 - ε) ≤ 1 := by
    have := Real.sqrt_le_sqrt ha1
    rwa [Real.sqrt_one] at this
  have hsQa : √Q ≤ √(1 - ε) := Real.sqrt_le_sqrt (by linarith)
  have hsQ0 : 0 ≤ √Q := Real.sqrt_nonneg _
  have hprod : (√(1 - ε) - √Q) * (√(1 - ε) + √Q) = 1 - ε - Q := by
    have h1 := Real.mul_self_sqrt ha0
    have h2 := Real.mul_self_sqrt hQ0
    nlinarith
  have hc : γ / 2 ≤ √(1 - ε) - √Q := by
    have hd0 : 0 ≤ √(1 - ε) - √Q := by linarith
    nlinarith
  have hch : (0 : ℝ) ≤ ((n + r).choose r : ℝ) := Nat.cast_nonneg _
  have hc0 : 0 < γ / 2 := by linarith
  calc (M : ℝ) ≤ ((n + r).choose r : ℝ) / (√(1 - ε) - √Q) ^ 2 := hconv
    _ ≤ ((n + r).choose r : ℝ) / (γ / 2) ^ 2 :=
        div_le_div_of_nonneg_left hch (pow_pos hc0 2) (pow_le_pow_left₀ hc0.le hc 2)
    _ = 4 / γ ^ 2 * ((n + r).choose r : ℝ) := by field_simp; ring

end

end QIQCOP
