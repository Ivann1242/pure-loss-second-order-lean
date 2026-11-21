import QIQCOP.Fock
import QIQCOP.Binomial

/-!
# Photon counting in the Heisenberg picture

For the `n`-mode pure-loss channel `𝒩 = lossChannel η` on the `≤ L`-photon Fock space and the
projector `Π_{≤ r} = lowProj r` onto at most `r` photons we show

`Tr[(1 - Π_{≤ r}) 𝒩(ρ)] = ∑_m ρ_mm · Pr{Bin(|m|, η) > r}`,

i.e. `∑_ℓ A_ℓᴴ (1 - Π_{≤ r}) A_ℓ` is diagonal in the Fock basis with the binomial upper tail on
the diagonal.  Consequences: bounds on the output weight above `r` photons in terms of the
binomial tail `binomGT`, which is monotone in the number of trials.
-/

open Finset Matrix
open scoped ComplexOrder

namespace QIQCOP

variable {n L : ℕ}

noncomputable section

/-- `Pr{K > r}` for `K ~ Bin(L, η)`. -/
def binomGT (L : ℕ) (η : ℝ) (r : ℕ) : ℝ := 1 - binomLT L η (r + 1)

/-- Projector onto at most `r` photons (diagonal in the Fock basis). -/
def lowProj (r : ℕ) : Matrix (Occ n L) (Occ n L) ℂ :=
  Matrix.diagonal fun m => if photons (m : Fin n → ℕ) ≤ r then 1 else 0

/-! ### The projector -/

theorem lowProj_isHermitian (r : ℕ) : (lowProj (n := n) (L := L) r).IsHermitian := by
  rw [lowProj, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  ext m
  rw [Pi.star_apply]
  split_ifs <;> simp

theorem lowProj_idem (r : ℕ) : lowProj (n := n) (L := L) r * lowProj r = lowProj r := by
  rw [lowProj, Matrix.diagonal_mul_diagonal]
  congr 1
  ext m
  split_ifs <;> simp

lemma one_sub_lowProj (r : ℕ) : (1 : Matrix (Occ n L) (Occ n L) ℂ) - lowProj (n := n) (L := L) r =
    Matrix.diagonal fun m : Occ n L => if photons (m : Fin n → ℕ) ≤ r then (0 : ℂ) else 1 := by
  ext i j
  simp only [lowProj, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- Hockey stick: `∑_{k ≤ r} C(n+k-1, k) = C(n+r, r)`. -/
lemma sum_sectorDim_nat (n r : ℕ) :
    ∑ k ∈ range (r + 1), (n + k - 1).choose k = (n + r).choose r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, show n + (r + 1) - 1 = n + r by omega,
      show n + (r + 1) = (n + r) + 1 by omega, Nat.choose_succ_succ]

/-- The `≤ r`-photon space of `n` modes has dimension `C(n+r, r)`. -/
theorem card_occSet (n r : ℕ) : (occSet n r).card = (n + r).choose r := by
  rw [occSet, Finset.card_biUnion]
  · simp only [card_sector]
    exact sum_sectorDim_nat n r
  · intro i _ j _ hij
    exact Finset.disjoint_left.2 fun m hi hj =>
      hij ((mem_sector.1 hi).symm.trans (mem_sector.1 hj))

/-- Rank of the projector: the `≤ r`-photon space of `n` modes has dimension `C(n+r, r)`. -/
theorem lowProj_trace {r : ℕ} (hr : r ≤ L) :
    (lowProj (n := n) (L := L) r).trace = (((n + r).choose r : ℕ) : ℂ) := by
  classical
  have hfil : (occSet n L).filter (fun m => photons m ≤ r) = occSet n r := by
    ext m; simp only [Finset.mem_filter, mem_occSet]; omega
  rw [lowProj, Matrix.trace_diagonal,
    Finset.sum_coe_sort (occSet n L) (fun m => if photons m ≤ r then (1 : ℂ) else 0),
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hfil, card_occSet]

lemma trace_diagonal_mul (d : Occ n L → ℂ) (ρ : Matrix (Occ n L) (Occ n L) ℂ) :
    (Matrix.diagonal d * ρ).trace = ∑ m, d m * ρ m m := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.diag_apply, Matrix.diagonal_mul]

/-! ### Multinomial Vandermonde: the number of survivors is binomial -/

open Polynomial in
/-- Summing the loss-pattern weights over patterns with exactly `k` survivors gives the
binomial probability `C(|m|, k) η^k (1-η)^{|m|-k}`. -/
lemma sum_survivors_eq (η : ℝ) (m : Fin n → ℕ) (k : ℕ) :
    ∑ ℓ ∈ Fintype.piFinset (fun j => range (m j + 1)),
      (if photons (m - ℓ) = k then
        ∏ j, ((m j).choose (ℓ j) : ℝ) * η ^ (m j - ℓ j) * (1 - η) ^ (ℓ j) else 0) =
      binomPMF (photons m) η k := by
  have hfac : ∀ N : ℕ, (C η * X + C (1 - η) : ℝ[X]) ^ N =
      ∑ i ∈ range (N + 1), C ((N.choose i : ℝ) * η ^ (N - i) * (1 - η) ^ i) * X ^ (N - i) := by
    intro N
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow, mul_pow, map_natCast]
    ring
  have hfac2 : ∀ N : ℕ, (C η * X + C (1 - η) : ℝ[X]) ^ N =
      ∑ i ∈ range (N + 1), C ((N.choose i : ℝ) * η ^ i * (1 - η) ^ (N - i)) * X ^ i := by
    intro N
    rw [add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow, mul_pow, map_natCast]
    ring
  have hP : ∏ j, (C η * X + C (1 - η) : ℝ[X]) ^ (m j) = (C η * X + C (1 - η)) ^ photons m :=
    Finset.prod_pow_eq_pow_sum _ _ _
  have hL : ∏ j, (C η * X + C (1 - η) : ℝ[X]) ^ (m j) =
      ∑ ℓ ∈ Fintype.piFinset (fun j => range (m j + 1)),
        C (∏ j, ((m j).choose (ℓ j) : ℝ) * η ^ (m j - ℓ j) * (1 - η) ^ (ℓ j)) *
          X ^ photons (m - ℓ) := by
    rw [Finset.prod_congr rfl fun j _ => hfac (m j),
      Finset.prod_univ_sum (fun j => range (m j + 1))
        (fun j i => (C (((m j).choose i : ℝ) * η ^ (m j - i) * (1 - η) ^ i) * X ^ (m j - i) : ℝ[X]))]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod]
    rfl
  have hR : ((C η * X + C (1 - η) : ℝ[X]) ^ photons m).coeff k = binomPMF (photons m) η k := by
    rw [hfac2, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · rw [binomPMF, Nat.choose_eq_zero_of_lt (by simpa using hk)]
      simp
  rw [← hR, ← hP, hL, finsetSum_coeff]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [coeff_C_mul_X_pow]
  by_cases h : photons (m - ℓ) = k
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- Summing the loss-pattern weights over patterns with more than `r` survivors gives the
binomial upper tail. -/
lemma sum_survivors_gt (η : ℝ) (m : Fin n → ℕ) (r : ℕ) :
    ∑ ℓ ∈ Fintype.piFinset (fun j => range (m j + 1)),
      (if r < photons (m - ℓ) then
        ∏ j, ((m j).choose (ℓ j) : ℝ) * η ^ (m j - ℓ j) * (1 - η) ^ (ℓ j) else 0) =
      binomGT (photons m) η r := by
  have h1 := sum_le_binom η m
  have h2 : ∑ ℓ ∈ Fintype.piFinset (fun j => range (m j + 1)),
      (if photons (m - ℓ) < r + 1 then
        ∏ j, ((m j).choose (ℓ j) : ℝ) * η ^ (m j - ℓ j) * (1 - η) ^ (ℓ j) else 0) =
      binomLT (photons m) η (r + 1) := by
    unfold binomLT
    rw [Finset.sum_congr rfl fun j _ => (sum_survivors_eq η m j).symm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
  unfold binomGT
  rw [← h2, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl fun ℓ _ => ?_).trans h1
  by_cases h : r < photons (m - ℓ)
  · rw [ite_eq_left h, ite_eq_right (by omega), add_zero]
  · rw [ite_eq_right h, ite_eq_left (by omega), zero_add]

/-! ### Heisenberg picture -/

/-- **Photon counting, Heisenberg picture**: `∑_ℓ A_ℓᴴ (1 - Π_{≤ r}) A_ℓ` is diagonal in the
Fock basis, with entry `Pr{Bin(|m|, η) > r}` at `m`. -/
theorem lossKraus_heisenberg_high {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (r : ℕ) :
    ∑ ℓ, (lossKraus (n := n) (L := L) η ℓ)ᴴ * (1 - lowProj r) * lossKraus η ℓ =
      Matrix.diagonal fun m : Occ n L => ((binomGT (photons (m : Fin n → ℕ)) η r : ℝ) : ℂ) := by
  classical
  rw [one_sub_lowProj]
  ext m m'
  have hE : ∀ ℓ : Occ n L, ((lossKraus η ℓ)ᴴ *
      (Matrix.diagonal fun x : Occ n L => if photons (x : Fin n → ℕ) ≤ r then (0 : ℂ) else 1) *
        lossKraus η ℓ) m m' =
      ∑ x : Occ n L, star (lossKraus η ℓ x m) *
        (if photons (x : Fin n → ℕ) ≤ r then (0 : ℂ) else 1) * lossKraus η ℓ x m' := by
    intro ℓ
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [Matrix.sum_apply, Finset.sum_congr rfl fun ℓ _ => hE ℓ]
  have hsub : ∀ ℓ : Occ n L, (m : Fin n → ℕ) - ℓ ∈ occSet n L := fun ℓ =>
    mem_occSet.2 (le_trans (photons_mono tsub_le_self) (mem_occSet.1 m.2))
  have key : ∀ ℓ : Occ n L, ∑ x : Occ n L, star (lossKraus η ℓ x m) *
        (if photons (x : Fin n → ℕ) ≤ r then (0 : ℂ) else 1) * lossKraus η ℓ x m' =
      star (lossKraus η ℓ ⟨_, hsub ℓ⟩ m) *
        (if photons ((m : Fin n → ℕ) - (ℓ : Fin n → ℕ)) ≤ r then (0 : ℂ) else 1) *
          lossKraus η ℓ ⟨_, hsub ℓ⟩ m' := by
    intro ℓ
    refine Finset.sum_eq_single (⟨_, hsub ℓ⟩ : Occ n L) (fun x _ hx => ?_) (by simp)
    have : lossKraus η ℓ x m = 0 := by
      rw [lossKraus, ite_eq_right]
      intro h; apply hx; apply Subtype.ext; simp [h]
    simp [this]
  rw [Finset.sum_congr rfl fun ℓ _ => key ℓ]
  by_cases hmm' : m = m'
  · subst hmm'
    rw [Matrix.diagonal_apply_eq]
    have hterm0 : ∀ ℓ : Occ n L,
        star (lossKraus η ℓ ⟨_, hsub ℓ⟩ m) * lossKraus η ℓ ⟨_, hsub ℓ⟩ m =
        (((if (ℓ : Fin n → ℕ) ≤ m then ∏ j, (((m : Fin n → ℕ) j).choose ((ℓ : Fin n → ℕ) j) : ℝ) *
          η ^ ((m : Fin n → ℕ) j - (ℓ : Fin n → ℕ) j) * (1 - η) ^ ((ℓ : Fin n → ℕ) j)
            else 0) : ℝ) : ℂ) := by
      intro ℓ
      by_cases hle : (ℓ : Fin n → ℕ) ≤ m
      · have h1 : (m : Fin n → ℕ) = ((m : Fin n → ℕ) - ℓ) + ℓ := (tsub_add_cancel_of_le hle).symm
        rw [lossKraus, ite_eq_left h1, ite_eq_left hle, Complex.star_def, Complex.conj_ofReal,
          ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Real.mul_self_sqrt]
        · simp
        · have := sub_nonneg.2 hη1
          positivity
      · have h1 : ¬ (m : Fin n → ℕ) = ((m : Fin n → ℕ) - ℓ) + ℓ := fun h =>
          hle (h ▸ le_add_self)
        rw [lossKraus, ite_eq_right h1, ite_eq_right hle]
        simp
    have hterm : ∀ ℓ : Occ n L,
        star (lossKraus η ℓ ⟨_, hsub ℓ⟩ m) *
          (if photons ((m : Fin n → ℕ) - (ℓ : Fin n → ℕ)) ≤ r then (0 : ℂ) else 1) *
            lossKraus η ℓ ⟨_, hsub ℓ⟩ m =
        (((if (ℓ : Fin n → ℕ) ≤ m then
            (if r < photons ((m : Fin n → ℕ) - (ℓ : Fin n → ℕ)) then
              ∏ j, (((m : Fin n → ℕ) j).choose ((ℓ : Fin n → ℕ) j) : ℝ) *
                η ^ ((m : Fin n → ℕ) j - (ℓ : Fin n → ℕ) j) * (1 - η) ^ ((ℓ : Fin n → ℕ) j)
            else 0)
          else 0) : ℝ) : ℂ) := by
      intro ℓ
      rw [mul_right_comm, hterm0]
      by_cases h2 : photons ((m : Fin n → ℕ) - (ℓ : Fin n → ℕ)) ≤ r
      · rw [ite_eq_left h2, ite_eq_right (not_lt.2 h2), mul_zero]
        simp
      · rw [ite_eq_right h2, ite_eq_left (not_le.1 h2), mul_one]
    have hfil : (occSet n L).filter (fun ℓ => ℓ ≤ (m : Fin n → ℕ)) =
        Fintype.piFinset (fun j => range ((m : Fin n → ℕ) j + 1)) := by
      ext ℓ
      simp only [Finset.mem_filter, mem_occSet, Fintype.mem_piFinset, Finset.mem_range,
        Nat.lt_succ_iff]
      constructor
      · rintro ⟨_, h⟩ j; exact h j
      · intro h; exact ⟨le_trans (photons_mono h) (mem_occSet.1 m.2), h⟩
    rw [Finset.sum_congr rfl fun ℓ _ => hterm ℓ, ← Complex.ofReal_sum,
      Finset.sum_coe_sort (occSet n L) (fun ℓ => if ℓ ≤ (m : Fin n → ℕ) then
        (if r < photons ((m : Fin n → ℕ) - (ℓ : Fin n → ℕ)) then
          ∏ j, (((m : Fin n → ℕ) j).choose (ℓ j) : ℝ) * η ^ ((m : Fin n → ℕ) j - ℓ j) *
            (1 - η) ^ (ℓ j) else 0) else 0),
      ← Finset.sum_filter, hfil, sum_survivors_gt]
  · rw [Matrix.diagonal_apply_ne _ hmm']
    refine Finset.sum_eq_zero fun ℓ _ => ?_
    by_cases h1 : (m : Fin n → ℕ) = ((m : Fin n → ℕ) - ℓ) + ℓ
    · have : lossKraus η ℓ ⟨_, hsub ℓ⟩ m' = 0 := by
        rw [lossKraus, ite_eq_right]
        intro h2; apply hmm'; apply Subtype.ext; rw [h1, h2]
      rw [this, mul_zero]
    · rw [lossKraus, ite_eq_right h1]; simp

/-- **Photon counting**: `Tr[(1 - Π_{≤r}) 𝒩(ρ)] = ∑_m ρ_mm · Pr{Bin(|m|, η) > r}`. -/
theorem trace_high_lossChannel {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (r : ℕ)
    (ρ : Matrix (Occ n L) (Occ n L) ℂ) :
    ((1 - lowProj r) * lossChannel η ρ).trace =
      ∑ m : Occ n L, ρ m m * (binomGT (photons (m : Fin n → ℕ)) η r : ℂ) := by
  have h1 : ((1 - lowProj r) * lossChannel η ρ).trace =
      ((∑ ℓ, (lossKraus (n := n) (L := L) η ℓ)ᴴ * (1 - lowProj r) * lossKraus η ℓ) * ρ).trace := by
    rw [lossChannel, Matrix.mul_sum, Matrix.trace_sum, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
  rw [h1, lossKraus_heisenberg_high hη0 hη1, trace_diagonal_mul]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

/-! ### The binomial upper tail -/

/-- Pascal's rule for the binomial distribution. -/
lemma binomPMF_succ_succ (L : ℕ) (η : ℝ) (k : ℕ) :
    binomPMF (L + 1) η (k + 1) = (1 - η) * binomPMF L η (k + 1) + η * binomPMF L η k := by
  unfold binomPMF
  rw [Nat.choose_succ_succ, Nat.succ_sub_succ]
  by_cases hk : k + 1 ≤ L
  · rw [show L - k = (L - (k + 1)) + 1 by omega]
    push_cast
    ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : L < k + 1)]
    push_cast
    ring

lemma binomLT_succ (L : ℕ) (η : ℝ) (r : ℕ) :
    binomLT (L + 1) η (r + 1) = binomLT L η (r + 1) - η * binomPMF L η r := by
  induction r with
  | zero =>
    simp only [binomLT, binomPMF, zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.sub_zero]
    ring
  | succ r ih =>
    have e1 : binomLT (L + 1) η (r + 1 + 1) =
        binomLT (L + 1) η (r + 1) + binomPMF (L + 1) η (r + 1) := by
      unfold binomLT; rw [Finset.sum_range_succ]
    have e2 : binomLT L η (r + 1 + 1) = binomLT L η (r + 1) + binomPMF L η (r + 1) := by
      unfold binomLT; rw [Finset.sum_range_succ]
    rw [e1, e2, ih, binomPMF_succ_succ]
    ring

/-- `Pr{Bin(L+1, η) > r} = Pr{Bin(L, η) > r} + η · Pr{Bin(L, η) = r}`. -/
lemma binomGT_succ (L : ℕ) (η : ℝ) (r : ℕ) :
    binomGT (L + 1) η r = binomGT L η r + η * binomPMF L η r := by
  unfold binomGT
  rw [binomLT_succ]
  ring

/-- The binomial upper tail is monotone in the number of trials. -/
theorem binomGT_mono {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (r : ℕ) {L₁ L₂ : ℕ} (h : L₁ ≤ L₂) :
    binomGT L₁ η r ≤ binomGT L₂ η r := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih =>
    refine ih.trans ?_
    rw [binomGT_succ]
    have := mul_nonneg hη0 (binomPMF_nonneg (L := m) hη0 hη1 r)
    linarith

lemma binomGT_zero (η : ℝ) (r : ℕ) : binomGT 0 η r = 0 := by
  unfold binomGT binomLT
  rw [Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp [binomPMF]
  · intro i _
    simp [binomPMF]

theorem binomGT_nonneg {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (L r : ℕ) : 0 ≤ binomGT L η r := by
  rw [← binomGT_zero η r]
  exact binomGT_mono hη0 hη1 r (Nat.zero_le L)

theorem binomGT_le_one {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (L r : ℕ) : binomGT L η r ≤ 1 := by
  unfold binomGT binomLT
  have : 0 ≤ ∑ j ∈ range (r + 1), binomPMF L η j :=
    Finset.sum_nonneg fun j _ => binomPMF_nonneg hη0 hη1 j
  linarith

/-! ### Consequences for states -/

lemma posSemidef_diag_re_nonneg {ρ : Matrix (Occ n L) (Occ n L) ℂ} (hρ : ρ.PosSemidef)
    (m : Occ n L) : 0 ≤ (ρ m m).re :=
  (Complex.nonneg_iff.1 (hρ.diag_nonneg (i := m))).1

lemma sum_diag_re_eq_one {ρ : Matrix (Occ n L) (Occ n L) ℂ} (hρt : ρ.trace = 1) :
    ∑ m, (ρ m m).re = 1 := by
  have := congrArg Complex.re hρt
  simpa [Matrix.trace] using this

/-- Consequence with leakage: if `ρ` is PSD with trace 1 and `w := Re Tr[(1 - Π_{≤L₀}) ρ]`
is the weight above `L₀` photons, then
`Re Tr[(1 - Π_{≤r}) 𝒩(ρ)] ≤ (1 - w) · Pr{Bin(L₀, η) > r} + w`. -/
theorem high_weight_le_of_leak {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (r L₀ : ℕ)
    (ρ : Matrix (Occ n L) (Occ n L) ℂ) (hρ : ρ.PosSemidef) (hρt : ρ.trace = 1) :
    (((1 - lowProj r) * lossChannel η ρ).trace).re ≤
      (1 - (((1 - lowProj L₀) * ρ).trace).re) * binomGT L₀ η r +
        (((1 - lowProj L₀) * ρ).trace).re := by
  have hp := posSemidef_diag_re_nonneg hρ
  have hsum := sum_diag_re_eq_one hρt
  have hw : (((1 - lowProj L₀) * ρ).trace).re =
      ∑ m : Occ n L, (ρ m m).re * (if photons (m : Fin n → ℕ) ≤ L₀ then (0 : ℝ) else 1) := by
    rw [one_sub_lowProj, trace_diagonal_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  have hl : (((1 - lowProj r) * lossChannel η ρ).trace).re =
      ∑ m : Occ n L, (ρ m m).re * binomGT (photons (m : Fin n → ℕ)) η r := by
    rw [trace_high_lossChannel hη0 hη1, Complex.re_sum]
    exact Finset.sum_congr rfl fun m _ => Complex.re_mul_ofReal _ _
  have e : ∑ m : Occ n L, (ρ m m).re *
        ((1 - (if photons (m : Fin n → ℕ) ≤ L₀ then (0 : ℝ) else 1)) * binomGT L₀ η r +
          (if photons (m : Fin n → ℕ) ≤ L₀ then (0 : ℝ) else 1)) =
      (∑ m : Occ n L, (ρ m m).re -
        ∑ m : Occ n L, (ρ m m).re * (if photons (m : Fin n → ℕ) ≤ L₀ then (0 : ℝ) else 1)) *
          binomGT L₀ η r +
        ∑ m : Occ n L, (ρ m m).re * (if photons (m : Fin n → ℕ) ≤ L₀ then (0 : ℝ) else 1) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hsum] at e
  rw [hl, hw, ← e]
  refine Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left ?_ (hp m)
  split_ifs with h
  · simpa using binomGT_mono hη0 hη1 r h
  · simpa using binomGT_le_one hη0 hη1 _ r

/-- Special case without leakage (all weight is at `≤ L` photons, automatic in `Occ n L`). -/
theorem high_weight_le {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (r : ℕ)
    (ρ : Matrix (Occ n L) (Occ n L) ℂ) (hρ : ρ.PosSemidef) (hρt : ρ.trace = 1) :
    (((1 - lowProj r) * lossChannel η ρ).trace).re ≤ binomGT L η r := by
  have hp := posSemidef_diag_re_nonneg hρ
  have hsum := sum_diag_re_eq_one hρt
  have hl : (((1 - lowProj r) * lossChannel η ρ).trace).re =
      ∑ m : Occ n L, (ρ m m).re * binomGT (photons (m : Fin n → ℕ)) η r := by
    rw [trace_high_lossChannel hη0 hη1, Complex.re_sum]
    exact Finset.sum_congr rfl fun m _ => Complex.re_mul_ofReal _ _
  rw [hl]
  calc ∑ m : Occ n L, (ρ m m).re * binomGT (photons (m : Fin n → ℕ)) η r
      ≤ ∑ m : Occ n L, (ρ m m).re * binomGT L η r :=
        Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left
          (binomGT_mono hη0 hη1 r (mem_occSet.1 m.2)) (hp m)
    _ = binomGT L η r := by rw [← Finset.sum_mul, hsum, one_mul]

end

end QIQCOP

