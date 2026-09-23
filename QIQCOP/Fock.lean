import QIQCOP.Sector

/-!
# The `n`-mode pure-loss channel on the `≤ L`-photon Fock space, and condensate states

* `lossKraus η ℓ` : Kraus operator of `𝒩_η^{⊗n}` for loss pattern `ℓ`,
  `A_ℓ |m⟩ = ∏ⱼ √(C(mⱼ,ℓⱼ) η^{mⱼ-ℓⱼ} (1-η)^{ℓⱼ}) |m - ℓ⟩`
  (the standard Fock-basis operator-sum form of the single-mode pure-loss channel,
  tensored over modes). Pure loss never increases photon number, so it maps the
  `≤ L`-photon space to itself.
* `condensate u k` : `|u;k⟩ = (∑ⱼ uⱼ aⱼ†)^k / √k! |0⟩`,
  with Fock coefficients `√(k!/∏ⱼ mⱼ!) ∏ⱼ uⱼ^{mⱼ}` on the `k`-photon sector.

Main facts: completeness of the Kraus operators (trace preservation), the overlap identity
`⟨u;k|v;k⟩ = ⟨u|v⟩^k` (proof.md (3)), and the loss identity (proof.md (2)).
-/

open Finset Matrix

namespace QIQCOP

variable {n L : ℕ}

noncomputable section

/-- Kraus operator of the `n`-mode pure-loss channel for loss pattern `ℓ`. -/
def lossKraus (η : ℝ) (ℓ : Occ n L) : Matrix (Occ n L) (Occ n L) ℂ :=
  fun r m =>
    if (m : Fin n → ℕ) = (r : Fin n → ℕ) + (ℓ : Fin n → ℕ) then
      ((∏ j, √((((m : Fin n → ℕ) j).choose ((ℓ : Fin n → ℕ) j) : ℝ) *
        η ^ ((r : Fin n → ℕ) j) * (1 - η) ^ ((ℓ : Fin n → ℕ) j)) : ℝ) : ℂ)
    else 0

/-- The `n`-mode pure-loss channel `𝒩_η^{⊗n}` acting on density matrices of the
`≤ L`-photon space. -/
def lossChannel (η : ℝ) (ρ : Matrix (Occ n L) (Occ n L) ℂ) : Matrix (Occ n L) (Occ n L) ℂ :=
  ∑ ℓ, lossKraus η ℓ * ρ * (lossKraus η ℓ)ᴴ

/-- The condensate `|u;k⟩`, as a vector of the `≤ L`-photon space. -/
def condensate (u : Fin n → ℂ) (k : ℕ) : Occ n L → ℂ := fun m =>
  if photons (m : Fin n → ℕ) = k then
    ((√((k.factorial : ℝ) / ∏ j, (((m : Fin n → ℕ) j).factorial : ℝ)) : ℝ) : ℂ) *
      ∏ j, u j ^ ((m : Fin n → ℕ) j)
  else 0

/-- `|ψ⟩⟨ψ|`. -/
def ketbra {D : Type*} (ψ : D → ℂ) : Matrix D D ℂ := vecMulVec ψ (star ψ)

/-- Photon number is additive. -/
lemma photons_add (a b : Fin n → ℕ) : photons (a + b) = photons a + photons b := by
  simp [photons, Finset.sum_add_distrib]

/-- Photon number is monotone. -/
lemma photons_mono {a b : Fin n → ℕ} (h : a ≤ b) : photons a ≤ photons b :=
  Finset.sum_le_sum fun j _ => h j

/-- Binomial theorem over all modes: `∑_{ℓ ≤ m} ∏ⱼ C(mⱼ,ℓⱼ) η^{mⱼ-ℓⱼ} (1-η)^{ℓⱼ} = 1`. -/
lemma sum_le_binom (η : ℝ) (m : Fin n → ℕ) :
    ∑ ℓ ∈ Fintype.piFinset (fun j => range (m j + 1)),
      ∏ j, ((m j).choose (ℓ j) : ℝ) * η ^ (m j - ℓ j) * (1 - η) ^ (ℓ j) = 1 := by
  rw [← Finset.prod_univ_sum (fun j => range (m j + 1))
    (fun j i => ((m j).choose i : ℝ) * η ^ (m j - i) * (1 - η) ^ i)]
  refine Finset.prod_eq_one fun j _ => ?_
  have := (add_pow (1 - η) η (m j)).symm
  rw [sub_add_cancel, one_pow] at this
  refine Eq.trans ?_ this
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Trace preservation: `∑_ℓ A_ℓᴴ A_ℓ = 1`. -/
theorem lossKraus_complete {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∑ ℓ, (lossKraus (n := n) (L := L) η ℓ)ᴴ * lossKraus η ℓ = 1 := by
  classical
  ext m m'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have hsub : ∀ ℓ : Occ n L, (m : Fin n → ℕ) - ℓ ∈ occSet n L := fun ℓ =>
    mem_occSet.2 (le_trans (photons_mono tsub_le_self) (mem_occSet.1 m.2))
  have key : ∀ ℓ : Occ n L, ∑ r, star (lossKraus η ℓ r m) * lossKraus η ℓ r m' =
      star (lossKraus η ℓ ⟨_, hsub ℓ⟩ m) * lossKraus η ℓ ⟨_, hsub ℓ⟩ m' := by
    intro ℓ
    refine Finset.sum_eq_single _ (fun r _ hr => ?_) (by simp)
    have : lossKraus η ℓ r m = 0 := by
      rw [lossKraus, ite_eq_right]
      intro h; apply hr; apply Subtype.ext; simp [h]
    simp [this]
  rw [Finset.sum_congr rfl fun ℓ _ => key ℓ]
  split_ifs with hmm'
  · subst hmm'
    have hterm : ∀ ℓ : Occ n L, star (lossKraus η ℓ ⟨_, hsub ℓ⟩ m) * lossKraus η ℓ ⟨_, hsub ℓ⟩ m =
        (((if (ℓ : Fin n → ℕ) ≤ m then ∏ j, (((m : Fin n → ℕ) j).choose ((ℓ : Fin n → ℕ) j) : ℝ) *
          η ^ ((m : Fin n → ℕ) j - (ℓ : Fin n → ℕ) j) * (1 - η) ^ ((ℓ : Fin n → ℕ) j) else 0) : ℝ) : ℂ) := by
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
        ∏ j, (((m : Fin n → ℕ) j).choose (ℓ j) : ℝ) * η ^ ((m : Fin n → ℕ) j - ℓ j) *
          (1 - η) ^ (ℓ j) else 0),
      ← Finset.sum_filter, hfil, sum_le_binom, Complex.ofReal_one]
  · refine Finset.sum_eq_zero fun ℓ _ => ?_
    by_cases h1 : (m : Fin n → ℕ) = ((m : Fin n → ℕ) - ℓ) + ℓ
    · have : lossKraus η ℓ ⟨_, hsub ℓ⟩ m' = 0 := by
        rw [lossKraus, ite_eq_right]
        intro h2; apply hmm'; apply Subtype.ext; rw [h1, h2]
      rw [this, mul_zero]
    · rw [lossKraus, ite_eq_right h1]; simp

/-- The condensate lives in the `k`-photon sector. -/
lemma condensate_eq_zero {u : Fin n → ℂ} {k : ℕ} {m : Occ n L}
    (h : photons (m : Fin n → ℕ) ≠ k) : condensate u k m = 0 := by
  simp [condensate, h]

/-- Overlap identity `⟨u;k|v;k⟩ = ⟨u|v⟩^k` (proof.md (3)); in particular `‖|u;k⟩‖ = ‖u‖^k`. -/
theorem condensate_inner (u v : Fin n → ℂ) {k : ℕ} (hk : k ≤ L) :
    star (condensate (L := L) u k) ⬝ᵥ condensate v k = (star u ⬝ᵥ v) ^ k := by
  classical
  set F : (Fin n → ℕ) → ℂ := fun m => if photons m = k then
    (((k.factorial : ℝ) / ∏ j, ((m j).factorial : ℝ) : ℝ) : ℂ) * ∏ j, (star (u j) * v j) ^ (m j)
    else 0 with hF
  have h1 : ∀ m : Occ n L, star (condensate (L := L) u k m) * condensate v k m = F m := by
    intro m
    simp only [condensate, hF]
    split_ifs with h
    · have h0 : (0 : ℝ) ≤ (k.factorial : ℝ) / ∏ j, (((m : Fin n → ℕ) j).factorial : ℝ) := by
        positivity
      have hx : ((√((k.factorial : ℝ) / ∏ j, (((m : Fin n → ℕ) j).factorial : ℝ)) : ℝ) : ℂ) *
          ((√((k.factorial : ℝ) / ∏ j, (((m : Fin n → ℕ) j).factorial : ℝ)) : ℝ) : ℂ) =
          (((k.factorial : ℝ) / ∏ j, (((m : Fin n → ℕ) j).factorial : ℝ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal, map_prod, map_pow]
      rw [Finset.prod_congr rfl fun j _ => mul_pow _ (v j) _, Finset.prod_mul_distrib]
      linear_combination (∏ j, (starRingEnd ℂ) (u j) ^ ((m : Fin n → ℕ) j)) *
        (∏ j, v j ^ ((m : Fin n → ℕ) j)) * hx
    · simp
  rw [dotProduct]
  simp only [Pi.star_apply]
  rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_coe_sort (occSet n L) F, hF,
    ← Finset.sum_filter]
  have hfil : (occSet n L).filter (fun m => photons m = k) = sector n k := by
    ext m; simp only [Finset.mem_filter, mem_occSet, mem_sector]; omega
  rw [hfil, dotProduct, Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hs : ∑ j, m j = k := mem_sector.1 hm
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin n)) m
  rw [hs] at hspec
  have hmul : ((Nat.multinomial Finset.univ m : ℕ) : ℝ) = (k.factorial : ℝ) / ∏ j, ((m j).factorial : ℝ) := by
    rw [eq_div_iff (by positivity), mul_comm]
    exact_mod_cast hspec
  simp only [Pi.star_apply]
  rw [← hmul]
  push_cast
  rfl

/-- The real-coefficient identity behind `A_ℓ |u;L⟩ ∝ |u;L-|ℓ|⟩`. -/
lemma loss_coeff_identity {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (r ℓ : Fin n → ℕ) :
    (∏ j, √(((r j + ℓ j).choose (ℓ j) : ℝ) * η ^ (r j) * (1 - η) ^ (ℓ j))) *
      √(((photons r + photons ℓ).factorial : ℝ) / ∏ j, ((r j + ℓ j).factorial : ℝ)) =
    √(binomPMF (photons r + photons ℓ) η (photons r + photons ℓ - photons ℓ)) *
      √(((photons ℓ).factorial : ℝ) / ∏ j, ((ℓ j).factorial : ℝ)) *
      √(((photons r + photons ℓ - photons ℓ).factorial : ℝ) / ∏ j, ((r j).factorial : ℝ)) := by
  have h1η : 0 ≤ 1 - η := sub_nonneg.2 hη1
  have hB : 0 ≤ binomPMF (photons r + photons ℓ) η (photons r + photons ℓ - photons ℓ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hη0 _)) (pow_nonneg h1η _)
  rw [← Real.sqrt_prod _ fun j _ => by positivity, ← Real.sqrt_mul' _ (by positivity),
    ← Real.sqrt_mul' _ (by positivity), ← Real.sqrt_mul' _ (by positivity)]
  congr 1
  rw [Nat.add_sub_cancel, binomPMF, Nat.add_sub_cancel_left, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  rw [show ∑ j, r j = photons r from rfl, show ∑ j, ℓ j = photons ℓ from rfl]
  have hC : (∏ j, (((r j + ℓ j).choose (ℓ j) : ℕ) : ℝ)) * (∏ j, ((r j).factorial : ℝ)) *
      (∏ j, ((ℓ j).factorial : ℝ)) = ∏ j, ((r j + ℓ j).factorial : ℝ) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial (r j) (ℓ j)
  have hL : (((photons r + photons ℓ).choose (photons r) : ℕ) : ℝ) * ((photons r).factorial : ℝ) *
      ((photons ℓ).factorial : ℝ) = ((photons r + photons ℓ).factorial : ℝ) := by
    have := Nat.add_choose_mul_factorial_mul_factorial (photons ℓ) (photons r)
    rw [add_comm (photons ℓ)] at this
    rw [mul_right_comm]
    exact_mod_cast this
  have hPC : (∏ j, (((r j + ℓ j).choose (ℓ j) : ℕ) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ =>
      Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_left _ _)).ne'
  have hPR : (∏ j, ((r j).factorial : ℝ)) ≠ 0 := by positivity
  have hPL : (∏ j, ((ℓ j).factorial : ℝ)) ≠ 0 := by positivity
  rw [← hC, ← hL]
  field_simp

/-- Loss acting on a condensate: `A_ℓ |u;L⟩ = √(Pr[K = L-|ℓ|]) ⟨ℓ|u;|ℓ|⟩ |u;L-|ℓ|⟩`. -/
lemma lossKraus_mulVec_condensate {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (u : Fin n → ℂ)
    (ℓ : Occ n L) :
    lossKraus η ℓ *ᵥ condensate (L := L) u L =
      ((((√(binomPMF L η (L - photons (ℓ : Fin n → ℕ)))) : ℝ) : ℂ) *
        condensate (L := L) u (photons (ℓ : Fin n → ℕ)) ℓ) •
        condensate (L := L) u (L - photons (ℓ : Fin n → ℕ)) := by
  have hs : photons (ℓ : Fin n → ℕ) ≤ L := mem_occSet.1 ℓ.2
  ext r
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  by_cases hr : photons (r : Fin n → ℕ) + photons (ℓ : Fin n → ℕ) ≤ L
  · have hmem : (r : Fin n → ℕ) + ℓ ∈ occSet n L := by
      rw [mem_occSet, photons_add]; exact hr
    rw [Finset.sum_eq_single ⟨_, hmem⟩ (fun m _ hm => ?_) (by simp)]
    swap
    · rw [lossKraus, ite_eq_right, zero_mul]
      intro h; exact hm (Subtype.ext h)
    by_cases ht : photons (r : Fin n → ℕ) + photons (ℓ : Fin n → ℕ) = L
    · have hpr : photons (r : Fin n → ℕ) = L - photons (ℓ : Fin n → ℕ) := by omega
      have e1 : photons ((⟨_, hmem⟩ : Occ n L) : Fin n → ℕ) = L := by
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
    · rw [condensate_eq_zero (m := ⟨_, hmem⟩) (by rw [Subtype.coe_mk, photons_add]; exact ht),
        condensate_eq_zero (m := r) (by omega)]
      simp
  · rw [Finset.sum_eq_zero, condensate_eq_zero (m := r) (by omega), mul_zero]
    intro m _
    rw [lossKraus, ite_eq_right, zero_mul]
    intro h
    have := mem_occSet.1 m.2
    rw [h, photons_add] at this
    exact hr this


/-- **Loss identity** (proof.md (2)): for a unit vector `u`,
`𝒩_η^{⊗n}(|u;L⟩⟨u;L|) = ∑ₖ C(L,k) ηᵏ (1-η)^{L-k} |u;k⟩⟨u;k|`. -/
theorem lossChannel_condensate {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (u : Fin n → ℂ)
    (hu : star u ⬝ᵥ u = 1) :
    lossChannel η (ketbra (condensate (L := L) u L)) =
      ∑ k ∈ range (L + 1), (binomPMF L η k : ℂ) • ketbra (condensate (L := L) u k) := by
  have hB : ∀ k, 0 ≤ binomPMF L η k := fun k =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hη0 _)) (pow_nonneg (sub_nonneg.2 hη1) _)
  have hA : ∀ ℓ : Occ n L, lossKraus η ℓ * ketbra (condensate (L := L) u L) * (lossKraus η ℓ)ᴴ =
      ∑ k ∈ range (L + 1), ((binomPMF L η k : ℂ) *
        (star (condensate (L := L) u (L - k) ℓ) * condensate (L := L) u (L - k) ℓ)) •
          ketbra (condensate (L := L) u k) := by
    intro ℓ
    have hs : photons (ℓ : Fin n → ℕ) ≤ L := mem_occSet.1 ℓ.2
    rw [ketbra, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec,
      lossKraus_mulVec_condensate hη0 hη1, star_smul, Matrix.smul_vecMulVec,
      Matrix.vecMulVec_smul, smul_smul]
    rw [Finset.sum_eq_single (L - photons (ℓ : Fin n → ℕ))]
    · rw [Nat.sub_sub_self hs, ketbra]
      congr 1
      have hsq : ((√(binomPMF L η (L - photons (ℓ : Fin n → ℕ))) : ℝ) : ℂ) *
          ((√(binomPMF L η (L - photons (ℓ : Fin n → ℕ))) : ℝ) : ℂ) =
          ((binomPMF L η (L - photons (ℓ : Fin n → ℕ)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hB _)]
      have hst : star ((√(binomPMF L η (L - photons (ℓ : Fin n → ℕ))) : ℝ) : ℂ) =
          ((√(binomPMF L η (L - photons (ℓ : Fin n → ℕ))) : ℝ) : ℂ) := Complex.conj_ofReal _
      rw [star_mul', hst]
      linear_combination (star (condensate (L := L) u (photons (ℓ : Fin n → ℕ)) ℓ) *
        condensate (L := L) u (photons (ℓ : Fin n → ℕ)) ℓ) * hsq
    · intro k hk hne
      rw [condensate_eq_zero (m := ℓ) (k := L - k) (by rw [Finset.mem_range] at hk; omega)]
      simp
    · intro h; rw [Finset.mem_range] at h; omega
  rw [lossChannel, Finset.sum_congr rfl fun ℓ _ => hA ℓ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hnorm : ∑ ℓ : Occ n L,
      star (condensate (L := L) u (L - k) ℓ) * condensate (L := L) u (L - k) ℓ = 1 := by
    have h := condensate_inner (L := L) u u (Nat.sub_le L k)
    rw [hu, one_pow] at h
    simpa [dotProduct] using h
  rw [← Finset.sum_smul, ← Finset.mul_sum, hnorm, mul_one]

end

end QIQCOP
