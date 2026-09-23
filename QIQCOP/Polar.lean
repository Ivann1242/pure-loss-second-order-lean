import QIQCOP.GramBound

/-!
# Isometric polar factor (square-root measurement vectors)

For `Ψ : D × ι` with `|ι| ≤ |D|` there is an isometry `W` (`Wᴴ W = 1`) with
`Wᴴ Ψ = √(Ψᴴ Ψ)`. The columns `φᵢ = W eᵢ` are orthonormal measurement vectors with
`⟨φᵢ, ψᵢ⟩ = (√G)ᵢᵢ`, i.e. the square-root measurement.

Proof: with `G = Ψᴴ Ψ = U diag(λ) Uᴴ`, the columns `yₐ` of `Y = Ψ U` are orthogonal with
`‖yₐ‖² = λₐ`. The normalized columns `λₐ^{-1/2} yₐ` (`λₐ ≠ 0`) extend to an orthonormal family
`(Fₐ)`, so `Fᴴ F = 1` and `F diag(√λ) = Y`; then `W = F Uᴴ` satisfies `W √G = Ψ`.
-/

open Matrix ComplexConjugate
open scoped ComplexOrder

namespace QIQCOP

theorem exists_isometry_polar {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
    [DecidableEq ι] (Ψ : Matrix D ι ℂ) (hcard : Fintype.card ι ≤ Fintype.card D) :
    ∃ W : Matrix D ι ℂ, Wᴴ * W = 1 ∧
      Wᴴ * Ψ = psdSqrt (isHermitian_conjTranspose_mul_self Ψ) := by
  classical
  set hH := isHermitian_conjTranspose_mul_self Ψ with hHdef
  have hPSD : (Ψᴴ * Ψ).PosSemidef := posSemidef_conjTranspose_mul_self Ψ
  set lam := hH.eigenvalues with hlam
  have hpos : ∀ i, 0 ≤ lam i := hPSD.eigenvalues_nonneg
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  have hU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self _
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  set Y : Matrix D ι ℂ := Ψ * U with hY
  have hYY : Yᴴ * Y = diagonal (fun i => (lam i : ℂ)) := by
    have hs := spectral_eq hH
    calc Yᴴ * Y = star U * (Ψᴴ * Ψ) * U := by
          simp only [Y, conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
      _ = star U * (U * diagonal (fun i => (lam i : ℂ)) * star U) * U := by rw [← hs]
      _ = (star U * U) * diagonal (fun i => (lam i : ℂ)) * (star U * U) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal (fun i => (lam i : ℂ)) := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  let y : ι → EuclideanSpace ℂ D := fun a => WithLp.toLp 2 (fun d => Y d a)
  have hinner : ∀ a b, inner ℂ (y a) (y b) = (Yᴴ * Y) a b := by
    intro a b
    simp only [y, PiLp.inner_apply, mul_apply, conjTranspose_apply,
      RCLike.inner_apply', RCLike.star_def]
  have hy0 : ∀ a, lam a = 0 → ∀ d, Y d a = 0 := by
    intro a ha d
    have h1 : inner ℂ (y a) (y a) = 0 := by
      rw [hinner, hYY, diagonal_apply_eq, ha, Complex.ofReal_zero]
    have h2 := inner_self_eq_zero.mp h1
    have := congrArg (fun z : EuclideanSpace ℂ D => z d) h2
    simpa [y] using this
  let c : ι → ℂ := fun a => (((√(lam a))⁻¹ : ℝ) : ℂ)
  let f : ι → EuclideanSpace ℂ D := fun a => c a • y a
  let κ := ι ⊕ Fin (Fintype.card D - Fintype.card ι)
  let v : κ → EuclideanSpace ℂ D := Sum.elim f 0
  let s : Set κ := Sum.inl '' {a | lam a ≠ 0}
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_, a, ha, rfl⟩ ⟨_, a', ha', rfl⟩
    by_cases h : a = a'
    · subst h
      rw [ite_eq_left rfl]
      simp only [Set.domRestrict_apply, v, Sum.elim_inl, f, inner_smul_left, inner_smul_right,
        hinner, hYY, diagonal_apply_eq]
      have hl : 0 < lam a := lt_of_le_of_ne (hpos a) (Ne.symm ha)
      simp only [c, Complex.conj_ofReal, ← Complex.ofReal_mul]
      rw [← Complex.ofReal_one]
      congr 1
      have hs : √(lam a) * √(lam a) = lam a := Real.mul_self_sqrt (hpos a)
      have hs0 : √(lam a) ≠ 0 := (Real.sqrt_pos.mpr hl).ne'
      field_simp
      linarith
    · rw [ite_eq_right (fun e => h (Sum.inl_injective (congrArg Subtype.val e)))]
      simp only [Set.domRestrict_apply, v, Sum.elim_inl, f, inner_smul_left, inner_smul_right,
        hinner, hYY, diagonal_apply_ne _ h, mul_zero]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [κ, finrank_euclideanSpace, Fintype.card_sum]; omega)
  let F : Matrix D ι ℂ := Matrix.of fun d a => b (Sum.inl a) d
  have hFF : Fᴴ * F = 1 := by
    ext a a'
    have h := orthonormal_iff_ite.mp b.orthonormal (Sum.inl a) (Sum.inl a')
    simp only [PiLp.inner_apply, RCLike.inner_apply'] at h
    simp only [F, mul_apply, conjTranspose_apply, of_apply, RCLike.star_def, h]
    by_cases haa : a = a'
    · subst haa; simp
    · rw [ite_eq_right (fun e => haa (Sum.inl_injective e)), one_apply_ne haa]
  have hFY : F * diagonal (fun a => ((√(lam a) : ℝ) : ℂ)) = Y := by
    ext d a
    rw [mul_diagonal]
    by_cases ha : lam a = 0
    · rw [hy0 a ha d, ha, Real.sqrt_zero, Complex.ofReal_zero, mul_zero]
    · have hmem : Sum.inl a ∈ s := ⟨a, ha, rfl⟩
      have hba := hb _ hmem
      have hl : 0 < lam a := lt_of_le_of_ne (hpos a) (Ne.symm ha)
      have hs0 : √(lam a) ≠ 0 := (Real.sqrt_pos.mpr hl).ne'
      simp only [F, of_apply, hba, v, Sum.elim_inl, f, c, PiLp.smul_apply, smul_eq_mul, y]
      rw [mul_comm, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0,
        Complex.ofReal_one, one_mul]
  have hWP : (F * star U) * psdSqrt hH = Ψ := by
    unfold psdSqrt
    calc F * star U * (U * diagonal (fun i => ((√(hH.eigenvalues i) : ℝ) : ℂ)) * star U)
        = F * (star U * U) * diagonal (fun i => ((√(lam i) : ℝ) : ℂ)) * star U := by
          simp only [Matrix.mul_assoc]; rfl
      _ = Y * star U := by rw [hU, Matrix.mul_one, hFY]
      _ = Ψ := by rw [hY, Matrix.mul_assoc, hU', Matrix.mul_one]
  have hWW : (F * star U)ᴴ * (F * star U) = 1 := by
    rw [conjTranspose_mul, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
    calc U * Fᴴ * (F * Uᴴ) = U * (Fᴴ * F) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hFF, Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hU']
  refine ⟨F * star U, hWW, ?_⟩
  calc (F * star U)ᴴ * Ψ = (F * star U)ᴴ * ((F * star U) * psdSqrt hH) := by rw [hWP]
    _ = psdSqrt hH := by rw [← Matrix.mul_assoc, hWW, Matrix.one_mul]

end QIQCOP
