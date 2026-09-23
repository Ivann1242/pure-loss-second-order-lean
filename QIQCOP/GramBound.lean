import QIQCOP.Defs

/-!
# Square-root-measurement Gram-matrix estimate (proof.md, Eq. (4))

For pure states `ψ₁,…,ψ_M` with Gram matrix `G` (so `G ⪰ 0`, `G i i = 1`), the square-root
measurement has error `1 - (1/M) ∑ᵢ ((√G)ᵢᵢ)²`. We prove the linear-algebra inequality

  `M - ∑ᵢ ((√G)ᵢᵢ)² ≤ ∑_{i,j} |G i j|² - M  ( = ∑_{i≠j} |G i j|² )`,

which after dividing by `M` is Eq. (4). The square root is the spectral one,
`√G = U diag(√λ) U*`, and we check `√G * √G = G` and that its diagonal is real.
-/

open Matrix ComplexConjugate
open scoped ComplexOrder

namespace QIQCOP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

/-- Spectral square root `U diag(√λ) U*` of a Hermitian matrix. -/
def psdSqrt {G : Matrix ι ι ℂ} (hG : G.IsHermitian) : Matrix ι ι ℂ :=
  (hG.eigenvectorUnitary : Matrix ι ι ℂ) *
    diagonal (fun i => ((√(hG.eigenvalues i) : ℝ) : ℂ)) *
    star (hG.eigenvectorUnitary : Matrix ι ι ℂ)

lemma conj_mul_conj {U : Matrix ι ι ℂ} (hU : star U * U = 1) (d e : ι → ℂ) :
    U * diagonal d * star U * (U * diagonal e * star U) = U * diagonal (d * e) * star U := by
  calc U * diagonal d * star U * (U * diagonal e * star U)
      = U * diagonal d * (star U * U) * diagonal e * star U := by simp only [mul_assoc]
    _ = U * diagonal (d * e) * star U := by
      rw [hU, mul_one, mul_assoc U, diagonal_mul_diagonal]; rfl

lemma trace_conj {U : Matrix ι ι ℂ} (hU : star U * U = 1) (d : ι → ℂ) :
    trace (U * diagonal d * star U) = ∑ i, d i := by
  rw [trace_mul_comm, ← mul_assoc, hU, one_mul, trace_diagonal]

lemma spectral_eq {G : Matrix ι ι ℂ} (hG : G.IsHermitian) :
    G = (hG.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun i => (hG.eigenvalues i : ℂ)) *
      star (hG.eigenvectorUnitary : Matrix ι ι ℂ) := by
  conv_lhs => rw [hG.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

lemma psdSqrt_mul_self {G : Matrix ι ι ℂ} (hG : G.PosSemidef) :
    psdSqrt hG.isHermitian * psdSqrt hG.isHermitian = G := by
  unfold psdSqrt
  rw [conj_mul_conj (Matrix.UnitaryGroup.star_mul_self _)]
  conv_rhs => rw [spectral_eq hG.isHermitian]
  congr 2
  congr 1
  funext i
  simp only [Pi.mul_apply]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hG.eigenvalues_nonneg i)]

lemma psdSqrt_diag_im {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (i : ι) :
    (psdSqrt hG i i).im = 0 := by
  unfold psdSqrt
  simp only [mul_apply, diagonal, of_apply, star_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro k _
  simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Gram-matrix estimate** behind Eq. (4). -/
theorem srm_gram_bound (G : Matrix ι ι ℂ) (hG : G.PosSemidef) (hdiag : ∀ i, G i i = 1) :
    (Fintype.card ι : ℝ) - ∑ i, ((psdSqrt hG.isHermitian) i i).re ^ 2 ≤
      (∑ i, ∑ j, ‖G i j‖ ^ 2) - Fintype.card ι := by
  set hH := hG.isHermitian
  set lam := hH.eigenvalues with hlam
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self _
  have hpos : ∀ i, 0 ≤ lam i := hG.eigenvalues_nonneg
  -- ∑ (√G)ᵢᵢ = ∑ √λ
  have h1 : ∑ i, ((psdSqrt hH) i i).re = ∑ i, √(lam i) := by
    have : trace (psdSqrt hH) = ∑ i, ((√(lam i) : ℝ) : ℂ) := trace_conj hU _
    have h := congrArg Complex.re this
    rw [Complex.re_sum] at h
    simpa [trace, Complex.re_sum] using h
  -- ∑ λ = M
  have h2 : ∑ i, lam i = Fintype.card ι := by
    have h := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    simp only [trace, diag, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Complex.re_sum, Complex.natCast_re] at h
    exact h.symm
  -- ∑ |Gᵢⱼ|² = ∑ λ²
  have h3 : ∑ i, ∑ j, ‖G i j‖ ^ 2 = ∑ i, lam i ^ 2 := by
    have hsq : trace (G * G) = ∑ i, ((lam i ^ 2 : ℝ) : ℂ) := by
      rw [spectral_eq hH, conj_mul_conj hU, trace_conj hU]
      simp [sq]
      rfl
    have hent : trace (G * G) = ∑ i, ∑ j, ((‖G i j‖ ^ 2 : ℝ) : ℂ) := by
      simp only [trace, diag, mul_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have : G j i = conj (G i j) := by
        rw [← hH.apply j i]; rfl
      rw [this, RCLike.mul_conj]
      push_cast; rfl
    have h := congrArg Complex.re (hent.symm.trans hsq)
    simp only [Complex.re_sum, Complex.ofReal_re] at h
    exact h
  -- pointwise inequalities
  have hA : ∀ i, 1 - ((psdSqrt hH) i i).re ^ 2 ≤ 2 - 2 * ((psdSqrt hH) i i).re := fun i => by
    nlinarith [sq_nonneg (1 - ((psdSqrt hH) i i).re)]
  have hB : ∀ i, 3 * lam i - 2 * √(lam i) - lam i ^ 2 ≤ 0 := fun i => by
    have hs := Real.sq_sqrt (hpos i)
    have hs0 := Real.sqrt_nonneg (lam i)
    set s := √(lam i)
    rw [← hs]
    nlinarith [mul_nonneg (mul_nonneg hs0 (sq_nonneg (s - 1))) (by linarith : (0:ℝ) ≤ s + 2)]
  have sA := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hA i)
  have sB := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hB i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum] at sA sB
  rw [h3]
  nlinarith [h1, h2]

end

end QIQCOP
