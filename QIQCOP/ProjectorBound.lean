import QIQCOP.GramBound

/-!
# Projector bound

For states `σ i`, a POVM `Λ i` and an orthogonal projector `P`,
`(1/M) ∑ Tr[Λᵢ σᵢ] ≤ (√(Tr P / M) + √((1/M) ∑ Tr[(1-P) σᵢ]))²`.

The proof avoids matrix square roots: it uses positivity of
`u ↦ Tr[Λ (uP - P') σ (uP - P')ᴴ]` (summed over `i`) and the discriminant criterion.
-/

open Finset Matrix
open scoped ComplexOrder

namespace QIQCOP

section
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The trace of a product of two positive semidefinite matrices is nonnegative. -/
lemma trace_mul_nonneg_of_posSemidef {A B : Matrix D D ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  set U : Matrix D D ℂ := (hA.isHermitian.eigenvectorUnitary : Matrix D D ℂ) with hU
  have hspec := spectral_eq hA.isHermitian
  rw [← hU] at hspec
  have hN : (Uᴴ * B * U).PosSemidef := hB.conjTranspose_mul_mul_same U
  have h : (A * B).trace
      = ∑ i, (hA.isHermitian.eigenvalues i : ℂ) * (Uᴴ * B * U) i i := by
    conv_lhs => rw [hspec]
    rw [star_eq_conjTranspose, mul_assoc, mul_assoc, trace_mul_comm, mul_assoc]
    simp [trace, diagonal_mul]
  rw [h]
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ hN.diag_nonneg
  exact_mod_cast hA.eigenvalues_nonneg i

lemma re_trace_mul_nonneg {A B : Matrix D D ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ ((A * B).trace).re :=
  (Complex.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef hA hB)).1

/-- A positive semidefinite matrix of trace one satisfies `σ ≤ 1`. -/
lemma one_sub_posSemidef_of_trace_one {σ : Matrix D D ℂ} (hσ : σ.PosSemidef)
    (hσt : σ.trace = 1) : (1 - σ).PosSemidef := by
  set U : Matrix D D ℂ := (hσ.isHermitian.eigenvectorUnitary : Matrix D D ℂ) with hU
  have hUU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self _
  have hUU' : U * star U = 1 := mul_eq_one_comm.mp hUU
  have hspec := spectral_eq hσ.isHermitian
  rw [← hU] at hspec
  have hsum : ∑ i, hσ.isHermitian.eigenvalues i = 1 := by
    have h1 : σ.trace = ∑ i, (hσ.isHermitian.eigenvalues i : ℂ) := by
      conv_lhs => rw [hspec]
      exact trace_conj hUU _
    rw [hσt] at h1
    have h2 := congrArg Complex.re h1
    simp only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] at h2
    exact h2.symm
  have hle : ∀ i, hσ.isHermitian.eigenvalues i ≤ 1 := fun i => by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hσ.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hrw : 1 - σ = U * diagonal (fun i => ((1 - hσ.isHermitian.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have hd : diagonal (fun i => ((1 - hσ.isHermitian.eigenvalues i : ℝ) : ℂ)) =
        (1 : Matrix D D ℂ) - diagonal (fun i => (hσ.isHermitian.eigenvalues i : ℂ)) := by
      rw [← diagonal_one, diagonal_sub]
      congr 1
      funext i
      simp
    rw [hd, mul_sub, sub_mul, mul_one, ← star_eq_conjTranspose, hUU', ← hspec]
  rw [hrw]
  refine PosSemidef.mul_mul_conjTranspose_same (PosSemidef.diagonal ?_) U
  intro i
  simp only [Pi.zero_apply]
  exact_mod_cast sub_nonneg.mpr (hle i)

/-- Key positivity: quadratic in the real parameter `u`. -/
lemma quad_nonneg {Λ σ P : Matrix D D ℂ} (hΛ : Λ.PosSemidef) (hσ : σ.PosSemidef)
    (hPh : P.IsHermitian) (u : ℝ) :
    0 ≤ ((Λ * P * σ * P).trace).re * (u * u)
      + -(((Λ * σ).trace).re - ((Λ * P * σ * P).trace).re
          - ((Λ * (1 - P) * σ * (1 - P)).trace).re) * u
      + ((Λ * (1 - P) * σ * (1 - P)).trace).re := by
  set P' : Matrix D D ℂ := 1 - P with hP'
  have hP'h : P'ᴴ = P' := by
    rw [hP', conjTranspose_sub, conjTranspose_one, hPh.eq]
  set X : Matrix D D ℂ := (u : ℂ) • P - P' with hX
  have hXh : Xᴴ = X := by
    rw [hX, conjTranspose_sub, conjTranspose_smul, hP'h, hPh.eq]
    simp
  have h0 : 0 ≤ ((Λ * (X * σ * Xᴴ)).trace).re :=
    re_trace_mul_nonneg hΛ (hσ.mul_mul_conjTranspose_same X)
  rw [hXh] at h0
  have hs : (Λ * σ).trace = (Λ * P * σ * P).trace + (Λ * P * σ * P').trace
      + (Λ * P' * σ * P).trace + (Λ * P' * σ * P').trace := by
    have h1 : Λ * σ = Λ * (P + P') * σ * (P + P') := by
      rw [hP', add_sub_cancel, mul_one, mul_one]
    rw [h1]
    simp only [mul_add, add_mul, trace_add]
    ring
  have hx : (Λ * (X * σ * X)).trace = (u : ℂ) * (u : ℂ) * (Λ * P * σ * P).trace
      - (u : ℂ) * ((Λ * P * σ * P').trace + (Λ * P' * σ * P).trace)
      + (Λ * P' * σ * P').trace := by
    rw [hX]
    simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, trace_sub, trace_smul,
      smul_eq_mul, ← mul_assoc]
    ring
  have hs' := congrArg Complex.re hs
  have hx' := congrArg Complex.re hx
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero] at hs' hx'
  rw [hx'] at h0
  rw [hs']
  nlinarith [h0]

end

/-- Projector bound: success ≤ (√(D/M) + √q)². -/
theorem projector_bound {D : Type*} [Fintype D] [DecidableEq D] {M : ℕ} (hM : 0 < M)
    (σ Λ : Fin M → Matrix D D ℂ)
    (hσ : ∀ i, (σ i).PosSemidef) (hσt : ∀ i, (σ i).trace = 1)
    (hΛ : ∀ i, (Λ i).PosSemidef) (hΛs : ∑ i, Λ i = 1)
    (P : Matrix D D ℂ) (hPh : P.IsHermitian) (hPi : P * P = P) :
    (∑ i, ((Λ i * σ i).trace).re) / M ≤
      (Real.sqrt ((P.trace).re / M) +
        Real.sqrt ((∑ i, (((1 - P) * σ i).trace).re) / M)) ^ 2 := by
  obtain ⟨P', hP'⟩ : ∃ P' : Matrix D D ℂ, P' = 1 - P := ⟨_, rfl⟩
  rw [← hP']
  have hP'h : P'ᴴ = P' := by
    rw [hP', conjTranspose_sub, conjTranspose_one, hPh.eq]
  have hP'i : P' * P' = P' := by
    rw [hP']
    simp [sub_mul, mul_sub, hPi]
  obtain ⟨a, ha⟩ : ∃ a : Fin M → ℝ, ∀ i, a i = ((Λ i * P * σ i * P).trace).re :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin M → ℝ, ∀ i, b i = ((Λ i * P' * σ i * P').trace).re :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : Fin M → ℝ, ∀ i, s i = ((Λ i * σ i).trace).re :=
    ⟨_, fun _ => rfl⟩
  simp only [← hs]
  -- nonnegativity
  have ha0 : ∀ i, 0 ≤ a i := fun i => by
    have h := re_trace_mul_nonneg (hΛ i) ((hσ i).mul_mul_conjTranspose_same P)
    rw [hPh.eq] at h
    rw [ha i]
    simpa only [mul_assoc] using h
  have hb0 : ∀ i, 0 ≤ b i := fun i => by
    have h := re_trace_mul_nonneg (hΛ i) ((hσ i).mul_mul_conjTranspose_same P')
    rw [hP'h] at h
    rw [hb i]
    simpa only [mul_assoc] using h
  -- upper bounds
  have ha1 : ∀ i, a i ≤ ((Λ i * P).trace).re := fun i => by
    have hN : (P * Λ i * P).PosSemidef := by
      have h := (hΛ i).mul_mul_conjTranspose_same P
      rwa [hPh.eq] at h
    have h := re_trace_mul_nonneg hN (one_sub_posSemidef_of_trace_one (hσ i) (hσt i))
    rw [mul_sub, mul_one, trace_sub, Complex.sub_re] at h
    have e1 : (P * Λ i * P * σ i).trace = (Λ i * P * σ i * P).trace := by
      rw [mul_assoc, mul_assoc, trace_mul_comm]
      simp only [mul_assoc]
    have e2 : (P * Λ i * P).trace = (Λ i * P).trace := by
      rw [mul_assoc, trace_mul_comm, mul_assoc, hPi]
    rw [e1, e2] at h
    rw [ha i]
    linarith
  have hΛle : ∀ i, (1 - Λ i).PosSemidef := fun i => by
    have h : 1 - Λ i = ∑ j ∈ univ.erase i, Λ j := by
      rw [← hΛs, ← Finset.add_sum_erase univ Λ (Finset.mem_univ i)]
      abel
    rw [h]
    exact posSemidef_sum _ fun j _ => hΛ j
  have hb1 : ∀ i, b i ≤ ((P' * σ i).trace).re := fun i => by
    have hN : (P' * σ i * P').PosSemidef := by
      have h := (hσ i).mul_mul_conjTranspose_same P'
      rwa [hP'h] at h
    have h := re_trace_mul_nonneg (hΛle i) hN
    rw [sub_mul, one_mul, trace_sub, Complex.sub_re] at h
    have e1 : (Λ i * (P' * σ i * P')).trace = (Λ i * P' * σ i * P').trace := by
      simp only [mul_assoc]
    have e2 : (P' * σ i * P').trace = (P' * σ i).trace := by
      rw [trace_mul_comm, ← mul_assoc, hP'i]
    rw [e1, e2] at h
    rw [hb i]
    linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ i, a i := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ i, b i := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i, s i := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (P.trace).re := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∑ i, ((P' * σ i).trace).re := ⟨_, rfl⟩
  rw [← hS, ← hT, ← hQ]
  have hA0 : 0 ≤ A := hA ▸ Finset.sum_nonneg fun i _ => ha0 i
  have hB0 : 0 ≤ B := hB ▸ Finset.sum_nonneg fun i _ => hb0 i
  have hAT : A ≤ T := by
    have h1 : A ≤ ∑ i, ((Λ i * P).trace).re := hA ▸ Finset.sum_le_sum fun i _ => ha1 i
    have h2 : ∑ i, ((Λ i * P).trace).re = T := by
      rw [hT, ← Complex.re_sum, ← trace_sum, ← Finset.sum_mul, hΛs, one_mul]
    rwa [h2] at h1
  have hBQ : B ≤ Q := by rw [hB, hQ]; exact Finset.sum_le_sum fun i _ => hb1 i
  -- quadratic positivity summed over i
  have hquad : ∀ u : ℝ, 0 ≤ A * (u * u) + -(S - A - B) * u + B := by
    intro u
    have h : 0 ≤ ∑ i, (a i * (u * u) + -(s i - a i - b i) * u + b i) :=
      Finset.sum_nonneg fun i _ => by
        have h := quad_nonneg (hΛ i) (hσ i) hPh u
        rw [← hP', ← ha i, ← hb i, ← hs i] at h
        exact h
    have e : ∑ i, (a i * (u * u) + -(s i - a i - b i) * u + b i)
        = A * (u * u) + -(S - A - B) * u + B := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_neg_distrib,
        Finset.sum_sub_distrib, hA, hB, hS]
    rwa [e] at h
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  have hcross : S - A - B ≤ 2 * (Real.sqrt A * Real.sqrt B) := by
    have hnn : 0 ≤ 2 * (Real.sqrt A * Real.sqrt B) := by positivity
    have hsq : (S - A - B) ^ 2 ≤ (2 * (Real.sqrt A * Real.sqrt B)) ^ 2 := by
      have e : (2 * (Real.sqrt A * Real.sqrt B)) ^ 2 = 4 * A * B := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
        ring
      rw [e]
      nlinarith [hdisc]
    exact (abs_le_of_sq_le_sq' hsq hnn).2
  have hSle : S ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by
    have e : (Real.sqrt A + Real.sqrt B) ^ 2 = A + B + 2 * (Real.sqrt A * Real.sqrt B) := by
      rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
      ring
    rw [e]
    linarith
  have hSle' : S ≤ (Real.sqrt T + Real.sqrt Q) ^ 2 := by
    refine hSle.trans ?_
    have h1 := Real.sqrt_le_sqrt hAT
    have h2 := Real.sqrt_le_sqrt hBQ
    have h3 := Real.sqrt_nonneg A
    have h4 := Real.sqrt_nonneg B
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hfin : (Real.sqrt (T / M) + Real.sqrt (Q / M)) ^ 2
      = (Real.sqrt T + Real.sqrt Q) ^ 2 / M := by
    rw [Real.sqrt_div' T hMpos.le, Real.sqrt_div' Q hMpos.le, ← add_div, div_pow,
      Real.sq_sqrt hMpos.le]
  rw [hfin]
  exact div_le_div_of_nonneg_right hSle' hMpos.le

end QIQCOP

