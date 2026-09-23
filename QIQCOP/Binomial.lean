import QIQCOP.Defs

/-!
# Elementary facts about the binomial distribution, and a Chebyshev quantile bound

`binomPMF L η k = C(L,k) η^k (1-η)^(L-k)` and `binomLT L η t = Pr{K < t}` for `K ~ Bin(L, η)`.
-/

open Real Finset

namespace QIQCOP

lemma binomPMF_nonneg {L : ℕ} {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (k : ℕ) :
    0 ≤ binomPMF L η k := by
  unfold binomPMF
  have : 0 ≤ 1 - η := by linarith
  positivity

lemma sum_binomPMF (L : ℕ) (η : ℝ) : ∑ k ∈ range (L + 1), binomPMF L η k = 1 := by
  have h := (add_pow η (1 - η) L).symm
  simp only [add_sub_cancel, one_pow] at h
  rw [← h]
  refine sum_congr rfl fun k _ => ?_
  unfold binomPMF; ring

/-- `Pr{K < t} + Pr{t ≤ K ≤ L} = 1`. -/
lemma binomLT_add_tail (L : ℕ) (η : ℝ) {t : ℕ} (ht : t ≤ L + 1) :
    binomLT L η t + ∑ k ∈ Ico t (L + 1), binomPMF L η k = 1 := by
  unfold binomLT
  rw [Finset.sum_range_add_sum_Ico _ ht, sum_binomPMF]

/-- Variance of the binomial distribution: `∑ₖ Pr{K = k} (k - η L)² = L η (1-η)`. -/
lemma binom_variance (L : ℕ) (η : ℝ) :
    ∑ k ∈ range (L + 1), binomPMF L η k * ((k : ℝ) - η * L) ^ 2 = L * (η * (1 - η)) := by
  have hv := congrArg (Polynomial.eval η) (bernsteinPolynomial.variance ℝ L)
  simp only [Polynomial.eval_finsetSum, bernsteinPolynomial, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_natCast, Polynomial.eval_one, nsmul_eq_mul] at hv
  rw [show (L : ℝ) * (η * (1 - η)) = L * η * (1 - η) by ring, ← hv]
  refine sum_congr rfl fun k _ => ?_
  unfold binomPMF; ring

/-- **Chebyshev**: `Pr{K < η L - s √(L η (1-η))} ≤ 1/s²`, written with the integer threshold
`t = ⌈η L - s √(L η (1-η))⌉₊` (for integer `K`, `K < t ↔ K < η L - s √(…)`). -/
theorem binomLT_chebyshev {L : ℕ} {η s : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hs : 0 < s)
    (hL : 1 ≤ L) :
    binomLT L η ⌈η * L - s * √(L * (η * (1 - η)))⌉₊ ≤ 1 / s ^ 2 := by
  have hvar := binom_variance L η
  set a := η * (1 - η) with ha_def
  have ha : 0 < a := mul_pos hη0 (by linarith)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hLa : 0 < (L : ℝ) * a := mul_pos hLpos ha
  set y := η * L - s * √(L * a) with hy
  set t := ⌈y⌉₊ with ht
  have hsq2 : √(L * a) ^ 2 = L * a := Real.sq_sqrt hLa.le
  have h0 : 0 ≤ s * √(L * a) := by positivity
  have hD : 0 < s ^ 2 * (L * a) := by positivity
  have htL : t ≤ L + 1 := by
    have : t ≤ L := by
      rw [ht, Nat.ceil_le]
      nlinarith
    omega
  unfold binomLT
  calc ∑ j ∈ range t, binomPMF L η j
      ≤ ∑ j ∈ range t, binomPMF L η j * ((j : ℝ) - η * L) ^ 2 / (s ^ 2 * (L * a)) := by
        refine sum_le_sum fun j hj => ?_
        have hj' : (j : ℝ) < y := by
          rw [mem_range, ht, Nat.lt_ceil] at hj; exact hj
        have hp := binomPMF_nonneg (L := L) hη0.le hη1.le j
        rw [le_div_iff₀ hD]
        have h1 : s * √(L * a) ≤ η * L - j := by linarith
        have h2 : s ^ 2 * (L * a) ≤ ((j : ℝ) - η * L) ^ 2 := by
          have : s ^ 2 * (L * a) = (s * √(L * a)) ^ 2 := by rw [mul_pow, hsq2]
          rw [this]
          nlinarith
        exact mul_le_mul_of_nonneg_left h2 hp
    _ ≤ ∑ j ∈ range (L + 1), binomPMF L η j * ((j : ℝ) - η * L) ^ 2 / (s ^ 2 * (L * a)) := by
        apply sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr htL)
        intro j _ _
        have hp := binomPMF_nonneg (L := L) hη0.le hη1.le j
        positivity
    _ = 1 / s ^ 2 := by
        rw [← sum_div, hvar]
        field_simp

end QIQCOP
