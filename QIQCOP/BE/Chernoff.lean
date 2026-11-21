import QIQCOP.Binomial

/-!
# A Chernoff bound for the binomial distribution

`Pr{|K - ηL| ≥ a} ≤ 2 exp(λ² η(1-η) L - λ a)` for `0 ≤ λ ≤ 1`, proved directly from the
binomial theorem.
-/

open Real Finset

namespace QIQCOP.BE

lemma exp_le_quad {x : ℝ} (hx : |x| ≤ 1) : exp x ≤ 1 + x + x ^ 2 := by
  have := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hx)).2
  linarith

lemma bern_mgf_le {η lam : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hl : |lam| ≤ 1) :
    η * exp (lam * (1 - η)) + (1 - η) * exp (-(lam * η)) ≤ exp (lam ^ 2 * (η * (1 - η))) := by
  have hq : 0 ≤ 1 - η := by linarith
  have h1 : |lam * (1 - η)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hq]
    nlinarith [abs_nonneg lam]
  have h2 : |-(lam * η)| ≤ 1 := by
    rw [abs_neg, abs_mul, abs_of_nonneg hη0]
    nlinarith [abs_nonneg lam]
  have e1 := mul_le_mul_of_nonneg_left (exp_le_quad h1) hη0
  have e2 := mul_le_mul_of_nonneg_left (exp_le_quad h2) hq
  have e3 := add_one_le_exp (lam ^ 2 * (η * (1 - η)))
  nlinarith

lemma binom_mgf (L : ℕ) (η lam : ℝ) :
    ∑ k ∈ range (L + 1), binomPMF L η k * exp (lam * ((k : ℝ) - η * L)) =
      (η * exp (lam * (1 - η)) + (1 - η) * exp (-(lam * η))) ^ L := by
  rw [add_pow]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ L := by simpa [Nat.lt_succ_iff] using hk
  unfold binomPMF
  rw [mul_pow, mul_pow, ← exp_nat_mul, ← exp_nat_mul]
  have : exp (lam * ((k : ℝ) - η * L)) =
      exp (k * (lam * (1 - η))) * exp (((L - k : ℕ) : ℝ) * (-(lam * η))) := by
    rw [← exp_add, Nat.cast_sub hk']; congr 1; ring
  rw [this]; ring

theorem binom_tail_le {η lam : ℝ} (a : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (L : ℕ) :
    ∑ k ∈ (range (L + 1)).filter (fun k : ℕ => a ≤ |(k : ℝ) - η * L|), binomPMF L η k ≤
      2 * exp (lam ^ 2 * (η * (1 - η)) * L - lam * a) := by
  have hM : ∀ l : ℝ, |l| ≤ 1 →
      ∑ k ∈ range (L + 1), binomPMF L η k * exp (l * ((k : ℝ) - η * L)) ≤
        exp (l ^ 2 * (η * (1 - η)) * L) := by
    intro l hl
    rw [binom_mgf]
    calc _ ≤ (exp (l ^ 2 * (η * (1 - η)))) ^ L :=
          pow_le_pow_left₀ (by have : 0 ≤ 1 - η := by linarith
                               positivity) (bern_mgf_le hη0.le hη1.le hl) L
      _ = _ := by rw [← exp_nat_mul]; congr 1; ring
  have hp := fun k => binomPMF_nonneg (L := L) hη0.le hη1.le k
  calc ∑ k ∈ (range (L + 1)).filter (fun k : ℕ => a ≤ |(k : ℝ) - η * L|), binomPMF L η k
      ≤ ∑ k ∈ (range (L + 1)).filter (fun k : ℕ => a ≤ |(k : ℝ) - η * L|), binomPMF L η k *
          (exp (-(lam * a)) * exp (lam * ((k : ℝ) - η * L)) +
            exp (-(lam * a)) * exp (-lam * ((k : ℝ) - η * L))) := by
        refine sum_le_sum fun k hk => ?_
        have hk' := (mem_filter.1 hk).2
        refine le_mul_of_one_le_right (hp k) ?_
        rw [← exp_add, ← exp_add]
        rcases le_abs.1 hk' with h | h
        · have : (0 : ℝ) ≤ -(lam * a) + lam * ((k : ℝ) - η * L) := by nlinarith
          have := one_le_exp this
          have := exp_pos (-(lam * a) + -lam * ((k : ℝ) - η * L))
          linarith
        · have : (0 : ℝ) ≤ -(lam * a) + -lam * ((k : ℝ) - η * L) := by nlinarith
          have := one_le_exp this
          have := exp_pos (-(lam * a) + lam * ((k : ℝ) - η * L))
          linarith
    _ ≤ ∑ k ∈ range (L + 1), binomPMF L η k *
          (exp (-(lam * a)) * exp (lam * ((k : ℝ) - η * L)) +
            exp (-(lam * a)) * exp (-lam * ((k : ℝ) - η * L))) := by
        refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ => ?_
        have := hp k
        positivity
    _ = exp (-(lam * a)) * (∑ k ∈ range (L + 1), binomPMF L η k * exp (lam * ((k : ℝ) - η * L))
          + ∑ k ∈ range (L + 1), binomPMF L η k * exp (-lam * ((k : ℝ) - η * L))) := by
        rw [← sum_add_distrib, mul_sum]
        refine sum_congr rfl fun k _ => ?_
        ring
    _ ≤ exp (-(lam * a)) * (exp (lam ^ 2 * (η * (1 - η)) * L) +
          exp (lam ^ 2 * (η * (1 - η)) * L)) := by
        have h1 := hM lam (by rw [abs_of_nonneg hl0]; exact hl1)
        have h2 := hM (-lam) (by rw [abs_neg, abs_of_nonneg hl0]; exact hl1)
        rw [neg_sq] at h2
        gcongr
    _ = 2 * exp (lam ^ 2 * (η * (1 - η)) * L - lam * a) := by
        rw [show lam ^ 2 * (η * (1 - η)) * L - lam * a =
          -(lam * a) + lam ^ 2 * (η * (1 - η)) * L by ring, exp_add]; ring

end QIQCOP.BE
