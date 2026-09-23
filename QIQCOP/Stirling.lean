import QIQCOP.Defs

/-!
# Stirling expansion of `log₂ C(n+k-1, k)` (proof.md, Eq. (7))

For `x = η N_S > 0` and any window radius `R`, uniformly over integers `k` with
`|k - n x| ≤ R √n`,

  `log₂ C(n+k-1, k) ≥ n g(x) + (k - n x) g'(x) - B log n`

for all large `n`.
-/

open Real Filter
open scoped Nat

namespace QIQCOP

lemma log_factorial_le_aux (m : ℕ) :
    Real.log (m ! : ℝ) ≤ m * Real.log m - m + (1/2) * Real.log m + 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have h1 := Stirling.log_stirlingSeq'_antitone (Nat.zero_le j)
  simp only [Function.comp_apply, Nat.succ_eq_add_one, zero_add, Stirling.stirlingSeq_one] at h1
  rw [Stirling.log_stirlingSeq_formula] at h1
  have hm : (0:ℝ) < (j+1 : ℕ) := by positivity
  rw [Real.log_div (exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_sqrt (by norm_num),
    Real.log_mul (by norm_num) hm.ne', Real.log_div hm.ne' (exp_pos 1).ne', Real.log_exp] at h1
  linarith

lemma log_factorial_ge_aux (m : ℕ) :
    m * Real.log m - m ≤ Real.log (m ! : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h := Stirling.le_log_factorial_stirling hm.ne'
  have h1 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have h2 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  linarith

lemma taylor_aux {a b x : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hx : 0 < x) :
    (a + b) * Real.log (1 + x) - b * Real.log x - (b - a * x) ^ 2 / (a * x) ≤
      (a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b := by
  have hab : 0 < a + b := by linarith
  have h1 : 1 - (a * (1 + x)) / (a + b) ≤ Real.log (a + b) - Real.log a - Real.log (1 + x) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (a + b) / (a * (1 + x))) (by positivity)
    rw [Real.log_div hab.ne' (by positivity), Real.log_mul ha.ne' (by positivity), inv_div] at this
    linarith
  have h1' : (a + b) * (1 - a * (1 + x) / (a + b)) = b - a * x := by field_simp; ring
  have h1'' := mul_le_mul_of_nonneg_left h1 hab.le
  rw [h1'] at h1''
  have h2 : b * (Real.log b - Real.log a - Real.log x) ≤ b * (b / (a * x) - 1) := by
    rcases hb.eq_or_lt with rfl | hb'
    · simp
    have := Real.log_le_sub_one_of_pos (x := b / (a * x)) (by positivity)
    rw [Real.log_div hb'.ne' (by positivity), Real.log_mul ha.ne' hx.ne'] at this
    exact mul_le_mul_of_nonneg_left (by linarith) hb
  have h3 : b * (b / (a * x) - 1) = (b - a * x) + (b - a * x) ^ 2 / (a * x) := by
    field_simp; ring
  nlinarith

lemma log_choose_ge_aux (n k : ℕ) :
    ((n : ℝ) + k) * Real.log ((n : ℝ) + k) - n * Real.log n - k * Real.log k
      - (1/2) * Real.log n - (1/2) * Real.log k - 2 ≤ Real.log ((n + k).choose k : ℝ) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial n k
  have hR : ((n + k).choose k : ℝ) * (n ! : ℝ) * (k ! : ℝ) = ((n + k)! : ℝ) := by
    exact_mod_cast h
  have hc : (0 : ℝ) < ((n + k).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left k n)
  have hl : Real.log ((n + k).choose k : ℝ) + Real.log (n ! : ℝ) + Real.log (k ! : ℝ)
      = Real.log ((n + k)! : ℝ) := by
    rw [← hR, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have e1 := log_factorial_ge_aux (n + k)
  have e2 := log_factorial_le_aux n
  have e3 := log_factorial_le_aux k
  push_cast at e1
  linarith

lemma sectorDim_mul (n k : ℕ) (hn : 0 < n) :
    sectorDim n k * ((n : ℝ) + k) = ((n + k).choose k : ℝ) * n := by
  have h := Nat.choose_mul_succ_eq (n + k - 1) k
  have e1 : n + k - 1 + 1 = n + k := by omega
  have e2 : n + k - k = n := by omega
  rw [e1, e2] at h
  unfold sectorDim
  exact_mod_cast h

theorem stirlingExpansion {η Ns : ℝ} (hx : 0 < η * Ns) : StirlingExpansion η Ns := by
  intro R
  set x := η * Ns with hxdef
  set C : ℝ := x + |R| + 1 with hCdef
  have hC1 : 1 ≤ C := by have := abs_nonneg R; linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC1
  have hlogC1 : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith)
  set K : ℝ := R ^ 2 / x + (1/2) * Real.log C + 2 + Real.log (1 + C) with hKdef
  have hK : 0 ≤ K := by have : 0 ≤ R ^ 2 / x := by positivity
                        linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(1 + K) / Real.log 2, by positivity, eventually_atTop.2 ⟨3, fun n hn k hk => ?_⟩⟩
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnpos' : 0 < n := by omega
  have hlogn : 1 ≤ Real.log n := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  -- window facts
  have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hnpos.le
  have hsq1 : 1 ≤ √(n : ℝ) := by
    rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsqn : √(n : ℝ) ≤ n := by nlinarith
  have hRs : 0 ≤ R * √(n : ℝ) := le_trans (abs_nonneg _) hk
  have hRabs : R * √(n : ℝ) ≤ |R| * n := by
    calc R * √(n : ℝ) ≤ |R| * √(n : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self R) (Real.sqrt_nonneg _)
      _ ≤ |R| * n := mul_le_mul_of_nonneg_left hsqn (abs_nonneg R)
  have hkC : (k : ℝ) ≤ C * n := by
    have := (abs_le.1 hk).2
    have : 0 ≤ (n : ℝ) := hnpos.le
    nlinarith
  have hsq2 : ((k : ℝ) - n * x) ^ 2 ≤ R ^ 2 * n := by
    have := pow_le_pow_left₀ (abs_nonneg _) hk 2
    rw [sq_abs, mul_pow, Real.sq_sqrt hnpos.le] at this
    exact this
  have hquad : ((k : ℝ) - n * x) ^ 2 / (n * x) ≤ R ^ 2 / x := by
    rw [div_le_div_iff₀ (by positivity) hx]
    nlinarith
  have hlogk : Real.log k ≤ Real.log C + Real.log n := by
    rcases (Nat.cast_nonneg (α := ℝ) k).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]
      linarith
    · rw [← Real.log_mul (by linarith) hnpos.ne']
      exact Real.log_le_log h0 hkC
  have hlognk : Real.log ((n : ℝ) + k) ≤ Real.log (1 + C) + Real.log n := by
    rw [← Real.log_mul (by linarith) hnpos.ne']
    exact Real.log_le_log (by linarith) (by nlinarith)
  -- log of sector dimension
  have hD := sectorDim_mul n k hnpos'
  have hc : (0 : ℝ) < ((n + k).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left k n)
  have hDpos : 0 < sectorDim n k := by
    have : 0 < sectorDim n k * ((n : ℝ) + k) := by rw [hD]; positivity
    exact pos_of_mul_pos_left this (by linarith)
  have hlogD : Real.log (sectorDim n k) + Real.log ((n : ℝ) + k) =
      Real.log ((n + k).choose k : ℝ) + Real.log n := by
    rw [← Real.log_mul hDpos.ne' (by linarith), ← Real.log_mul hc.ne' hnpos.ne', hD]
  have hT := taylor_aux hnpos hk0 hx
  have hS := log_choose_ge_aux n k
  have hmain : ((n : ℝ) + k) * Real.log (1 + x) - k * Real.log x - (1 + K) * Real.log n ≤
      Real.log (sectorDim n k) := by
    nlinarith
  -- convert to base 2
  have hgp : Real.log (1 + 1 / x) = Real.log (x + 1) - Real.log x := by
    rw [show 1 + 1 / x = (x + 1) / x by field_simp, Real.log_div (by linarith) hx.ne']
  unfold g gp
  simp only [Real.logb]
  rw [hgp]
  have hlhs : (n : ℝ) * ((x + 1) * (Real.log (x + 1) / Real.log 2) - x * (Real.log x / Real.log 2)) +
      ((k : ℝ) - n * x) * ((Real.log (x + 1) - Real.log x) / Real.log 2) -
      (1 + K) / Real.log 2 * Real.log n =
      (((n : ℝ) + k) * Real.log (1 + x) - k * Real.log x - (1 + K) * Real.log n) / Real.log 2 := by
    rw [add_comm 1 x]
    field_simp
    ring
  rw [hlhs]
  exact div_le_div_of_nonneg_right hmain hlog2.le

end QIQCOP
