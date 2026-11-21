import QIQCOP.Binomial
import QIQCOP.BE.StirlingBounds

/-!
# Local limit expansion of `log binomPMF`

For `x = k - ηL` with `|x| ≤ min(η, 1-η)/2 · L`,
`log binomPMF L η k = -log(2π L η(1-η))/2 - x²/(2 L η(1-η)) + O(1/L + |x|/L + |x|³/L²)`.
-/

open Real
open scoped Nat

namespace QIQCOP.BE

lemma abs_log_one_add_le {u : ℝ} (hu : |u| ≤ 1 / 2) : |log (1 + u)| ≤ 2 * |u| := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg]; linarith) 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, sub_neg_eq_add, abs_neg,
    pow_one] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [abs_nonneg u]

lemma abs_log_one_add_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |log (1 + u) - (u - u ^ 2 / 2)| ≤ 2 * |u| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    sub_neg_eq_add, abs_neg, Nat.cast_zero, Nat.cast_one] at h
  have e : (-u) ^ 1 / 1 + (-u) ^ (1 + 1) / (1 + 1) + log (1 + u) =
      log (1 + u) - (u - u ^ 2 / 2) := by ring
  rw [e] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ |u| ^ 3 := by positivity
  have e2 : |u| ^ (2 + 1) = |u| ^ 3 := by norm_num
  rw [e2]
  nlinarith [abs_nonneg u]

lemma abs_psi_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |(1 + u) * log (1 + u) - u - u ^ 2 / 2| ≤ 4 * |u| ^ 3 := by
  have h := abs_log_one_add_sub_le hu
  set r := log (1 + u) - (u - u ^ 2 / 2) with hr
  have e : (1 + u) * log (1 + u) - u - u ^ 2 / 2 = -(u ^ 3 / 2) + (1 + u) * r := by
    rw [hr]; ring
  rw [e]
  have h1 : |-(u ^ 3 / 2)| = |u| ^ 3 / 2 := by
    rw [abs_neg, abs_div, abs_pow]; norm_num
  have h2 : |(1 + u) * r| ≤ 3 / 2 * (2 * |u| ^ 3) := by
    rw [abs_mul]
    have : |1 + u| ≤ 3 / 2 := by
      rw [abs_le] at hu ⊢; constructor <;> linarith
    exact mul_le_mul this h (abs_nonneg _) (by norm_num)
  have h3 := abs_add_le (-(u ^ 3 / 2)) ((1 + u) * r)
  have : 0 ≤ |u| ^ 3 := by positivity
  linarith

theorem log_binomPMF_approx {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) {L k : ℕ} (hL : 1 ≤ L)
    (hx : |(k : ℝ) - η * L| ≤ min η (1 - η) / 2 * L) :
    |log (binomPMF L η k) - (-(log (2 * π * (L * (η * (1 - η)))) / 2)
        - ((k : ℝ) - η * L) ^ 2 / (2 * (L * (η * (1 - η)))))| ≤
      (1 / (6 * η) + 1 / (6 * (1 - η)) + 1 / 12) / L
        + |(k : ℝ) - η * L| / (L * (η * (1 - η)))
        + 4 * |(k : ℝ) - η * L| ^ 3 / (L : ℝ) ^ 2 * (1 / η ^ 2 + 1 / (1 - η) ^ 2) := by
  have hη' : 0 < 1 - η := by linarith
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set x : ℝ := (k : ℝ) - η * L with hxdef
  set a : ℝ := η * L with ha
  set b : ℝ := (1 - η) * L with hb
  have ha0 : 0 < a := mul_pos hη0 hLr
  have hb0 : 0 < b := mul_pos hη' hLr
  have hxa : |x| ≤ a / 2 := by
    refine hx.trans ?_
    have := min_le_left η (1 - η)
    rw [ha]; nlinarith
  have hxb : |x| ≤ b / 2 := by
    refine hx.trans ?_
    have := min_le_right η (1 - η)
    rw [hb]; nlinarith
  have hkx : (k : ℝ) = a + x := by rw [hxdef]; ring
  have hk0 : a / 2 ≤ (k : ℝ) := by rw [hkx]; linarith [neg_abs_le x]
  have hkpos : (0 : ℝ) < k := by linarith
  have hkL' : (k : ℝ) < L := by
    have : (L : ℝ) = a + b := by rw [ha, hb]; ring
    rw [hkx, this]; linarith [le_abs_self x]
  have hkL : k ≤ L := by exact_mod_cast hkL'.le
  have hk_ne : k ≠ 0 := by rintro rfl; simp at hkpos
  have hM_ne : L - k ≠ 0 := by
    have : k < L := by exact_mod_cast hkL'
    omega
  have hL_ne : L ≠ 0 := by omega
  set M : ℝ := ((L - k : ℕ) : ℝ) with hMdef
  have hMx : M = b - x := by
    rw [hMdef, Nat.cast_sub hkL, hkx, hb, ha]; ring
  have hM0 : b / 2 ≤ M := by rw [hMx]; linarith [le_abs_self x]
  have hMpos : 0 < M := by linarith
  set u : ℝ := x / a with hu
  set v : ℝ := x / b with hv
  have hau : a * u = x := by rw [hu]; field_simp
  have hbv : b * v = x := by rw [hv]; field_simp
  have hu2 : |u| ≤ 1 / 2 := by
    rw [hu, abs_div, abs_of_pos ha0, div_le_iff₀ ha0]; linarith
  have hv2 : |v| ≤ 1 / 2 := by
    rw [hv, abs_div, abs_of_pos hb0, div_le_iff₀ hb0]; linarith
  have hv2' : |-v| ≤ 1 / 2 := by rwa [abs_neg]
  have h1u : 0 < 1 + u := by linarith [neg_abs_le u]
  have h1v : 0 < 1 + -v := by linarith [le_abs_self v]
  -- logs
  set lL := log (L : ℝ) with hlL
  set le := log η with hle
  set le' := log (1 - η) with hle'
  set l1 := log (1 + u) with hl1
  set l2 := log (1 + -v) with hl2
  set lp := log (2 * π) with hlp
  have hlogk : log (k : ℝ) = le + lL + l1 := by
    have : (k : ℝ) = η * L * (1 + u) := by rw [hkx, ← hau, ha]; ring
    rw [this, log_mul (by positivity) h1u.ne', log_mul hη0.ne' hLr.ne']
  have hlogM : log M = le' + lL + l2 := by
    have : M = (1 - η) * L * (1 + -v) := by rw [hMx, ← hbv, hb]; ring
    rw [this, log_mul (by positivity) h1v.ne', log_mul hη'.ne' hLr.ne']
  have h2p : (0 : ℝ) < 2 * π := by positivity
  -- Stirling
  have sL1 := log_factorial_ge hL_ne
  have sL2 := log_factorial_le hL_ne
  have sk1 := log_factorial_ge hk_ne
  have sk2 := log_factorial_le hk_ne
  have sM1 := log_factorial_ge hM_ne
  have sM2 := log_factorial_le hM_ne
  rw [log_mul h2p.ne' hLr.ne'] at sL1 sL2
  rw [log_mul h2p.ne' hkpos.ne', hlogk] at sk1 sk2
  rw [← hMdef, log_mul h2p.ne' hMpos.ne', hlogM] at sM1 sM2
  rw [← hlp, ← hlL] at sL1 sL2
  rw [← hlp] at sk1 sk2 sM1 sM2
  set fL := log (L ! : ℝ) with hfL
  set fk := log (k ! : ℝ) with hfk
  set fM := log ((L - k)! : ℝ) with hfM
  -- log of pmf
  have hchoose : log (L.choose k : ℝ) = fL - fk - fM := by
    have h := Nat.choose_mul_factorial_mul_factorial hkL
    have hR : (L.choose k : ℝ) * (k ! : ℝ) * ((L - k)! : ℝ) = (L ! : ℝ) := by
      exact_mod_cast h
    have hc : (0 : ℝ) < L.choose k := by exact_mod_cast Nat.choose_pos hkL
    have h1 : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have h2 : (0 : ℝ) < ((L - k)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [hfL, ← hR, log_mul (by positivity) h2.ne', log_mul hc.ne' h1.ne']
    ring
  have hlogp : log (binomPMF L η k) = fL - fk - fM + k * le + M * le' := by
    have hc : (0 : ℝ) < L.choose k := by exact_mod_cast Nat.choose_pos hkL
    unfold binomPMF
    rw [log_mul (by positivity) (by positivity), log_mul hc.ne' (by positivity), log_pow,
      log_pow, hchoose]
  have hT : log (2 * π * (L * (η * (1 - η)))) = lp + lL + le + le' := by
    rw [log_mul h2p.ne' (by positivity), log_mul hLr.ne' (by positivity),
      log_mul hη0.ne' hη'.ne']
    ring
  have hq : (L : ℝ) * (η * (1 - η)) ≠ 0 := by positivity
  have hx2 : x ^ 2 / (2 * (L * (η * (1 - η)))) = a * u ^ 2 / 2 + b * v ^ 2 / 2 := by
    rw [hu, hv, ha, hb]; field_simp; ring
  set θL := fL - ((L : ℝ) * lL - L + (lp + lL) / 2) with hθL
  set θk := fk - ((k : ℝ) * (le + lL + l1) - k + (lp + (le + lL + l1)) / 2) with hθk
  set θM := fM - (M * (le' + lL + l2) - M + (lp + (le' + lL + l2)) / 2) with hθM
  set Ψ1 := (1 + u) * l1 - u - u ^ 2 / 2 with hΨ1
  set Ψ2 := (1 + -v) * l2 - -v - (-v) ^ 2 / 2 with hΨ2
  have hMk : M = L - k := by rw [hMdef, Nat.cast_sub hkL]
  have key : log (binomPMF L η k) - (-(log (2 * π * (L * (η * (1 - η)))) / 2)
        - x ^ 2 / (2 * (L * (η * (1 - η))))) =
      θL - θk - θM - (l1 + l2) / 2 - a * Ψ1 - b * Ψ2 := by
    rw [hlogp, hT, hx2, hθL, hθk, hθM, hΨ1, hΨ2, hMk, hkx]
    have hLab : (L : ℝ) = a + b := by rw [ha, hb]; ring
    rw [hLab]
    linear_combination (l1 - 1) * hau + (1 - l2) * hbv
  rw [key]
  -- bounds
  have b1 : |θL - θk - θM| ≤ (1 / (6 * η) + 1 / (6 * (1 - η)) + 1 / 12) / L := by
    have t1 : 0 ≤ θL := by rw [hθL]; linarith
    have t2 : θL ≤ 1 / (12 * L) := by rw [hθL]; linarith
    have t3 : 0 ≤ θk := by rw [hθk]; linarith
    have t4 : θk ≤ 1 / (12 * k) := by rw [hθk]; linarith
    have t5 : 0 ≤ θM := by rw [hθM]; linarith
    have t6 : θM ≤ 1 / (12 * M) := by rw [hθM]; linarith
    have t7 : (1 : ℝ) / (12 * k) ≤ 1 / (6 * η) / L := by
      rw [div_div, mul_assoc, ← ha]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have t8 : (1 : ℝ) / (12 * M) ≤ 1 / (6 * (1 - η)) / L := by
      rw [div_div, mul_assoc, ← hb]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have t9 : (1 : ℝ) / (12 * L) = 1 / 12 / L := by rw [div_div]
    have e : (1 / (6 * η) + 1 / (6 * (1 - η)) + 1 / 12) / L =
        1 / (6 * η) / L + 1 / (6 * (1 - η)) / L + 1 / 12 / L := by ring
    have p1 : (0 : ℝ) ≤ 1 / (6 * η) / L := by positivity
    have p2 : (0 : ℝ) ≤ 1 / (6 * (1 - η)) / L := by positivity
    rw [e, abs_le]; constructor <;> linarith
  have b2 : |(l1 + l2) / 2| ≤ |x| / (L * (η * (1 - η))) := by
    have h1 := abs_log_one_add_le hu2
    have h2 := abs_log_one_add_le hv2'
    rw [abs_neg] at h2
    have h3 := abs_add_le l1 l2
    have e : |x| / (L * (η * (1 - η))) = |u| + |v| := by
      rw [hu, hv, abs_div, abs_div, abs_of_pos ha0, abs_of_pos hb0, ha, hb]
      field_simp; ring
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have b3 : |a * Ψ1 + b * Ψ2| ≤
      4 * |x| ^ 3 / (L : ℝ) ^ 2 * (1 / η ^ 2 + 1 / (1 - η) ^ 2) := by
    have h1 := abs_psi_le hu2
    have h2 := abs_psi_le hv2'
    rw [abs_neg] at h2
    have h3 := abs_add_le (a * Ψ1) (b * Ψ2)
    rw [abs_mul a Ψ1, abs_mul b Ψ2, abs_of_pos ha0, abs_of_pos hb0] at h3
    have e : 4 * |x| ^ 3 / (L : ℝ) ^ 2 * (1 / η ^ 2 + 1 / (1 - η) ^ 2) =
        a * (4 * |u| ^ 3) + b * (4 * |v| ^ 3) := by
      rw [hu, hv, abs_div, abs_div, abs_of_pos ha0, abs_of_pos hb0, ha, hb]
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left h1 ha0.le
    have := mul_le_mul_of_nonneg_left h2 hb0.le
    linarith
  have e : θL - θk - θM - (l1 + l2) / 2 - a * Ψ1 - b * Ψ2 =
      (θL - θk - θM) + -((l1 + l2) / 2) + -(a * Ψ1 + b * Ψ2) := by ring
  rw [e]
  have c1 := abs_add_le ((θL - θk - θM) + -((l1 + l2) / 2)) (-(a * Ψ1 + b * Ψ2))
  have c2 := abs_add_le (θL - θk - θM) (-((l1 + l2) / 2))
  rw [abs_neg] at c1 c2
  linarith

end QIQCOP.BE
