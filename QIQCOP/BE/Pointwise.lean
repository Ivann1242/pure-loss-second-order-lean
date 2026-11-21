import QIQCOP.BE.LocalLimit
import QIQCOP.BE.GaussianCell

/-!
# Pointwise comparison of the binomial pmf with the Gaussian density

With `h = 1/√(Lη(1-η))` and `x = k - ηL`:
* inside the window `|x| ≤ min(η,1-η)/2·L`, `|x|³ ≤ L²`:
  `|binomPMF L η k - h·phi(xh)| ≤ C h²/(1+|xh|)²`;
* outside the window `|x|³ ≥ c³L²`: `h·phi(xh) ≤ C h²/(1+|xh|)²`.
-/

open Real

namespace QIQCOP.BE

lemma abs_exp_sub_one_le' (d : ℝ) : |exp d - 1| ≤ |d| * exp |d| := by
  rcases le_total 0 d with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by linarith [one_le_exp h])]
    have h1 := add_one_le_exp (-d)
    have h2 : exp d * exp (-d) = 1 := by rw [← exp_add]; simp
    nlinarith [exp_pos d]
  · rw [abs_of_nonpos h, abs_of_nonpos (by linarith [exp_le_one_iff.2 h])]
    have h1 := add_one_le_exp d
    have h2 : 1 ≤ exp (-d) := one_le_exp (by linarith)
    nlinarith

/-- Constant bounding the log-error inside the window. -/
noncomputable def cD (η : ℝ) : ℝ :=
  (1 / (6 * η) + 1 / (6 * (1 - η)) + 1 / 12) + 1 / (η * (1 - η))
    + 4 * (1 / η ^ 2 + 1 / (1 - η) ^ 2)

/-- Window constant. -/
noncomputable def cWin (η : ℝ) : ℝ := 1536 * (cD η * exp (cD η))

lemma cD_pos {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) : 0 < cD η := by
  have : 0 < 1 - η := by linarith
  unfold cD; positivity

theorem binomPMF_sub_le {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) {L k : ℕ} (hL : 1 ≤ L) {h : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hh : h ^ 2 * (L * (η * (1 - η))) = 1)
    (hx : |(k : ℝ) - η * L| ≤ min η (1 - η) / 2 * L)
    (hx3 : |(k : ℝ) - η * L| ^ 3 ≤ (L : ℝ) ^ 2) :
    |binomPMF L η k - h * phi (((k : ℝ) - η * L) * h)| ≤
      cWin η * h ^ 2 / (1 + |((k : ℝ) - η * L) * h|) ^ 2 := by
  have hη' : 0 < 1 - η := by linarith
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have happ := log_binomPMF_approx hη0 hη1 hL hx
  set x : ℝ := (k : ℝ) - η * L with hxdef
  set q : ℝ := η * (1 - η) with hq
  have hq0 : 0 < q := mul_pos hη0 hη'
  have hq1 : q ≤ 1 := by rw [hq]; nlinarith
  set z : ℝ := x * h with hz
  have hzabs : |z| = |x| * h := by rw [hz, abs_mul, abs_of_pos hh0]
  set A1 : ℝ := 1 / (6 * η) + 1 / (6 * (1 - η)) + 1 / 12 with hA1
  set A3 : ℝ := 1 / η ^ 2 + 1 / (1 - η) ^ 2 with hA3
  have hA1p : 0 < A1 := by rw [hA1]; positivity
  have hA3p : 0 < A3 := by rw [hA3]; positivity
  have hcD : cD η = A1 + 1 / q + 4 * A3 := rfl
  set T : ℝ := -(log (2 * π * (L * q)) / 2) - x ^ 2 / (2 * (L * q)) with hT
  set D : ℝ := A1 / L + |x| / (L * q) + 4 * |x| ^ 3 / (L : ℝ) ^ 2 * A3 with hD
  clear_value D T A1 A3 z q x
  -- the window implies `k ≤ L`, hence positivity of the pmf
  have hxL : |x| ≤ L := by
    refine hx.trans ?_
    have := min_le_left η (1 - η)
    nlinarith
  have hkL : k ≤ L := by
    have h1 : |x| ≤ (1 - η) / 2 * L := by
      refine hx.trans ?_
      have := min_le_right η (1 - η)
      nlinarith
    have h2 : (k : ℝ) = η * L + x := by rw [hxdef]; ring
    have h3 : (k : ℝ) ≤ L := by
      rw [h2]; nlinarith [le_abs_self x]
    exact_mod_cast h3
  have hp : 0 < binomPMF L η k := by
    unfold binomPMF
    have : (0 : ℝ) < L.choose k := by exact_mod_cast Nat.choose_pos hkL
    positivity
  -- `h * phi z = exp T`
  have hσ : √((L : ℝ) * q) = h⁻¹ := by
    have : (L : ℝ) * q = (h⁻¹) ^ 2 := by
      field_simp; linarith
    rw [this, Real.sqrt_sq (by positivity)]
  have hexpT : h * phi z = exp T := by
    have h2p : (0 : ℝ) < 2 * π := by positivity
    have hY : (0 : ℝ) < 2 * π * (L * q) := by positivity
    have e1 : exp (-(log (2 * π * (L * q)) / 2)) = h / √(2 * π) := by
      rw [← Real.log_sqrt hY.le, exp_neg, exp_log (Real.sqrt_pos.2 hY),
        Real.sqrt_mul h2p.le, hσ]
      field_simp
    have e2 : x ^ 2 / (2 * (L * q)) = z ^ 2 / 2 := by
      rw [hz]; field_simp; linear_combination (-(x ^ 2)) * hh
    rw [hT, sub_eq_add_neg, exp_add, e1, e2, phi]
    ring_nf
  -- error bounds
  have hD0 : D ≤ cD η := by
    rw [hcD, hD]
    have t1 : A1 / L ≤ A1 := div_le_self hA1p.le hLr
    have t2 : |x| / (L * q) ≤ 1 / q := by
      rw [div_le_div_iff₀ (by positivity) hq0, one_mul]
      exact mul_le_mul_of_nonneg_right hxL hq0.le
    have t3 : 4 * |x| ^ 3 / (L : ℝ) ^ 2 * A3 ≤ 4 * A3 := by
      have : |x| ^ 3 / (L : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; exact hx3
      have e : 4 * |x| ^ 3 / (L : ℝ) ^ 2 * A3 = 4 * A3 * (|x| ^ 3 / (L : ℝ) ^ 2) := by ring
      rw [e]
      exact mul_le_of_le_one_right (by positivity) this
    linarith
  have hDz : D = A1 * q * h ^ 2 + |z| * h + 4 * A3 * q ^ 2 * |z| ^ 3 * h := by
    have hLq : (L : ℝ) = 1 / (h ^ 2 * q) := by
      field_simp; linear_combination hh
    rw [hD, hzabs, hLq]
    field_simp
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hDh : D ≤ cD η * h * (1 + |z|) ^ 3 := by
    rw [hDz, hcD]
    have c1 : (1 : ℝ) ≤ (1 + |z|) ^ 3 := one_le_pow₀ (by linarith)
    have c2 : |z| ≤ (1 + |z|) ^ 3 :=
      (by linarith : |z| ≤ 1 + |z|).trans (le_self_pow₀ (by linarith) (by norm_num))
    have c3 : |z| ^ 3 ≤ (1 + |z|) ^ 3 := pow_le_pow_left₀ hz0 (by linarith) 3
    have d1 : A1 * q * h ^ 2 ≤ A1 * h * (1 + |z|) ^ 3 := by
      have hqh : q * h ≤ 1 := (mul_le_mul hq1 hh1 hh0.le zero_le_one).trans (by norm_num)
      calc A1 * q * h ^ 2 = A1 * h * (q * h) := by ring
        _ ≤ A1 * h * (1 + |z|) ^ 3 :=
          mul_le_mul_of_nonneg_left (hqh.trans c1) (by positivity)
    have d2 : |z| * h ≤ 1 / q * h * (1 + |z|) ^ 3 := by
      have hq' : 1 ≤ 1 / q := by rw [le_div_iff₀ hq0]; linarith
      calc |z| * h ≤ (1 + |z|) ^ 3 * h := mul_le_mul_of_nonneg_right c2 hh0.le
        _ = 1 * (h * (1 + |z|) ^ 3) := by ring
        _ ≤ 1 / q * (h * (1 + |z|) ^ 3) := mul_le_mul_of_nonneg_right hq' (by positivity)
        _ = 1 / q * h * (1 + |z|) ^ 3 := by ring
    have d3 : 4 * A3 * q ^ 2 * |z| ^ 3 * h ≤ 4 * A3 * h * (1 + |z|) ^ 3 := by
      have : q ^ 2 ≤ 1 := pow_le_one₀ hq0.le hq1
      have e : 4 * A3 * q ^ 2 * |z| ^ 3 * h = 4 * A3 * h * (q ^ 2 * |z| ^ 3) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc q ^ 2 * |z| ^ 3 ≤ 1 * |z| ^ 3 := by gcongr
        _ ≤ (1 + |z|) ^ 3 := by rw [one_mul]; exact c3
    have e : (A1 + 1 / q + 4 * A3) * h * (1 + |z|) ^ 3 = A1 * h * (1 + |z|) ^ 3
        + 1 / q * h * (1 + |z|) ^ 3 + 4 * A3 * h * (1 + |z|) ^ 3 := by ring
    rw [e]
    linarith
  set δ : ℝ := log (binomPMF L η k) - T with hδ
  have hδD : |δ| ≤ D := happ
  have hpexp : binomPMF L η k = exp T * exp δ := by
    rw [← exp_add, hδ, add_sub_cancel, exp_log hp]
  have hD_nonneg : 0 ≤ D := (abs_nonneg _).trans hδD
  rw [hexpT, hpexp, show exp T * exp δ - exp T = exp T * (exp δ - 1) by ring, abs_mul,
    abs_of_pos (exp_pos T), ← hexpT]
  have s1 : |exp δ - 1| ≤ cD η * h * (1 + |z|) ^ 3 * exp (cD η) := by
    refine (abs_exp_sub_one_le' δ).trans ?_
    exact mul_le_mul (hδD.trans hDh) (exp_le_exp.2 (hδD.trans hD0)) (exp_pos _).le
      (hD_nonneg.trans hDh)
  have s2 : h * phi z ≤ h * (1536 / (1 + |z|) ^ 5) :=
    mul_le_mul_of_nonneg_left (phi_le z) hh0.le
  have s3 := mul_le_mul s2 s1 (abs_nonneg _) (by positivity)
  refine s3.trans (le_of_eq ?_)
  rw [cWin]
  field_simp

/-- Outside the window the Gaussian density itself is negligible. -/
theorem phi_outside_le {η c x h : ℝ} {L : ℕ} (hη0 : 0 < η) (hη1 : η < 1) (hc : 0 < c)
    (hh0 : 0 < h) (hh : h ^ 2 * (L * (η * (1 - η))) = 1)
    (hx3 : c ^ 3 * (L : ℝ) ^ 2 ≤ |x| ^ 3) :
    h * phi (x * h) ≤ 1536 / c ^ 3 * h ^ 2 / (1 + |x * h|) ^ 2 := by
  have hη' : 0 < 1 - η := by linarith
  set q : ℝ := η * (1 - η) with hq
  have hq0 : 0 < q := mul_pos hη0 hη'
  have hq1 : q ≤ 1 := by rw [hq]; nlinarith
  set z : ℝ := x * h with hz
  have hzabs : |z| = |x| * h := by rw [hz, abs_mul, abs_of_pos hh0]
  have hz0 : 0 ≤ |z| := abs_nonneg z
  -- `c³ ≤ h |z|³`
  have hkey : c ^ 3 ≤ h * |z| ^ 3 := by
    have e : h * |z| ^ 3 = h ^ 4 * |x| ^ 3 := by rw [hzabs]; ring
    have e2 : h ^ 4 * (L : ℝ) ^ 2 * q ^ 2 = 1 := by
      have : h ^ 4 * (L : ℝ) ^ 2 * q ^ 2 = (h ^ 2 * (L * q)) ^ 2 := by ring
      rw [this, hh]; norm_num
    have e3 : c ^ 3 ≤ h ^ 4 * (c ^ 3 * (L : ℝ) ^ 2) := by
      have hq2 : q ^ 2 ≤ 1 := pow_le_one₀ hq0.le hq1
      have hpos : 0 ≤ c ^ 3 * (h ^ 4 * (L : ℝ) ^ 2) := by positivity
      nlinarith
    rw [e]
    exact e3.trans (mul_le_mul_of_nonneg_left hx3 (by positivity))
  have hzpos : 0 < |z| ^ 3 := by
    have : 0 < c ^ 3 := by positivity
    nlinarith
  have s1 : phi z ≤ 1536 / ((1 + |z|) ^ 2 * |z| ^ 3) := by
    refine (phi_le z).trans ?_
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    have : |z| ^ 3 ≤ (1 + |z|) ^ 3 := pow_le_pow_left₀ hz0 (by linarith) 3
    calc (1 + |z|) ^ 2 * |z| ^ 3 ≤ (1 + |z|) ^ 2 * (1 + |z|) ^ 3 := by gcongr
      _ = (1 + |z|) ^ 5 := by ring
  have s2 : (1536 : ℝ) / ((1 + |z|) ^ 2 * |z| ^ 3) ≤ 1536 / c ^ 3 * h / (1 + |z|) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ (1 + |z|) ^ 2 := by positivity
    have hc3 : 0 < c ^ 3 := by positivity
    have e : 1536 / c ^ 3 * h * ((1 + |z|) ^ 2 * |z| ^ 3) =
        1536 * (1 + |z|) ^ 2 * (h * |z| ^ 3 / c ^ 3) := by ring
    rw [e]
    have : 1 ≤ h * |z| ^ 3 / c ^ 3 := by rw [le_div_iff₀ hc3]; linarith
    nlinarith
  calc h * phi z ≤ h * (1536 / c ^ 3 * h / (1 + |z|) ^ 2) :=
        mul_le_mul_of_nonneg_left (s1.trans s2) hh0.le
    _ = 1536 / c ^ 3 * h ^ 2 / (1 + |z|) ^ 2 := by ring

end QIQCOP.BE
