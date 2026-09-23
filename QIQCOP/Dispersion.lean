import QIQCOP.Defs

/-!
# The fixed-photon dispersion is strictly smaller than the thermal one

`V_occ / v(η N_S) = (1 - η) / (1 + η N_S) < 1` (proof.md, display after (T)).
-/

open Real

namespace QIQCOP

lemma gp_pos {x : ℝ} (hx : 0 < x) : 0 < gp x := by
  unfold gp
  apply Real.logb_pos (by norm_num)
  have : 0 < 1 / x := by positivity
  linarith

lemma vTh_eq {x : ℝ} (hx : 0 < x) : vTh x = x * (x + 1) * gp x ^ 2 := by
  unfold vTh gp
  congr 2
  rw [← Real.logb_div (by positivity) hx.ne']
  congr 1
  field_simp

/-- The ratio identity `V_occ = (1-η)/(1+η N_S) · v(η N_S)`. -/
theorem Vocc_eq_ratio_mul_vTh {η Ns : ℝ} (hη : 0 < η) (hNs : 0 < Ns) :
    Vocc η Ns = (1 - η) / (1 + η * Ns) * vTh (η * Ns) := by
  have hx : 0 < η * Ns := mul_pos hη hNs
  rw [vTh_eq hx, Vocc]
  field_simp
  ring

lemma Vocc_nonneg {η Ns : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns) : 0 ≤ Vocc η Ns := by
  unfold Vocc
  have : 0 < 1 - η := by linarith
  positivity

/-- **Strict dispersion gap**: `V_occ < v(η N_S)` for `0 < η < 1`, `N_S > 0`. -/
theorem Vocc_lt_vTh {η Ns : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns) :
    Vocc η Ns < vTh (η * Ns) := by
  have hx : 0 < η * Ns := mul_pos hη0 hNs
  have hv : 0 < vTh (η * Ns) := by
    rw [vTh_eq hx]; have := gp_pos hx; positivity
  rw [Vocc_eq_ratio_mul_vTh hη0 hNs]
  have hr : (1 - η) / (1 + η * Ns) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  nlinarith

end QIQCOP
