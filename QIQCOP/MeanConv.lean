import QIQCOP.StirlingWide

/-!
# Converse under a mean photon-number constraint

`mean_converse`: every code with mean photon number `≤ n N_S` and success `≥ 1 - ε` has
`log₂ M ≤ n g(x_ε) - √((1-κ) V_ε n ln n)` for large `n`, where `x_ε = η N_S/(1-ε)` and
`V_ε = (1-η) x_ε g'(x_ε)²`.
-/

open Real Filter Finset

namespace QIQCOP

theorem mean_converse {η Ns ε κ : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (L' M : ℕ) (C : Code n L' M), 1 ≤ M → C.meanPhotons ≤ n * Ns →
      1 - ε ≤ C.success η →
        Real.logb 2 M ≤ n * g (η * Ns / (1 - ε))
          - √((1 - κ) * ((1 - η) * (η * Ns / (1 - ε)) * gp (η * Ns / (1 - ε)) ^ 2) * n *
              Real.log n) := by
  obtain ⟨r₀, hr₀⟩ := binomGT_le_linear hη0 hη1 (κ := κ / 2) (by linarith) (by linarith)
  have he1 : 0 < 1 - ε := by linarith
  set e1 := 1 - ε with he1def
  set xe := η * Ns / e1 with hxe
  have hxe0 : 0 < xe := by positivity
  have hη' : 0 < 1 - η := by linarith
  set w := (1 - η) * xe with hw
  have hw0 : 0 < w := by positivity
  set G := gp xe with hG
  have hG0 : 0 < G := gp_pos hxe0
  set a := 1 - κ / 2 with ha
  set b := 1 - 3 * κ / 4 with hb
  set m := 1 - 5 * κ / 8 with hm
  set d := 1 - κ with hd
  set δ := κ / 16 with hδ
  have ha0 : 0 < a := by rw [ha]; linarith
  have hb0 : 0 < b := by rw [hb]; linarith
  have hm0 : 0 < m := by rw [hm]; linarith
  have hd0 : 0 < d := by rw [hd]; linarith
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : 0 < 1 - δ := by rw [hδ]; linarith
  have hmb : √b < √m := Real.sqrt_lt_sqrt hb0.le (by rw [hb, hm]; linarith)
  have hbd : √d < √b := Real.sqrt_lt_sqrt hd0.le (by rw [hb, hd]; linarith)
  have hsw : 0 < √w := Real.sqrt_pos.2 hw0
  have hma : m ≤ a * (1 - δ) ^ 2 := by
    have e : a * (1 - δ) ^ 2 - m = κ ^ 2 * (17 / 256 - κ / 512) := by
      rw [ha, hm, hδ]; ring
    have : 0 ≤ κ ^ 2 * (17 / 256 - κ / 512) := mul_nonneg (sq_nonneg κ) (by linarith)
    linarith
  set c := 2 / e1 with hc
  have hc0 : 0 < c := by positivity
  have hce : c * e1 = 2 := by rw [hc]; field_simp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx1 : 0 < (1 - δ) * xe := by positivity
  filter_upwards [MeanAsymp.sqrt_nlogn_le (√b * √w) (δ := δ * xe) (by positivity),
    MeanAsymp.ev_log_ge (-Real.log ((1 - δ) * xe) / δ),
    MeanAsymp.absorb (c * xe) 0 0 (δ := (√m - √b) * √w) (mul_pos (by linarith) hsw),
    SecondOrderLog.eventually_sqrt_ge c,
    MeanAsymp.absorb 0 (1 / Real.log 2) (2 + G) (δ := (√b - √d) * G * √w)
      (mul_pos (mul_pos (by linarith) hG0) hsw),
    eventually_ge_atTop ⌈((r₀ : ℝ) + 1) / ((1 - δ) * xe)⌉₊,
    MeanAsymp.ev_log_ge 1, eventually_ge_atTop 1] with n F1 F2 F3 F4 F5 F6 F7 F8
  intro L' M C hM hmean hs
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast F8
  have hn0 : (0 : ℝ) < n := by linarith
  set S := √((n : ℝ) * Real.log n) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set s := √(n : ℝ) with hs'
  have hs0 : 0 < s := Real.sqrt_pos.2 hn0
  have hss : s * s = n := Real.mul_self_sqrt hn0.le
  have hlog0 : 0 ≤ Real.log n := by linarith
  -- the threshold
  set y := (n : ℝ) * xe - √b * √w * S with hy
  have hy1 : (1 - δ) * xe * n ≤ y := by rw [hy]; linarith
  have hy2 : (r₀ : ℝ) + 1 ≤ (1 - δ) * xe * n := by
    have h := (Nat.ceil_le.1 F6)
    rw [div_le_iff₀ hx1] at h; linarith
  set r := ⌈y⌉₊ with hr
  have hry : y ≤ r := Nat.le_ceil y
  have hry' : (r : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith [Nat.cast_nonneg (α := ℝ) r₀])
  have hrr₀ : r₀ ≤ r := by
    have : (r₀ : ℝ) ≤ r := by linarith
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ r := by linarith [Nat.cast_nonneg (α := ℝ) r₀]
  have hrlow : (1 - δ) * xe * n ≤ r := by linarith
  have hlogr : (1 - δ) * Real.log n ≤ Real.log r := by
    have h1 : Real.log ((1 - δ) * xe * n) ≤ Real.log r :=
      Real.log_le_log (by positivity) hrlow
    rw [Real.log_mul hx1.ne' hn0.ne'] at h1
    rw [div_le_iff₀ hδ0] at F2
    linarith
  have hprod : m * w * (n * Real.log n) ≤ (a * Real.log r) * ((1 - η) * r) := by
    have h1 : a * ((1 - δ) * Real.log n) ≤ a * Real.log r :=
      mul_le_mul_of_nonneg_left hlogr ha0.le
    have h2 : (1 - η) * ((1 - δ) * xe * n) ≤ (1 - η) * r :=
      mul_le_mul_of_nonneg_left hrlow hη'.le
    have h3 := mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)
    have h4 : m * (w * (n * Real.log n)) ≤ a * (1 - δ) ^ 2 * (w * (n * Real.log n)) :=
      mul_le_mul_of_nonneg_right hma (by positivity)
    calc m * w * (n * Real.log n) = m * (w * (n * Real.log n)) := by ring
      _ ≤ a * (1 - δ) ^ 2 * (w * (n * Real.log n)) := h4
      _ = a * ((1 - δ) * Real.log n) * ((1 - η) * ((1 - δ) * xe * n)) := by rw [hw]; ring
      _ ≤ _ := h3
  have hsq : √m * √w * S ≤ √(a * Real.log r) * √((1 - η) * r) := by
    have e1' : √m * √w * S = √(m * w * (n * Real.log n)) := by
      rw [Real.sqrt_mul (mul_nonneg hm0.le hw0.le) (n * Real.log n), Real.sqrt_mul hm0.le w]
    rw [e1', ← Real.sqrt_mul (le_trans (by positivity) (mul_le_mul_of_nonneg_left hlogr ha0.le))]
    exact Real.sqrt_le_sqrt hprod
  set f := (r : ℝ) + √(a * Real.log r) * √((1 - η) * r) with hf
  have hfge : n * xe + c * xe * s ≤ f := by
    have : c * xe * s ≤ (√m - √b) * √w * S := by linarith
    rw [hf]; linarith
  have hf0 : 0 < f := lt_of_lt_of_le (by positivity) hfge
  set γ := 1 / s with hγ
  have hγ0 : 0 < γ := by positivity
  have hγs : γ * s = 1 := by rw [hγ]; field_simp
  have hγle : γ * c ≤ 1 := by
    rw [hγ, one_div, inv_mul_le_iff₀ hs0]; linarith
  have hγe : γ ≤ e1 / 2 := by
    have h1 : γ * c * e1 ≤ 1 * e1 := mul_le_mul_of_nonneg_right hγle he1.le
    have h2 : γ * c * e1 = 2 * γ := by rw [mul_assoc, hce]; ring
    linarith only [h1, h2]
  -- the thinned tail
  have hlam : (n : ℝ) * Ns / (f / η) ≤ e1 - γ := by
    rw [div_le_iff₀ (by positivity), mul_div_assoc', le_div_iff₀ hη0]
    have h1 : (e1 - γ) * (n * xe + c * xe * s) ≤ (e1 - γ) * f :=
      mul_le_mul_of_nonneg_left hfge (by linarith)
    have h2 : (e1 - γ) * (n * xe + c * xe * s) = xe * ((e1 - γ) * (s * s + c * s)) := by
      rw [hss]; ring
    have h3 : (e1 - γ) * (s * s + c * s) = e1 * (s * s) + (c * e1) * s - (γ * s) * s - (γ * s) * c := by
      ring
    have h4 : e1 * (s * s) ≤ (e1 - γ) * (s * s + c * s) := by
      rw [h3, hce, hγs]; linarith only [F4]
    have h5 : (n : ℝ) * Ns * η = xe * (e1 * (s * s)) := by
      rw [hss, hxe]; field_simp
    rw [h5]
    calc xe * (e1 * (s * s)) ≤ xe * ((e1 - γ) * (s * s + c * s)) :=
          mul_le_mul_of_nonneg_left h4 hxe0.le
      _ = _ := h2.symm
      _ ≤ _ := h1
  have hQ : ∑ ℓ ∈ range (L' + 1), C.law ℓ * binomGT ℓ η r ≤ e1 - γ := by
    calc ∑ ℓ ∈ range (L' + 1), C.law ℓ * binomGT ℓ η r
        ≤ ∑ ℓ ∈ range (L' + 1), C.law ℓ * ((ℓ : ℝ) / (f / η)) :=
          Finset.sum_le_sum fun ℓ _ =>
            mul_le_mul_of_nonneg_left (hr₀ r hrr₀ ℓ) (C.law_nonneg ℓ)
      _ = C.meanPhotons / (f / η) := by
          rw [C.meanPhotons_eq, Finset.sum_div]
          exact Finset.sum_congr rfl fun ℓ _ => by ring
      _ ≤ n * Ns / (f / η) := div_le_div_of_nonneg_right hmean (by positivity)
      _ ≤ e1 - γ := hlam
  have hth : ε + γ ≤ thinLT η C.law L' (r + 1) := by
    rw [C.sum_law_binomGT hM] at hQ; linarith
  have hconv := quantile_conv hη0.le hη1.le hM C r hs hγ0 hth
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hch : (0 : ℝ) < ((n + r).choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left r n)
  have h4γ : 4 / γ ^ 2 = 4 * n := by
    rw [hγ, one_div, inv_pow, sq, hss]; field_simp
  rw [h4γ] at hconv
  have hlogM : Real.logb 2 M ≤ 2 + Real.log n / Real.log 2 + Real.logb 2 ((n + r).choose r) := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hMr hconv
    rw [Real.logb_mul (by positivity) hch.ne', Real.logb_mul (by norm_num) hn0.ne'] at h
    have h2 : Real.logb 2 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]
      simp
    rw [h2] at h
    exact h
  have hup := logb_choose_le n r hxe0
  have hrG : ((r : ℝ) - n * xe) * G ≤ (1 - √b * √w * S) * G :=
    mul_le_mul_of_nonneg_right (by rw [hy] at hry'; linarith) hG0.le
  rw [MeanAsymp.sqrt_form hd0.le hw0.le hG0.le]
  have e5 : (1 / Real.log 2) * Real.log n = Real.log n / Real.log 2 := by ring
  rw [zero_mul, zero_add, e5] at F5
  linarith
end QIQCOP
