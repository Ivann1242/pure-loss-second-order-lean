import QIQCOP.MeanMain
import QIQCOP.MajorantSharp

/-!
# Second-order asymptotics under a mean photon-number constraint, with `O(√n)` remainder

With `x = η N_S/(1-ε)` and `V = (1-η) x g'(x)²`:

* `mean_sharp_cutoff`: the converse core, stated without reference to codes.
* `mean_ach_sharp`, `mean_conv_sharp`: the two directions.
* `mean_second_order_sharp`: `log₂ M*(n, ε) = n g(x) - √(V n ln n) + O(√n)`.
-/

open Real Filter Finset

namespace QIQCOP

namespace MeanSharp

/-- `log n ≤ √n` for every natural `n ≥ 1`. -/
lemma log_le_sqrt {n : ℕ} (hn : 1 ≤ n) : Real.log n ≤ √(n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hu0 : 0 < √(√(n : ℝ)) := Real.sqrt_pos.2 hs0
  have h1 : Real.log (√(√(n : ℝ))) = Real.log n / 4 := by
    rw [Real.log_sqrt hs0.le, Real.log_sqrt hn0.le]; ring
  have h2 := Real.log_le_sub_one_of_pos hu0
  have h3 : √(√(n : ℝ)) ^ 2 = √(n : ℝ) := Real.sq_sqrt hs0.le
  rw [h1] at h2
  nlinarith [sq_nonneg (√(√(n : ℝ)) - 2)]

lemma sqrt_form' {w G n lg : ℝ} (hw : 0 ≤ w) (hG : 0 ≤ G) :
    √(w * G ^ 2 * n * lg) = G * (√w * √(n * lg)) := by
  rw [show w * G ^ 2 * n * lg = G ^ 2 * (w * (n * lg)) by ring,
    Real.sqrt_mul (sq_nonneg G), Real.sqrt_sq hG, Real.sqrt_mul hw]

lemma sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- The squared form of `√(W n L) - √n ≤ √(log r) √((1-η) r)`. -/
lemma core_sq {sw sn sL ρ x r b lr : ℝ} (hsw : 0 ≤ sw) (hsn : 0 ≤ sn) (hsL : 0 ≤ sL)
    (hρ : 0 ≤ ρ) (hW : ρ * x = sw ^ 2) (h1 : sn ^ 2 * x - sw * (sn * sL) ≤ r)
    (h2 : sL ^ 2 - b ≤ lr) (hb : 0 ≤ b) (hbL : b ≤ sL ^ 2) (h3 : ρ * sL ^ 2 ≤ sn)
    (h4 : b * sw ^ 2 + 1 ≤ sw * sL) (h5 : ρ * (sw * (sn * sL)) ≤ sw ^ 2 * sn ^ 2) :
    (sw * (sn * sL) - sn) ^ 2 ≤ lr * (ρ * r) := by
  have h6 : sw ^ 2 * sn ^ 2 - ρ * (sw * (sn * sL)) ≤ ρ * r := by
    have := mul_le_mul_of_nonneg_left h1 hρ
    have e : ρ * (sn ^ 2 * x - sw * (sn * sL)) =
        (ρ * x) * sn ^ 2 - ρ * (sw * (sn * sL)) := by ring
    rw [e, hW] at this; exact this
  have h7 := mul_le_mul h2 h6 (sub_nonneg.2 h5) (le_trans (sub_nonneg.2 hbL) h2)
  refine le_trans ?_ h7
  have h8 : ρ * sL ^ 2 * (sw * sn * sL) ≤ sn * (sw * sn * sL) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h9 : (b * sw ^ 2 + 1) * sn ^ 2 ≤ sw * sL * sn ^ 2 :=
    mul_le_mul_of_nonneg_right h4 (sq_nonneg sn)
  have h10 : 0 ≤ b * (ρ * (sw * (sn * sL))) := by positivity
  nlinarith only [h8, h9, h10]

end MeanSharp

open MeanSharp

set_option maxHeartbeats 1000000 in
-- the proof is a long chain of elementary estimates in one context
/-- **Converse core**, stated without reference to codes. -/
theorem mean_sharp_cutoff {η Ns ε : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop, ∃ (r : ℕ) (lam : ℝ), 0 < lam ∧
      (∀ ℓ : ℕ, binomGT ℓ η r ≤ (ℓ : ℝ) / lam) ∧
      (n : ℝ) * Ns / lam ≤ 1 - ε - 1 / √(n : ℝ) ∧
      Real.logb 2 (4 * n * ((n + r).choose r : ℝ)) ≤
        n * g (η * Ns / (1 - ε))
          - √(((1 - η) * (η * Ns / (1 - ε)) * gp (η * Ns / (1 - ε)) ^ 2) * n * Real.log n)
          + A * √(n : ℝ) := by
  obtain ⟨r₀, hr₀⟩ := binomGT_le_linear_sharp hη0 hη1
  have he1 : 0 < 1 - ε := by linarith
  set e1 := 1 - ε with he1def
  set xe := η * Ns / e1 with hxe
  have hxe0 : 0 < xe := by positivity
  have hη' : 0 < 1 - η := by linarith
  set w := (1 - η) * xe with hw
  have hw0 : 0 < w := by positivity
  set G := gp xe with hG
  have hG0 : 0 < G := gp_pos hxe0
  have hsw : 0 < √w := Real.sqrt_pos.2 hw0
  set c := 2 / e1 with hc
  have hc0 : 0 < c := by positivity
  have hce : c * e1 = 2 := by rw [hc]; field_simp
  set A₀ := 1 + √(2 * w) + c * xe with hA₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  set b := |Real.log (xe / 2)| with hb
  have hb0 : 0 ≤ b := abs_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 + 1 / Real.log 2 + A₀ * G + G, ?_⟩
  filter_upwards [MeanAsymp.sqrt_nlogn_le (√w) (δ := xe / 2) (by positivity),
    MeanAsymp.ev_log_ge b, MeanAsymp.ev_log_ge (((b * w + 1) / √w) ^ 2),
    SecondOrderLog.eventually_sqrt_ge c,
    SecondOrderLog.eventually_sqrt_ge ((A₀ + 1) / xe),
    eventually_ge_atTop ⌈2 * ((r₀ : ℝ) + 1) / xe⌉₊, eventually_ge_atTop 1]
    with n F2 F3 F4 F5 F6 F7 F1
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast F1
  have hn0 : (0 : ℝ) < n := by linarith
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg hnr
  have hLs := log_le_sqrt F1
  set T := √((n : ℝ) * Real.log n) with hT
  set s := √(n : ℝ) with hs'
  have hs0 : 0 < s := Real.sqrt_pos.2 hn0
  have hss : s * s = n := Real.mul_self_sqrt hn0.le
  have hs2 : s ^ 2 = n := by rw [sq]; exact hss
  have hs1 : 1 ≤ s := by
    rw [hs', show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hnr
  set sL := √(Real.log n) with hsL
  have hsL0 : 0 ≤ sL := Real.sqrt_nonneg _
  have hsL2 : sL ^ 2 = Real.log n := Real.sq_sqrt hL0
  have hTe : T = s * sL := Real.sqrt_mul hn0.le _
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hsw2 : √w ^ 2 = w := Real.sq_sqrt hw0.le
  -- the threshold
  set y := (n : ℝ) * xe - √w * T + A₀ * s with hy
  have hyhalf : xe / 2 * n ≤ y := by
    have : 0 ≤ A₀ * s := by positivity
    rw [hy]; linarith
  have hr0half : (r₀ : ℝ) + 1 ≤ xe / 2 * n := by
    have h := Nat.ceil_le.1 F7
    rw [div_le_iff₀ hxe0] at h; linarith
  have hy0 : 0 < y := by linarith [Nat.cast_nonneg (α := ℝ) r₀]
  set r := ⌈y⌉₊ with hr
  have hry : y ≤ r := Nat.le_ceil y
  have hry' : (r : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
  have hrr₀ : r₀ ≤ r := by
    have : (r₀ : ℝ) ≤ r := by linarith
    exact_mod_cast this
  have hrpos : (0 : ℝ) < r := by linarith
  have hr1 : (1 : ℝ) ≤ r := by linarith [Nat.cast_nonneg (α := ℝ) r₀]
  have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlogr : Real.log n - b ≤ Real.log r := by
    have h1 : Real.log (xe / 2 * n) ≤ Real.log r :=
      Real.log_le_log (by positivity) (hyhalf.trans hry)
    rw [Real.log_mul (by positivity) hn0.ne'] at h1
    have := neg_abs_le (Real.log (xe / 2))
    linarith
  -- the main square-root estimate
  have hF4 : b * √w ^ 2 + 1 ≤ √w * sL := by
    have h := Real.le_sqrt_of_sq_le F4
    rw [div_le_iff₀ hsw] at h
    rw [hsw2]; linarith
  have hmain : √w * T - s ≤ √(Real.log r) * √((1 - η) * r) := by
    have hsq := core_sq (sw := √w) (sn := s) (sL := sL) (ρ := 1 - η) (x := xe) (r := r)
      (b := b) (lr := Real.log r) hsw.le hs0.le hsL0 hη'.le (by rw [hsw2])
      (by rw [hs2, ← hTe]; have : 0 ≤ A₀ * s := by positivity
          rw [hy] at hry; linarith)
      (by rw [hsL2]; exact hlogr) hb0 (by rw [hsL2]; exact F3)
      (by
        rw [hsL2]
        have : (1 - η) * Real.log n ≤ Real.log n := by nlinarith
        linarith)
      hF4
      (by
        rw [← hTe, hsw2, hs2]
        have h1 := mul_le_mul_of_nonneg_left F2 hη'.le
        have e : (1 - η) * (xe / 2 * n) = w * n / 2 := by rw [hw]; ring
        rw [e] at h1
        have : 0 ≤ w * n := by positivity
        linarith)
    rw [← hTe] at hsq
    rw [← Real.sqrt_mul hlogr0]
    exact Real.le_sqrt_of_sq_le hsq
  have hrup : (r : ℝ) ≤ 2 * (n * xe) := by
    have h1 := mul_le_mul_of_nonneg_right
      (show (A₀ + 1) / xe ≤ s from F6) hxe0.le
    rw [div_mul_cancel₀ _ hxe0.ne'] at h1
    have h2 : (A₀ + 1) * s ≤ s * xe * s := mul_le_mul_of_nonneg_right h1 hs0.le
    have h3 : s * xe * s = n * xe := by rw [← hss]; ring
    have h4 : 0 ≤ √w * T := by positivity
    have h5 : A₀ * s + 1 ≤ (A₀ + 1) * s := by
      have e : (A₀ + 1) * s = A₀ * s + s := by ring
      linarith only [hs1, e]
    rw [hy] at hry'
    linarith only [hry', h1, h2, h3, h4, h5]
  have hsqρ : √((1 - η) * r) ≤ √(2 * w) * s := by
    rw [hs', ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc (1 - η) * (r : ℝ) ≤ (1 - η) * (2 * (n * xe)) :=
          mul_le_mul_of_nonneg_left hrup hη'.le
      _ = 2 * w * n := by rw [hw]; ring
  set f := (r : ℝ) + (√(Real.log r) - 1) * √((1 - η) * r) with hf
  have hfge : n * xe + c * xe * s ≤ f := by
    have e : f = r + (√(Real.log r) * √((1 - η) * r) - √((1 - η) * r)) := by rw [hf]; ring
    rw [e]
    have e2 : y = (n : ℝ) * xe - √w * T + (s + √(2 * w) * s + c * xe * s) := by
      rw [hy, hA₀]; ring
    rw [e2] at hry
    linarith
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
  have hlam : (n : ℝ) * Ns / (f / η) ≤ e1 - γ := by
    rw [div_le_iff₀ (by positivity), mul_div_assoc', le_div_iff₀ hη0]
    have h1 : (e1 - γ) * (n * xe + c * xe * s) ≤ (e1 - γ) * f :=
      mul_le_mul_of_nonneg_left hfge (by linarith)
    have h2 : (e1 - γ) * (n * xe + c * xe * s) = xe * ((e1 - γ) * (s * s + c * s)) := by
      rw [hss]; ring
    have h3 : (e1 - γ) * (s * s + c * s) =
        e1 * (s * s) + (c * e1) * s - (γ * s) * s - (γ * s) * c := by
      ring
    have h4 : e1 * (s * s) ≤ (e1 - γ) * (s * s + c * s) := by
      rw [h3, hce, hγs]; linarith only [F5]
    have h5 : (n : ℝ) * Ns * η = xe * (e1 * (s * s)) := by
      rw [hss, hxe]; field_simp
    rw [h5]
    calc xe * (e1 * (s * s)) ≤ xe * ((e1 - γ) * (s * s + c * s)) :=
          mul_le_mul_of_nonneg_left h4 hxe0.le
      _ = _ := h2.symm
      _ ≤ _ := h1
  refine ⟨r, f / η, by positivity, fun ℓ => hr₀ r hrr₀ ℓ, hlam, ?_⟩
  have hch : (0 : ℝ) < ((n + r).choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left r n)
  have hlogM : Real.logb 2 (4 * n * ((n + r).choose r : ℝ)) =
      2 + Real.log n / Real.log 2 + Real.logb 2 ((n + r).choose r) := by
    rw [Real.logb_mul (by positivity) hch.ne', Real.logb_mul (by norm_num) hn0.ne']
    have h2 : Real.logb 2 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]
      simp
    rw [h2]; rfl
  have hup := logb_choose_le n r hxe0
  have hrG : ((r : ℝ) - n * xe) * G ≤ (1 - √w * T + A₀ * s) * G :=
    mul_le_mul_of_nonneg_right (by rw [hy] at hry'; linarith) hG0.le
  rw [hlogM, sqrt_form' hw0.le hG0.le]
  have h1 : Real.log n / Real.log 2 ≤ s / Real.log 2 :=
    div_le_div_of_nonneg_right hLs hlog2.le
  have h2 : G ≤ G * s := le_mul_of_one_le_right hG0.le hs1
  have e : (2 + 1 / Real.log 2 + A₀ * G + G) * s =
      2 * s + s / Real.log 2 + A₀ * G * s + G * s := by ring
  rw [e]
  nlinarith only [h1, h2, hup, hrG, hs1]

/-- Converse with `O(√n)` remainder. -/
theorem mean_conv_sharp {η Ns ε : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop, ∀ (L' M : ℕ) (C : Code n L' M), 1 ≤ M →
      C.meanPhotons ≤ n * Ns → 1 - ε ≤ C.success η →
        Real.logb 2 M ≤ n * g (η * Ns / (1 - ε))
          - √(((1 - η) * (η * Ns / (1 - ε)) * gp (η * Ns / (1 - ε)) ^ 2) * n * Real.log n)
          + A * √(n : ℝ) := by
  obtain ⟨A, hA⟩ := mean_sharp_cutoff hη0 hη1 hNs hε0 hε1
  refine ⟨A, ?_⟩
  filter_upwards [hA, eventually_ge_atTop 1] with n hn F1
  obtain ⟨r, lam, hlam0, hmaj, hlam, hlog⟩ := hn
  intro L' M C hM hmean hs
  refine le_trans ?_ hlog
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast F1
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have hγ0 : 0 < 1 / √(n : ℝ) := by positivity
  have hQ : ∑ ℓ ∈ range (L' + 1), C.law ℓ * binomGT ℓ η r ≤ 1 - ε - 1 / √(n : ℝ) := by
    calc ∑ ℓ ∈ range (L' + 1), C.law ℓ * binomGT ℓ η r
        ≤ ∑ ℓ ∈ range (L' + 1), C.law ℓ * ((ℓ : ℝ) / lam) :=
          Finset.sum_le_sum fun ℓ _ =>
            mul_le_mul_of_nonneg_left (hmaj ℓ) (C.law_nonneg ℓ)
      _ = C.meanPhotons / lam := by
          rw [C.meanPhotons_eq, Finset.sum_div]
          exact Finset.sum_congr rfl fun ℓ _ => by ring
      _ ≤ n * Ns / lam := div_le_div_of_nonneg_right hmean hlam0.le
      _ ≤ _ := hlam
  have hth : ε + 1 / √(n : ℝ) ≤ thinLT η C.law L' (r + 1) := by
    rw [C.sum_law_binomGT hM] at hQ; linarith
  have hconv := quantile_conv hη0.le hη1.le hM C r hs hγ0 hth
  have h4γ : 4 / (1 / √(n : ℝ)) ^ 2 = 4 * n := by
    rw [one_div, inv_pow, sq, hss]; field_simp
  rw [h4γ] at hconv
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  exact Real.logb_le_logb_of_le (by norm_num) hMr hconv

set_option maxHeartbeats 1000000 in
-- the proof is a long chain of elementary estimates in one context
/-- Achievability with `O(√n)` remainder. -/
theorem mean_ach_sharp {η Ns ε : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, ∃ L' M : ℕ, 1 ≤ M ∧ ∃ C : Code n L' M,
      C.meanPhotons ≤ n * Ns ∧ 1 - ε ≤ C.success η ∧
        n * g (η * Ns / (1 - ε))
          - √(((1 - η) * (η * Ns / (1 - ε)) * gp (η * Ns / (1 - ε)) ^ 2) * n * Real.log n)
          - A * √(n : ℝ) ≤ Real.logb 2 M := by
  obtain ⟨C', hC'0, hC'⟩ := binomLT_moderate hη0 hη1 (κ := 0) le_rfl
  have he1 : 0 < 1 - ε := by linarith
  set e1 := 1 - ε with he1def
  set xe := η * Ns / e1 with hxe
  have hxe0 : 0 < xe := by positivity
  have hxee : xe * e1 = η * Ns := by rw [hxe]; field_simp
  have hη' : 0 < 1 - η := by linarith
  set w := (1 - η) * xe with hw
  have hw0 : 0 < w := by positivity
  set G := gp xe with hG
  have hG0 : 0 < G := gp_pos hxe0
  have hsw : 0 < √w := Real.sqrt_pos.2 hw0
  set c₁ := C' * √(2 / Ns) + 1 with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set A := xe * c₁ / e1 with hA
  have hA0 : 0 < A := by positivity
  set β := |Real.log (Ns / e1)| with hβ
  have hβ0 : 0 ≤ β := abs_nonneg _
  set E := √(β * w) with hE
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  set R := √w + 1 with hR
  obtain ⟨B, hB0, hB⟩ := stirlingWide hxe0 R
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨G * (E + A) + G * (η + 1) + |Real.logb 2 (2 * Real.exp 1)| + B +
    1 / (2 * Real.log 2), ?_⟩
  filter_upwards [hB, eventually_ge_atTop 1, SecondOrderLog.eventually_sqrt_ge (c₁ / ε),
    eventually_ge_atTop ⌈4 / Ns⌉₊,
    MeanAsymp.absorb (E + A) 0 (η + 1) (δ := 1) one_pos,
    MeanAsymp.sqrt_nlogn_le R (δ := xe) hxe0,
    MeanAsymp.ev_log_ge 1] with n F0 F1 F2 F3 F5 F6 F8
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast F1
  have hn0 : (0 : ℝ) < n := by linarith
  have hLs := log_le_sqrt F1
  set S := √((n : ℝ) * Real.log n) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set s := √(n : ℝ) with hs'
  have hs0 : 0 < s := Real.sqrt_pos.2 hn0
  have hss : s * s = n := Real.mul_self_sqrt hn0.le
  have hs1 : 1 ≤ s := by
    rw [hs', show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hnr
  have hlog0 : 0 ≤ Real.log n := by linarith
  have hnNs : 4 ≤ (n : ℝ) * Ns := by
    have h := Nat.ceil_le.1 F3
    rw [div_le_iff₀ hNs] at h; exact h
  -- the weight p
  set u := c₁ / s with hu
  have hu0 : 0 < u := by positivity
  have hus : u * s = c₁ := by rw [hu]; field_simp
  have huε : u ≤ ε := by
    rw [div_le_iff₀ hε0] at F2
    rw [hu, div_le_iff₀ hs0]; linarith only [F2]
  set p := e1 + u with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, he1def]; linarith only [huε]
  have hpe : e1 ≤ p := by rw [hp]; linarith only [hu0]
  -- the photon number ℓ
  set X := (n : ℝ) * Ns / p with hX
  have hXp : X * p = n * Ns := by rw [hX]; field_simp
  have hX0 : 0 < X := by positivity
  have hXlo : (n : ℝ) * Ns ≤ X := by
    rw [hX, le_div_iff₀ hp0]
    have : 0 ≤ (n : ℝ) * Ns := by positivity
    nlinarith only [this, hp1]
  have hXhi : X ≤ n * Ns / e1 := div_le_div_of_nonneg_left (by positivity) he1 hpe
  set ℓ := ⌊X⌋₊ with hℓ
  have hℓX : (ℓ : ℝ) ≤ X := Nat.floor_le hX0.le
  have hXℓ : X < ℓ + 1 := Nat.lt_floor_add_one X
  have hℓ3 : (3 : ℝ) < ℓ := by linarith only [hXℓ, hXlo, hnNs]
  have hℓ2 : 2 ≤ ℓ := by
    have : (2 : ℝ) ≤ ℓ := by linarith only [hℓ3]
    exact_mod_cast this
  have hℓne : ℓ ≠ 0 := by omega
  have hℓ0 : (0 : ℝ) < ℓ := by linarith only [hℓ3]
  have hℓhalf : (n : ℝ) * Ns / 2 ≤ ℓ := by linarith only [hXℓ, hXlo, hnNs]
  have hpℓ : p * ℓ ≤ n * Ns := by
    rw [← hXp, mul_comm]; exact mul_le_mul_of_nonneg_right hℓX hp0.le
  have hℓhi : (ℓ : ℝ) ≤ n * Ns / e1 := hℓX.trans hXhi
  -- the threshold
  set τ := η * ℓ - √(Real.log ℓ) * √(ℓ * (η * (1 - η))) with hτ
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg (by linarith only [hℓ3])
  have hlogℓ : Real.log ℓ ≤ Real.log n + β := by
    have h1 : Real.log ℓ ≤ Real.log (Ns / e1 * n) :=
      Real.log_le_log hℓ0 (by rw [show Ns / e1 * n = n * Ns / e1 by ring]; exact hℓhi)
    rw [Real.log_mul (by positivity) hn0.ne'] at h1
    have := le_abs_self (Real.log (Ns / e1))
    linarith only [h1, this, hβ]
  have hsq : √(Real.log ℓ) * √(ℓ * (η * (1 - η))) ≤ √w * S + E * s := by
    have h2 : (ℓ : ℝ) * (η * (1 - η)) ≤ w * n := by
      have := mul_le_mul_of_nonneg_right hℓhi (by positivity : 0 ≤ η * (1 - η))
      have e : (n : ℝ) * Ns / e1 * (η * (1 - η)) = w * n := by rw [hw, hxe]; ring
      rw [e] at this; exact this
    have h3 := mul_le_mul hlogℓ h2 (by positivity) (by positivity)
    rw [← Real.sqrt_mul hlogℓ0]
    calc √(Real.log ℓ * (ℓ * (η * (1 - η))))
        ≤ √(w * (n * Real.log n) + β * w * n) :=
          Real.sqrt_le_sqrt (h3.trans_eq (by ring))
      _ ≤ √(w * (n * Real.log n)) + √(β * w * n) :=
          sqrt_add_le' (by positivity) (by positivity)
      _ = √w * S + E * s := by
          rw [Real.sqrt_mul hw0.le, Real.sqrt_mul (by positivity : 0 ≤ β * w)]
  have hηX : (n : ℝ) * xe - A * s ≤ η * X := by
    have h1 : ((n : ℝ) * xe - A * s) * p ≤ η * (n * Ns) := by
      have e : ((n : ℝ) * xe - A * s) * p =
          n * (xe * e1) + s * xe * (u * s) - xe * c₁ * s - xe * c₁ / e1 * (u * s) := by
        rw [hp, hA, ← hss]; field_simp; ring
      rw [e, hus, hxee]
      have : 0 ≤ xe * c₁ / e1 * c₁ := by positivity
      linarith only [this]
    calc (n : ℝ) * xe - A * s = ((n : ℝ) * xe - A * s) * p / p := by field_simp
      _ ≤ η * (n * Ns) / p := div_le_div_of_nonneg_right h1 hp0.le
      _ = η * X := by rw [hX]; ring
  have hηℓlo : (n : ℝ) * xe - A * s - η ≤ η * ℓ := by
    have : η * X < η * (ℓ + 1) := mul_lt_mul_of_pos_left hXℓ hη0
    linarith only [this, hηX]
  have hηℓhi : η * (ℓ : ℝ) ≤ n * xe := by
    have := mul_le_mul_of_nonneg_left hℓhi hη0.le
    have e : η * ((n : ℝ) * Ns / e1) = n * xe := by rw [hxe]; ring
    rw [e] at this; exact this
  rw [zero_mul, add_zero, one_mul] at F5
  have hRS : R * S = √w * S + S := by rw [hR]; ring
  have hτlo' : (n : ℝ) * xe - √w * S - (E + A) * s - η ≤ τ := by
    rw [hτ]; linarith only [hsq, hηℓlo]
  have hτlo : (n : ℝ) * xe - R * S + 1 ≤ τ := by
    rw [hRS]; linarith only [hτlo', F5]
  have hτ1 : 1 ≤ τ := by linarith only [hτlo, F6]
  have hτhi : τ ≤ η * ℓ := by
    rw [hτ]
    have : 0 ≤ √(Real.log ℓ) * √(ℓ * (η * (1 - η))) := by positivity
    linarith only [this]
  set t := ⌊τ⌋₊ with ht
  have htτ : (t : ℝ) ≤ τ := Nat.floor_le (by linarith only [hτ1])
  have hτt : τ < t + 1 := Nat.lt_floor_add_one τ
  have htℓ : t ≤ ℓ := by
    have h1 : η * (ℓ : ℝ) ≤ ℓ := by nlinarith only [hℓ0, hη1]
    have : (t : ℝ) ≤ ℓ := by linarith only [htτ, hτhi, h1]
    exact_mod_cast this
  have habs : |(t : ℝ) - n * xe| ≤ R * √((n : ℝ) * Real.log n) := by
    rw [abs_le]
    constructor
    · linarith only [hτt, hτlo]
    · have : 0 ≤ R * S := by rw [hRS]; positivity
      linarith only [htτ, hτhi, hηℓhi, this]
  have hSt := F0 t habs
  -- error of the law
  have hBL := hC' ℓ hℓ2 t (by rw [add_zero, one_mul]; exact htτ)
  have hsℓ : s ≤ √(2 / Ns) * √(ℓ : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_mul_eq_mul_div, le_div_iff₀ hNs]; linarith only [hℓhalf]
  have hsℓ0 : 0 < √(ℓ : ℝ) := Real.sqrt_pos.2 hℓ0
  have hBL' : binomLT ℓ η t ≤ (c₁ - 1) / s := by
    refine hBL.trans ?_
    rw [div_le_div_iff₀ hsℓ0 hs0, hc₁]
    have := mul_le_mul_of_nonneg_left hsℓ hC'0
    linarith only [this]
  -- the message set
  have hD1 : (1 : ℝ) ≤ sectorDim n t := by
    unfold sectorDim; exact_mod_cast Nat.choose_pos (by omega)
  have he1' : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hee0 : 0 < Real.exp 1 := Real.exp_pos 1
  set v := 1 / s with hv
  have hv0 : 0 < v := by positivity
  have hv1 : v ≤ 1 := by rw [hv, div_le_one hs0]; exact hs1
  set z := v * sectorDim n t / Real.exp 1 with hz
  have hz0 : 0 < z := by positivity
  have hzD : z ≤ sectorDim n t := by
    rw [hz, div_le_iff₀ hee0]; nlinarith only [hv1, he1', hD1, hv0]
  set M : ℕ := max 1 ⌊z⌋₊ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMz : (M : ℝ) - 1 ≤ z := by
    rcases le_total 1 ⌊z⌋₊ with h | h
    · rw [hM, max_eq_right h]; have := Nat.floor_le hz0.le; linarith
    · rw [hM, max_eq_left h]; push_cast; linarith
  have hMz2 : z / 2 ≤ M := by
    have h1 : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have h2 : (⌊z⌋₊ : ℝ) ≤ M := by exact_mod_cast le_max_right 1 ⌊z⌋₊
    have h3 := Nat.sub_one_lt_floor z
    rcases lt_or_ge z 2 with h | h <;> linarith
  have hMD : M ≤ (n + t - 1).choose t := by
    have : (M : ℝ) ≤ sectorDim n t := by
      rcases le_total 1 ⌊z⌋₊ with h | h
      · rw [hM, max_eq_right h]; exact (Nat.floor_le hz0.le).trans hzD
      · rw [hM, max_eq_left h]; push_cast; exact hD1
    unfold sectorDim at this; exact_mod_cast this
  have herrM : ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ v := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_right hMz hee0.le
    rw [hz] at this; field_simp at this; linarith
  -- the code
  set pl : ℕ → ℝ := fun j => if j = 0 then 1 - p else if j = ℓ then p else 0 with hpl
  have hpl0 : ∀ j, 0 ≤ pl j := by
    intro j; rw [hpl]; dsimp only
    split_ifs <;> linarith
  have hpl1 : ∑ j ∈ range (ℓ + 1), pl j = 1 := by
    have := MeanAsymp.sum_two hℓne (1 - p) p (fun _ => 1)
    simp only [mul_one] at this
    rw [hpl, this]; ring
  have hb0 : binomLT 0 η t ≤ 1 := BE.binomLT_le_one hη0 hη1 0 t
  have hbℓ0 : 0 ≤ binomLT ℓ η t := BE.binomLT_nonneg hη0 hη1 ℓ t
  have herr : ∑ j ∈ range (ℓ + 1), pl j * binomLT j η t +
      ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ ε := by
    rw [hpl, MeanAsymp.sum_two hℓne (1 - p) p (fun j => binomLT j η t)]
    have h1 : (1 - p) * binomLT 0 η t ≤ 1 - p :=
      mul_le_of_le_one_right (by linarith only [hp1]) hb0
    have h2 : p * binomLT ℓ η t ≤ binomLT ℓ η t := mul_le_of_le_one_left hbℓ0 hp1
    have h3 : (c₁ - 1) / s + v = u := by rw [hv, hu]; ring
    rw [hp, he1def] at h1
    linarith only [h1, h2, h3, hBL', herrM]
  obtain ⟨C, hC1, -, hC3⟩ := exists_lawCode hη0.le hη1.le F1 htℓ pl hpl0 hpl1 hM1 hMD herr
  refine ⟨ℓ, M, hM1, C, ?_, hC1, ?_⟩
  · rw [hC3, hpl, MeanAsymp.sum_two hℓne (1 - p) p (fun j => (j : ℝ))]
    simp only [Nat.cast_zero, mul_zero, zero_add]
    exact hpℓ
  -- the rate
  have hlogM : Real.logb 2 (z / 2) ≤ Real.logb 2 M :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hMz2
  have hlogv : Real.logb 2 v = -(1 / (2 * Real.log 2)) * Real.log n := by
    rw [SecondOrderLog.logb_two_eq, hv, Real.log_div one_ne_zero hs0.ne', Real.log_one, hs',
      Real.log_sqrt hn0.le]
    field_simp
    ring
  have hsplit : Real.logb 2 (z / 2) =
      Real.logb 2 (sectorDim n t) - Real.logb 2 (2 * Real.exp 1)
        - (1 / (2 * Real.log 2)) * Real.log n := by
    have e : z / 2 = sectorDim n t / (2 * Real.exp 1) * v := by rw [hz]; field_simp
    rw [e, Real.logb_mul (by positivity) hv0.ne', Real.logb_div (by positivity) (by positivity),
      hlogv]
    ring
  have htG : -(√w * S + (E + A) * s + η + 1) * G ≤ ((t : ℝ) - n * xe) * G :=
    mul_le_mul_of_nonneg_right (by linarith only [hτt, hτlo']) hG0.le
  rw [sqrt_form' hw0.le hG0.le]
  rw [hsplit] at hlogM
  have k1 : B * Real.log n ≤ B * s := mul_le_mul_of_nonneg_left hLs hB0
  have k2 : (1 / (2 * Real.log 2)) * Real.log n ≤ (1 / (2 * Real.log 2)) * s :=
    mul_le_mul_of_nonneg_left hLs (by positivity)
  have k3 : G * (η + 1) ≤ G * (η + 1) * s :=
    le_mul_of_one_le_right (by positivity) hs1
  have k4 : Real.logb 2 (2 * Real.exp 1) ≤ |Real.logb 2 (2 * Real.exp 1)| * s :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hs1)
  nlinarith only [hlogM, hSt, htG, k1, k2, k3, k4]

/-- **Main theorem.** `log₂ M*(n, ε) = n g(x) - √(V n ln n) + O(√n)`, where
`x = η N_S/(1-ε)` and `V = (1-η) x g'(x)²`. -/
theorem mean_second_order_sharp {η Ns ε : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      (∃ L' M : ℕ, 1 ≤ M ∧ ∃ C : Code n L' M, C.meanPhotons ≤ n * Ns ∧ 1 - ε ≤ C.success η ∧
        n * g (η * Ns / (1 - ε))
          - √(((1 - η) * (η * Ns / (1 - ε)) * gp (η * Ns / (1 - ε)) ^ 2) * n * Real.log n)
          - A * √(n : ℝ) ≤ Real.logb 2 M) ∧
      (∀ (L' M : ℕ) (C : Code n L' M), 1 ≤ M → C.meanPhotons ≤ n * Ns → 1 - ε ≤ C.success η →
        Real.logb 2 M ≤ n * g (η * Ns / (1 - ε))
          - √(((1 - η) * (η * Ns / (1 - ε)) * gp (η * Ns / (1 - ε)) ^ 2) * n * Real.log n)
          + A * √(n : ℝ)) := by
  obtain ⟨A₁, h₁⟩ := mean_ach_sharp hη0 hη1 hNs hε0 hε1
  obtain ⟨A₂, h₂⟩ := mean_conv_sharp hη0 hη1 hNs hε0 hε1
  refine ⟨max A₁ A₂, ?_⟩
  filter_upwards [h₁, h₂] with n hn₁ hn₂
  have hs := Real.sqrt_nonneg (n : ℝ)
  have k₁ : A₁ * √(n : ℝ) ≤ max A₁ A₂ * √(n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hs
  have k₂ : A₂ * √(n : ℝ) ≤ max A₁ A₂ * √(n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hs
  refine ⟨?_, fun L' M C hM hmean hsucc => (hn₂ L' M C hM hmean hsucc).trans (by linarith)⟩
  obtain ⟨L', M, hM, C, hmean, hsucc, hrate⟩ := hn₁
  exact ⟨L', M, hM, C, hmean, hsucc, le_trans (by linarith) hrate⟩

end QIQCOP
