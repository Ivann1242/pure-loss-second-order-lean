import QIQCOP.UnboundedCode
import QIQCOP.Final
import QIQCOP.MeanMain

/-!
# Converses over arbitrary inputs on the full Fock space (M3, M4)

* `unbounded_converse_log` (M3): the converse half of `second_order_asymptotics` for `UCode`.
* `unbounded_mean_bound` (M4a): generic bridge from any linear majorant of the binomial tail.
* `unbounded_mean_converse` (M4b): the converse half of `mean_second_order` for `UCode`.

Mean-constrained statements assume `Summable (t ↦ t P(t))`: a Lean `tsum` is `0` on a divergent
series, so without this hypothesis `mean ≤ n Ns` would not express a finite-energy constraint.
-/

open Real Filter Finset MeasureTheory ProbabilityTheory

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace QIQCOP

namespace Unbounded

open SecondOrderLog

variable {n M : ℕ}

/-- Output weight above `r` is controlled by leakage above `L`. -/
theorem UCode.tail_le_of_leak (C : UCode n M) {η d : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (hM : 1 ≤ M) (r L : ℕ) (hleak : C.leak L ≤ d) (hd : d ≤ 1) :
    C.tail η r ≤ (1 - d) * binomGT L η r + d := by
  set G := binomGT L η r with hG
  have hG0 : 0 ≤ G := binomGT_nonneg hη.1 hη.2 _ _
  have hG1 : G ≤ 1 := binomGT_le_one hη.1 hη.2 _ _
  have hlaw := C.hasSum_law hM
  have hl : Summable fun t => if L < t then C.law t else 0 :=
    Summable.of_nonneg_of_le
      (fun t => by split_ifs; exacts [C.law_nonneg t, le_rfl])
      (fun t => by split_ifs; exacts [le_rfl, C.law_nonneg t]) hlaw.summable
  have hR : HasSum (fun t => C.law t * G + (if L < t then C.law t else 0) * (1 - G))
      (1 * G + C.leak L * (1 - G)) :=
    (hlaw.mul_right G).add (hl.hasSum.mul_right (1 - G))
  have hle : C.tail η r ≤ 1 * G + C.leak L * (1 - G) := by
    refine hasSum_le (fun t => ?_) (C.hasSum_tail hη r).summable.hasSum hR
    have h0 := C.law_nonneg t
    by_cases h : L < t
    · simp only [if_pos h]
      have := binomGT_le_one hη.1 hη.2 t r
      nlinarith
    · simp only [if_neg h, zero_mul, add_zero]
      exact mul_le_mul_of_nonneg_left (binomGT_mono hη.1 hη.2 r (not_lt.1 h)) h0
  have : C.leak L * (1 - G) ≤ d * (1 - G) :=
    mul_le_mul_of_nonneg_right hleak (by linarith)
  linarith

/-- A linear majorant of the binomial tail bounds `w_r` by the mean. -/
theorem UCode.tail_le_mean (C : UCode n M) {η lam : ℝ} {r : ℕ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (hlam : 0 < lam) (hmaj : ∀ ℓ : ℕ, binomGT ℓ η r ≤ (ℓ : ℝ) / lam)
    (hsm : Summable fun t : ℕ => (t : ℝ) * C.law t) : C.tail η r ≤ C.mean / lam := by
  have hR : HasSum (fun t : ℕ => (t : ℝ) * C.law t / lam) (C.mean / lam) :=
    hsm.hasSum.div_const lam
  refine hasSum_le (fun t => ?_) (C.hasSum_tail hη r).summable.hasSum hR
  have := mul_le_mul_of_nonneg_left (hmaj t) (C.law_nonneg t)
  calc C.law t * binomGT t η r ≤ C.law t * ((t : ℝ) / lam) := this
    _ = (t : ℝ) * C.law t / lam := by ring

set_option maxHeartbeats 1000000 in
/-- **M3.** Occupation converse over arbitrary inputs on the full Fock space. -/
theorem unbounded_converse_log {η Ns δ q B : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hB : 0 ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n : ℕ in atTop, ∀ (M : ℕ) (C : UCode n M), 1 ≤ M →
      C.leak (cutoff Ns n) ≤ δ + B / √(n : ℝ) →
      1 - (1 - δ) * Φ q ≤ C.success (⟨hη0.le, hη1.le⟩ : η ∈ Set.Icc (0 : ℝ) 1) →
        Real.logb 2 M ≤ n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) + A * Real.log n := by
  have hηI : η ∈ Set.Icc (0 : ℝ) 1 := ⟨hη0.le, hη1.le⟩
  have hBE : BinomBE η := binomBE hη0 hη1
  have hx : 0 < η * Ns := mul_pos hη0 hNs
  have hgp := gp_pos hx
  have hgs := gp_mul_sqrt_eq_sqrt_Vocc hη0 hη1 hNs
  set a := η * (1 - η) with ha
  have ha0 : 0 < a := mul_pos hη0 (by linarith)
  have hsa : 0 < √a := Real.sqrt_pos.2 ha0
  have hd : 0 < 1 - δ := by linarith
  have hsN1 : 0 < √(Ns + 1) := Real.sqrt_pos.2 (by linarith)
  set K := (B + 1) * √(Ns + 1) / (1 - δ) with hK
  obtain ⟨c, hc0, L₁, hL₁⟩ := binomLT_ge_of_BE hη0 hη1 hBE q K
  set D := |q| * √a + η + c + 1 with hD
  have hD0 : 0 ≤ D := by positivity
  set c2 := 1 / Real.log 2 with hc2
  have hc20 : 0 < c2 := by rw [hc2]; exact one_div_pos.2 (Real.log_pos (by norm_num))
  have hΦ0 := Φ_pos q
  have hΦ1 := Φ_lt_one q
  refine ⟨D * gp (η * Ns) + 2 + c2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 3, (tendsto_cutoff hNs).eventually (eventually_ge_atTop L₁),
    eventually_sqrt_cutoff_ge hNs (|q| * √a / η), eventually_sqrt_ge (B / (1 - δ))]
    with n hn3 hnL hnW hnB
  intro M C hM hleak hs
  have hn1 : 1 ≤ n := by omega
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlog := one_le_log_of_three_le hn3
  obtain ⟨hLlo, hLhi, hσlo, hσhi, hsLn⟩ := cutoff_facts hη0 hη1 hNs hn1
  rw [← ha] at hσlo hσhi
  set L := cutoff Ns n with hLdef
  set Lr : ℝ := (L : ℝ) with hLr
  set sn := √(n : ℝ) with hsn
  have hsn1 : 1 ≤ sn := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsn2 : sn ^ 2 = n := Real.sq_sqrt (by linarith)
  have hLr0 : 0 < Lr := lt_of_lt_of_le (by positivity) hLlo
  set sL := √Lr with hsL
  have hsL0 : 0 < sL := Real.sqrt_pos.2 hLr0
  have hsL2 : sL * sL = Lr := Real.mul_self_sqrt hLr0.le
  set σ := √(Lr * a) with hσ
  have hσe : σ = sL * √a := Real.sqrt_mul hLr0.le _
  set s₀ := sn * √(η * (1 - η) * Ns) with hs₀
  obtain ⟨hqlo, hqhi⟩ := mul_between (q := q) hσlo hσhi
  -- the threshold
  set y := η * Lr + q * σ + c with hy
  have hy0 : 0 ≤ y := by
    rw [div_le_iff₀ hη0] at hnW
    have h1 : -(|q| * σ) ≤ q * σ := by
      have := neg_abs_le q
      have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
      nlinarith
    have h2 : |q| * σ ≤ η * Lr := by
      rw [hσe, ← hsL2]
      have := mul_le_mul_of_nonneg_right hnW hsL0.le
      nlinarith
    linarith
  set r := ⌈y⌉₊ with hr
  have hry : y ≤ r := Nat.le_ceil y
  have hry1 : (r : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have hP := hL₁ L hnL (r + 1) (by push_cast; linarith)
  set P := binomLT L η (r + 1) with hPdef
  have hG : binomGT L η r = 1 - P := rfl
  have hG0 := binomGT_nonneg hη0.le hη1.le L r
  have hP1 : P ≤ 1 := by linarith
  -- slack
  set u := 1 / sn with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu, div_le_one (by linarith)]; exact hsn1
  have hKu : (B + 1) * u / (1 - δ) ≤ K / sL := by
    rw [hK, hu, div_le_div_iff₀ hd hsL0]
    have h1 : (B + 1) * (1 / sn) * sL ≤ (B + 1) * (1 / sn) * (sn * √(Ns + 1)) :=
      mul_le_mul_of_nonneg_left hsLn (by positivity)
    have h2 : (B + 1) * (1 / sn) * (sn * √(Ns + 1)) = (B + 1) * √(Ns + 1) := by
      field_simp
    have h3 : (B + 1) * √(Ns + 1) / (1 - δ) * (1 - δ) = (B + 1) * √(Ns + 1) := by
      field_simp
    linarith
  set P₀ := Φ q + (B + 1) * u / (1 - δ) with hP₀
  have hP₀P : P₀ ≤ P := by linarith
  have hP₀e : (1 - δ) * P₀ = (1 - δ) * Φ q + (B + 1) * u := by
    rw [hP₀]; field_simp
  have hBu : B / sn = B * u := by rw [hu]; ring
  rw [hBu] at hleak
  have hδn1 : δ + B * u ≤ 1 := by
    rw [div_le_iff₀ hd] at hnB
    have : B * u ≤ 1 - δ := by
      rw [hu, mul_one_div, div_le_iff₀ (by linarith)]
      linarith
    linarith
  have hBu0 : 0 ≤ B * u := by positivity
  have hkey : (1 - δ) * Φ q + u ≤ (1 - (δ + B * u)) * P := by
    have h1 : (1 - (δ + B * u)) * P₀ ≤ (1 - (δ + B * u)) * P :=
      mul_le_mul_of_nonneg_left hP₀P (by linarith)
    have h2 : (1 - (δ + B * u)) * P₀ = (1 - δ) * P₀ - B * u * P₀ := by ring
    have h3 : B * u * P₀ ≤ B * u * 1 := mul_le_mul_of_nonneg_left (by linarith) hBu0
    linarith
  set ε := (1 - δ) * Φ q with hε
  have hε0 : 0 ≤ ε := by positivity
  set Q := (1 - (δ + B * u)) * binomGT L η r + (δ + B * u) with hQ
  have hQle : Q ≤ 1 - ε - u := by rw [hQ, hG]; linarith
  have hQ0 : 0 ≤ Q := by
    have := mul_nonneg (sub_nonneg.2 hδn1) hG0
    rw [hQ]; linarith
  have htail : C.tail η r ≤ Q := C.tail_le_of_leak hηI hM r L hleak hδn1
  have hconv := unbounded_quantile_conv hηI hM C r hs hu0 (htail.trans hQle)
  have hch : (0 : ℝ) < ((n + r).choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left _ _)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have h4u : 4 / u ^ 2 = 4 * (n : ℝ) := by
    rw [hu, ← hsn2]
    field_simp
  have hM' : (M : ℝ) ≤ ((n + r).choose r : ℝ) * (4 * n) := by
    rw [h4u] at hconv
    linarith
  have hlogM : Real.logb 2 M ≤ Real.logb 2 ((n + r).choose r : ℝ) + 2 + c2 * Real.log n := by
    have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hMr hM'
    rw [Real.logb_mul hch.ne' (by positivity), Real.logb_mul (by norm_num) (by positivity)] at h1
    have h4 : Real.logb 2 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [h4, logb_two_eq (n : ℝ)] at h1
    linarith
  have hst := logb_choose_le n r hx
  -- r - n x ≤ q s₀ + D
  have hrn : (r : ℝ) - n * (η * Ns) ≤ q * s₀ + D := by
    have e2 : η * Lr ≤ η * (n * Ns + 1) := mul_le_mul_of_nonneg_left hLhi.le hη0.le
    rw [hD]
    nlinarith
  have h4 := mul_le_mul_of_nonneg_right hrn hgp.le
  have h5 : (q * s₀ + D) * gp (η * Ns) = q * √(Vocc η Ns) * sn + D * gp (η * Ns) := by
    rw [← hgs, hs₀]; ring
  rw [h5] at h4
  have h6 : D * gp (η * Ns) + 2 ≤ (D * gp (η * Ns) + 2) * Real.log n :=
    le_mul_of_one_le_right (by positivity) hlog
  have h7 : (D * gp (η * Ns) + 2 + c2) * Real.log n =
      (D * gp (η * Ns) + 2) * Real.log n + c2 * Real.log n := by ring
  rw [h7]
  linarith


/-- **M4(a).** Generic bridge from a linear majorant of the binomial tail. -/
theorem unbounded_mean_bound {η Ns ε lam : ℝ} {n M r : ℕ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (C : UCode n M) (hmaj : ∀ ℓ : ℕ, binomGT ℓ η r ≤ (ℓ : ℝ) / lam) (hlam : 0 < lam)
    (hsm : Summable fun t : ℕ => (t : ℝ) * C.law t) (hmean : C.mean ≤ n * Ns)
    (hgap : n * Ns / lam ≤ 1 - ε - 1 / √(n : ℝ)) (hs : 1 - ε ≤ C.success hη) (hn : 1 ≤ n) :
    Real.logb 2 M ≤ Real.logb 2 (4 * n * ((n + r).choose r : ℝ)) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hch : (1 : ℝ) ≤ ((n + r).choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left r n)
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [Nat.cast_zero, Real.logb_zero]
    exact Real.logb_nonneg (by norm_num) (by nlinarith)
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by linarith)
  have hw : C.tail η r ≤ 1 - ε - 1 / √(n : ℝ) := by
    have h1 := C.tail_le_mean hη hlam hmaj hsm
    have h2 : C.mean / lam ≤ n * Ns / lam := div_le_div_of_nonneg_right hmean hlam.le
    linarith
  have h := unbounded_quantile_conv hη hM C r hs (by positivity) hw
  have e : 4 / (1 / √(n : ℝ)) ^ 2 = 4 * (n : ℝ) := by
    rw [one_div, inv_pow, hsq]
    field_simp
  rw [e] at h
  exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hM) h

set_option maxHeartbeats 1000000 in
/-- **M4(b).** The converse half of `mean_second_order` over arbitrary inputs. -/
theorem unbounded_mean_converse {η Ns ε κ : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (M : ℕ) (C : UCode n M), 1 ≤ M →
      Summable (fun t : ℕ => (t : ℝ) * C.law t) → C.mean ≤ n * Ns →
      1 - ε ≤ C.success (⟨hη0.le, hη1.le⟩ : η ∈ Set.Icc (0 : ℝ) 1) →
        Real.logb 2 M ≤ n * g (η * Ns / (1 - ε))
          - √((1 - κ) * ((1 - η) * (η * Ns / (1 - ε)) * gp (η * Ns / (1 - ε)) ^ 2) * n *
              Real.log n) := by
  have hηI : η ∈ Set.Icc (0 : ℝ) 1 := ⟨hη0.le, hη1.le⟩
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
  intro M C hM hsm hmean hs
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
  have hQ : C.tail η r ≤ 1 - ε - γ := by
    have h1 := C.tail_le_mean hηI (lam := f / η) (by positivity) (hr₀ r hrr₀) hsm
    have h2 : C.mean / (f / η) ≤ n * Ns / (f / η) :=
      div_le_div_of_nonneg_right hmean (by positivity)
    linarith
  have hconv := unbounded_quantile_conv hηI hM C r hs hγ0 hQ
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

end Unbounded

end QIQCOP
