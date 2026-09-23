import QIQCOP.Code
import QIQCOP.Stirling
import QIQCOP.Gaussian
import QIQCOP.Dispersion
import QIQCOP.Asymptotic

/-!
# The candidate pure-loss second-order converse is false

Problem: <https://qiqc-op.com/problem/op_89fb664ba06ba5de/>, Eq. (4):

  `log₂ M*_occ(n, η, N_S, ε, c) ≤ n g(η N_S) + √(n v(η N_S)) Φ⁻¹(ε) + O(log n)`.

`CandidateConverse η Ns ε q` is this upper bound, with `q = Φ⁻¹(ε)`, asserted for every code
whose inputs lie in the photon-cutoff subspace (`≤ ⌈n N_S⌉` photons). Such codes satisfy the
occupation constraint Eq. (2) with `δ_n = 0`, so `M ≤ M*_occ` for each of them. Hence Eq. (4)
implies `CandidateConverse η Ns ε (Φ⁻¹ ε)`, and refuting the latter refutes Eq. (4).

The refutation uses the fixed-photon condensate code (`QIQCOP.Code`). Its threshold comes from
Chebyshev's inequality instead of Berry–Esseen, which gives the dispersion `V_occ / (ε - γ)` in
place of `V_occ` (the CLT-sharp value). That is still strictly below `v · Φ⁻¹(ε)²` whenever
`(1-η)/(1+ηN_S) < Φ⁻¹(ε)² ε`. In particular this covers every `ε < 1/2` and `N_S > 0` for all
`η` close enough to `1`.
-/

open Real Filter Finset

namespace QIQCOP

/-- Eq. (4) of the problem for codes with inputs below the photon cutoff `⌈n N_S⌉`,
with `q` in place of `Φ⁻¹(ε)`. -/
def CandidateConverse (η Ns ε q : ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ (M : ℕ) (code : Code n (cutoff Ns n) M), 1 ≤ M →
    1 - ε ≤ code.success η →
      logb 2 M ≤ n * g (η * Ns) + √(n * vTh (η * Ns)) * q + C * log n

lemma sqrt_add_le (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : √(u + v) ≤ √u + √v := by
  rw [show √u + √v = √((√u + √v) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  have h1 := Real.sq_sqrt hu
  have h2 := Real.sq_sqrt hv
  have h3 := mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)
  exact Real.sqrt_le_sqrt (by nlinarith)

set_option maxHeartbeats 2000000 in
/-- **Second-order achievability from a threshold bound.** Let `0 < γ ≤ 1` and `s ≥ 0`, and
suppose that for large `n`, `Pr{K < η L - s √(L η(1-η))} ≤ ε - γ` with `K ~ Bin(L, η)` and
`L = ⌈n N_S⌉`. Then for all large `n` there is a code with success `≥ 1 - ε` and
`log₂ M ≥ n g(η N_S) - √n · s √V_occ - O(log n)`. -/
theorem achievability_of_threshold {η Ns ε γ s : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hs0 : 0 ≤ s)
    (hth : ∀ᶠ n : ℕ in atTop, binomLT (cutoff Ns n) η
      ⌈η * (cutoff Ns n : ℝ) - s * √((cutoff Ns n : ℝ) * (η * (1 - η)))⌉₊ ≤ ε - γ) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, ∃ M : ℕ, 1 ≤ M ∧
      (∃ code : Code n (cutoff Ns n) M, 1 - ε ≤ code.success η) ∧
      n * g (η * Ns) - √(n : ℝ) * (s * √(Vocc η Ns)) - A * log n ≤ logb 2 M := by
  set x := η * Ns with hx
  set a := η * (1 - η) with ha
  have hx0 : 0 < x := mul_pos hη0 hNs
  have ha0 : 0 < a := mul_pos hη0 (by linarith)
  have hgp := gp_pos hx0
  set R := s * √(Ns * a) + s * √a + η + 1 with hR
  obtain ⟨B, hB0, hB⟩ := stirlingExpansion hx0 R
  set c0 := s * √a * gp x with hc0
  set c1 := logb 2 (γ / (2 * Real.exp 1)) with hc1
  refine ⟨B + |c0| + |c1| + 1, ?_⟩
  filter_upwards [hB, hth, eventually_ge_atTop 3] with n hSt hPt0 hn3
  rw [← hx] at hSt
  -- basic facts about n
  have hn : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hsn : 1 ≤ √(n : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hlog : 1 ≤ log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  -- the cutoff L
  set L := cutoff Ns n with hLdef
  set Lr : ℝ := (L : ℝ) with hLr
  have hL1 : (n : ℝ) * Ns ≤ Lr := Nat.le_ceil _
  have hL2 : Lr < n * Ns + 1 := Nat.ceil_lt_add_one (by positivity)
  have hLpos : 1 ≤ L := by
    have : (0 : ℝ) < Lr := lt_of_lt_of_le (by positivity) hL1
    exact_mod_cast (show (0 : ℝ) < L from this)
  -- the Chebyshev threshold
  set y := η * Lr - s * √(Lr * a) with hy
  set t := ⌈y⌉₊ with ht
  have hPt : binomLT L η t ≤ ε - γ := hPt0
  have htL : t ≤ L := by
    rw [ht, Nat.ceil_le]
    have : 0 ≤ s * √(Lr * a) := mul_nonneg hs0 (Real.sqrt_nonneg _)
    have : η * Lr ≤ Lr := by nlinarith
    linarith
  have hty : y ≤ t := Nat.le_ceil y
  have htup : (t : ℝ) < η * Lr + 1 := by
    have hyle : y ≤ η * Lr := by
      have : 0 ≤ s * √(Lr * a) := mul_nonneg hs0 (Real.sqrt_nonneg _)
      linarith
    have h1 : t ≤ ⌈η * Lr⌉₊ := Nat.ceil_mono hyle
    have h2 : (⌈η * Lr⌉₊ : ℝ) < η * Lr + 1 := Nat.ceil_lt_add_one (by positivity)
    have h3 : (t : ℝ) ≤ ⌈η * Lr⌉₊ := by exact_mod_cast h1
    linarith
  -- √(L a) ≤ √n √(N_S a) + √a
  have hsqn : √((n : ℝ) * Ns * a) = √(n : ℝ) * √(Ns * a) := by
    rw [mul_assoc]; exact Real.sqrt_mul hn0 _
  have hsqL : √(Lr * a) ≤ √(n : ℝ) * √(Ns * a) + √a := by
    rw [← hsqn]
    calc √(Lr * a) ≤ √(n * Ns * a + a) := Real.sqrt_le_sqrt (by nlinarith)
      _ ≤ _ := sqrt_add_le _ _ (by positivity) ha0.le
  have hsNa : 0 ≤ √(Ns * a) := Real.sqrt_nonneg _
  have hsa : 0 ≤ √a := Real.sqrt_nonneg _
  -- bounds on t - n x
  have htlow : -(s * (√(n : ℝ) * √(Ns * a))) - s * √a ≤ (t : ℝ) - n * x := by
    have e1 : s * √(Lr * a) ≤ s * (√(n : ℝ) * √(Ns * a)) + s * √a := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left hsqL hs0
    have e2 : η * (n * Ns) ≤ η * Lr := mul_le_mul_of_nonneg_left hL1 hη0.le
    have e3 : (n : ℝ) * x = η * (n * Ns) := by rw [hx]; ring
    linarith
  have hthigh : (t : ℝ) - n * x ≤ η + 1 := by
    have e2 : η * Lr ≤ η * (n * Ns + 1) := mul_le_mul_of_nonneg_left hL2.le hη0.le
    have e3 : (n : ℝ) * x = η * (n * Ns) := by rw [hx]; ring
    linarith
  have hwin : |(t : ℝ) - n * x| ≤ R * √(n : ℝ) := by
    rw [abs_le]
    have e : R * √(n : ℝ) = s * (√(n : ℝ) * √(Ns * a)) + (s * √a + η + 1) * √(n : ℝ) := by
      rw [hR]; ring
    have hk0 : 0 ≤ s * √a + η + 1 := by
      have := mul_nonneg hs0 hsa; linarith
    have k1 : s * √a + η + 1 ≤ (s * √a + η + 1) * √(n : ℝ) := le_mul_of_one_le_right hk0 hsn
    have k2 : 0 ≤ s * (√(n : ℝ) * √(Ns * a)) :=
      mul_nonneg hs0 (mul_nonneg (Real.sqrt_nonneg _) hsNa)
    have k3 : 0 ≤ s * √a := mul_nonneg hs0 hsa
    constructor <;> linarith
  have hSt' := hSt t hwin
  -- the √n coefficient: s √(n N_S a) g'(x) = √n · √V_occ / √(ε-γ)
  have hVocc : √(n : ℝ) * (s * √(Vocc η Ns)) = s * (√(n : ℝ) * √(Ns * a)) * gp x := by
    have : √(Vocc η Ns) = √(Ns * a) * gp x := by
      rw [show Vocc η Ns = (Ns * a) * gp x ^ 2 by simp only [Vocc, ha, hx]; ring]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hgp.le]
    rw [this]; ring
  have hcoef : -(√(n : ℝ) * (s * √(Vocc η Ns))) - c0 ≤ ((t : ℝ) - n * x) * gp x := by
    have := mul_le_mul_of_nonneg_right htlow hgp.le
    rw [hVocc, hc0]; linarith
  -- the code size M = max 1 ⌊γ D / e⌋
  have hn1 : 1 ≤ n := by omega
  have hD1 : (1 : ℝ) ≤ sectorDim n t := by
    unfold sectorDim; exact_mod_cast Nat.choose_pos (by omega)
  have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set z := γ * sectorDim n t / Real.exp 1 with hz
  have hz0 : 0 < z := by positivity
  have hzD : z ≤ sectorDim n t := by
    rw [hz, div_le_iff₀ he0]; nlinarith
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
  have herr : binomLT L η t + ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ ε := by
    have : ((M : ℝ) - 1) * Real.exp 1 / sectorDim n t ≤ γ := by
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_right hMz he0.le
      rw [hz] at this; field_simp at this; linarith
    linarith
  refine ⟨M, hM1, exists_code (L := L) hη0.le hη1.le hn1 htL hM1 hMD herr, ?_⟩
  -- log₂ M ≥ log₂ (z/2) = log₂ D + log₂ (γ/(2e))
  have hlogM : logb 2 (z / 2) ≤ logb 2 M :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hMz2
  have hsplit : logb 2 (z / 2) = logb 2 (sectorDim n t) + c1 := by
    rw [hc1, ← Real.logb_mul (by positivity) (by positivity)]
    congr 1; rw [hz]; field_simp
  have habs0 : c0 ≤ |c0| := le_abs_self c0
  have habs1 : -|c1| ≤ c1 := neg_abs_le c1
  have hc : |c0| + |c1| + 1 ≤ (|c0| + |c1| + 1) * log n :=
    le_mul_of_one_le_right (by positivity) hlog
  rw [hsplit] at hlogM
  have hexp : (B + |c0| + |c1| + 1) * log n = B * log n + (|c0| + |c1| + 1) * log n := by ring
  have h1 : (n : ℝ) * g x - √(n : ℝ) * (s * √(Vocc η Ns)) - c0 - B * log n ≤
      logb 2 (sectorDim n t) := by linarith
  have h2 : (n : ℝ) * g x - √(n : ℝ) * (s * √(Vocc η Ns)) - c0 - B * log n + c1 ≤
      logb 2 M := by linarith
  rw [hexp]
  linarith

/-- **The contradiction.** A threshold bound with slack `s` whose achievable `√n` coefficient
`-s √V_occ` beats the conjectured `√v · q` refutes the candidate converse. -/
theorem not_candidateConverse_of_threshold {η Ns ε q γ s : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hNs : 0 < Ns) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hs0 : 0 ≤ s)
    (hth : ∀ᶠ n : ℕ in atTop, binomLT (cutoff Ns n) η
      ⌈η * (cutoff Ns n : ℝ) - s * √((cutoff Ns n : ℝ) * (η * (1 - η)))⌉₊ ≤ ε - γ)
    (hgap : s * √(Vocc η Ns) < √(vTh (η * Ns)) * (-q)) :
    ¬ CandidateConverse η Ns ε q := by
  rintro ⟨C, hC⟩
  obtain ⟨A, hA⟩ := achievability_of_threshold hη0 hη1 hNs hγ0 hγ1 hs0 hth
  apply not_eventually_sqrt_le_log (δ := √(vTh (η * Ns)) * (-q) - s * √(Vocc η Ns))
    (K := A + C) (by linarith)
  filter_upwards [hA, hC] with n hAn hCn
  obtain ⟨M, hM1, ⟨code, hcode⟩, hlow⟩ := hAn
  have hup := hCn M code hM1 hcode
  have e : √((n : ℝ) * vTh (η * Ns)) = √(n : ℝ) * √(vTh (η * Ns)) :=
    Real.sqrt_mul (Nat.cast_nonneg n) _
  rw [e] at hup
  nlinarith

lemma vTh_pos {η Ns : ℝ} (hη0 : 0 < η) (hNs : 0 < Ns) : 0 < vTh (η * Ns) := by
  have hx0 : 0 < η * Ns := mul_pos hη0 hNs
  rw [vTh_eq hx0]; have := gp_pos hx0; positivity

/-- **Main theorem (Chebyshev version).** For `0 < η < 1`, `N_S > 0` and `q < 0` with
`(1-η)/(1+ηN_S) < q² ε`, the candidate converse fails. -/
theorem candidateConverse_false {η Ns ε q : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hq : q < 0) (hcond : (1 - η) / (1 + η * Ns) < q ^ 2 * ε) :
    ¬ CandidateConverse η Ns ε q := by
  set r := (1 - η) / (1 + η * Ns) with hr
  have hηN : 0 < η * Ns := mul_pos hη0 hNs
  have hr0 : 0 < r := div_pos (by linarith) (by linarith)
  have hq2 : 0 < q ^ 2 := by nlinarith
  have hrq : r / q ^ 2 < ε := by rw [div_lt_iff₀ hq2]; linarith
  set γ := min ((ε - r / q ^ 2) / 2) 1 with hγ
  have hγ0 : 0 < γ := lt_min (by linarith) one_pos
  have hγ1 : γ ≤ 1 := min_le_right _ _
  have hγle : γ ≤ (ε - r / q ^ 2) / 2 := min_le_left _ _
  have hrq0 : 0 < r / q ^ 2 := div_pos hr0 hq2
  have hεγ : r / q ^ 2 < ε - γ := by linarith
  have hεγ0 : 0 < ε - γ := by linarith
  set s := 1 / √(ε - γ) with hs
  have hs0 : 0 < s := by positivity
  have hs2 : 1 / s ^ 2 = ε - γ := by
    rw [hs, div_pow, one_pow, Real.sq_sqrt hεγ0.le, one_div_one_div]
  -- Chebyshev threshold
  have hth : ∀ᶠ n : ℕ in atTop, binomLT (cutoff Ns n) η
      ⌈η * (cutoff Ns n : ℝ) - s * √((cutoff Ns n : ℝ) * (η * (1 - η)))⌉₊ ≤ ε - γ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hL : 1 ≤ cutoff Ns n := by
      have h1 : (0 : ℝ) < n * Ns := mul_pos (by exact_mod_cast hn) hNs
      have h2 : (n : ℝ) * Ns ≤ cutoff Ns n := Nat.le_ceil _
      exact_mod_cast (show (0 : ℝ) < cutoff Ns n by linarith)
    rw [← hs2]; exact binomLT_chebyshev hη0 hη1 hs0 hL
  -- the √n coefficient gap
  have hv := vTh_pos hη0 hNs
  have hVr : Vocc η Ns = r * vTh (η * Ns) := Vocc_eq_ratio_mul_vTh hη0 hNs
  have hlt : Vocc η Ns / (ε - γ) < vTh (η * Ns) * q ^ 2 := by
    rw [div_lt_iff₀ hεγ0, hVr]
    have : r < q ^ 2 * (ε - γ) := by rwa [div_lt_iff₀ hq2, mul_comm] at hεγ
    nlinarith
  have hgap : s * √(Vocc η Ns) < √(vTh (η * Ns)) * (-q) := by
    rw [show s * √(Vocc η Ns) = √(Vocc η Ns) / √(ε - γ) by rw [hs]; ring,
      ← Real.sqrt_div (Vocc_nonneg hη0 hη1 hNs)]
    calc √(Vocc η Ns / (ε - γ)) < √(vTh (η * Ns) * q ^ 2) :=
          Real.sqrt_lt_sqrt (div_nonneg (Vocc_nonneg hη0 hη1 hNs) hεγ0.le) hlt
      _ = √(vTh (η * Ns)) * (-q) := by
          rw [Real.sqrt_mul hv.le, Real.sqrt_sq_eq_abs, abs_of_neg hq]
  exact not_candidateConverse_of_threshold hη0 hη1 hNs hγ0 hγ1 hs0.le hth hgap

/-- **Concrete counterexample.** With `η = 9/10`, `N_S = 1` and `ε = Φ(-1) ≈ 0.159` (so
`Φ⁻¹(ε) = -1`), the candidate converse Eq. (4) fails. -/
theorem counterexample : ¬ CandidateConverse (9 / 10) 1 (Φ (-1)) (-1) := by
  apply candidateConverse_false (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := Φ_neg_one_ge
  norm_num
  linarith

/-- `Φ⁻¹(Φ(-1)) = -1`: `-1` is the only `q` with `Φ q = Φ(-1)`. -/
theorem Φ_injective : Function.Injective Φ := Φ_strictMono.injective

/-- **For every `ε < 1/2`** (written as `ε = Φ(q)` with `q = Φ⁻¹(ε) < 0`) and every
`N_S > 0`, the candidate converse fails for all transmissivities `η` close enough to `1`. -/
theorem candidateConverse_false_near_one {q Ns : ℝ} (hq : q < 0) (hNs : 0 < Ns) :
    ∃ η₀ < 1, ∀ η, η₀ < η → η < 1 → ¬ CandidateConverse η Ns (Φ q) q := by
  have hΦ : 0 < Φ q := by
    have h1 := Φ_strictMono (show q - 1 < q by linarith)
    have h0 : 0 ≤ Φ (q - 1) := ENNReal.toReal_nonneg
    linarith
  set c := q ^ 2 * Φ q with hc
  have hc0 : 0 < c := mul_pos (by nlinarith) hΦ
  refine ⟨max (1 - c) 0, max_lt (by linarith) one_pos, fun η hη hη1 => ?_⟩
  have hη0 : 0 < η := lt_of_le_of_lt (le_max_right _ _) hη
  have hηc : 1 - c < η := lt_of_le_of_lt (le_max_left _ _) hη
  apply candidateConverse_false hη0 hη1 hNs hq
  have hηN : 0 < η * Ns := mul_pos hη0 hNs
  rw [div_lt_iff₀ (by linarith)]
  have h1 := mul_pos hc0 hηN
  rw [hc] at h1 hηc
  nlinarith

end QIQCOP
