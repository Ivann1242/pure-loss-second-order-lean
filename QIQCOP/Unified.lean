import QIQCOP.Embed
import QIQCOP.MeanSharp
import QIQCOP.Coherent

/-!
# Unified second-order theorems over the full Fock space

With `x = η N_S/(1-ε)` and `V = (1-η) x g'(x)²`:

* `mean_second_order_sharp_unbounded` (U1): both directions over `UCode`.
* `meanMax`, `meanMax_spec`, `mean_limit`, `meanMax_sharp` (U2): the optimal code size under the
  mean constraint and its exact second-order limit.
* `second_order_asymptotics_unbounded` (U3): the occupation-constraint theorem over `UCode`.
* `coherent_strictly_suboptimal` (U4): countable coherent mixtures are strictly worse for `q < 0`.
-/

open Real Filter Topology
open QIQCOP.Unbounded

namespace QIQCOP

noncomputable section

/-- The operating point `x = η N_S/(1-ε)`. -/
abbrev meanX (η Ns ε : ℝ) : ℝ := η * Ns / (1 - ε)

/-- The coefficient `V = (1-η) x g'(x)²`. -/
abbrev meanV (η Ns ε : ℝ) : ℝ :=
  (1 - η) * meanX η Ns ε * gp (meanX η Ns ε) ^ 2

/-- **U1.** `log₂ M = n g(x) - √(V n ln n) + O(√n)` over all Fock-space codes with finite mean. -/
theorem mean_second_order_sharp_unbounded {η Ns ε : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      (∃ M : ℕ, 1 ≤ M ∧ ∃ C : UCode n M, Summable (fun t : ℕ => (t : ℝ) * C.law t) ∧
        C.mean ≤ n * Ns ∧ 1 - ε ≤ C.success (⟨hη0.le, hη1.le⟩ : η ∈ Set.Icc (0 : ℝ) 1) ∧
        n * g (meanX η Ns ε) - √(meanV η Ns ε * n * Real.log n) - A * √(n : ℝ) ≤
          Real.logb 2 M) ∧
      (∀ M : ℕ, 1 ≤ M → ∀ C : UCode n M, Summable (fun t : ℕ => (t : ℝ) * C.law t) →
        C.mean ≤ n * Ns → 1 - ε ≤ C.success (⟨hη0.le, hη1.le⟩ : η ∈ Set.Icc (0 : ℝ) 1) →
        Real.logb 2 M ≤ n * g (meanX η Ns ε) - √(meanV η Ns ε * n * Real.log n) +
          A * √(n : ℝ)) := by
  obtain ⟨A₁, h₁⟩ := mean_second_order_sharp hη0 hη1 hNs hε0 hε1
  obtain ⟨A₂, h₂⟩ := mean_sharp_cutoff hη0 hη1 hNs hε0 hε1
  refine ⟨max A₁ A₂, ?_⟩
  simp only [meanV, meanX]
  filter_upwards [h₁, h₂, eventually_ge_atTop 1] with n hn₁ hn₂ hn
  have hs := Real.sqrt_nonneg (n : ℝ)
  have k₁ : A₁ * √(n : ℝ) ≤ max A₁ A₂ * √(n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hs
  have k₂ : A₂ * √(n : ℝ) ≤ max A₁ A₂ * √(n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hs
  obtain ⟨⟨L', M, hM, C, hmean, hsucc, hrate⟩, -⟩ := hn₁
  obtain ⟨r, lam, hlam, hmaj, hgap, hbd⟩ := hn₂
  refine ⟨⟨M, hM, C.toUCode, C.toUCode_summable_mean, by rw [C.toUCode_mean]; exact hmean,
    hsucc.trans_eq (C.toUCode_success _).symm, le_trans (by linarith) hrate⟩, ?_⟩
  intro M' hM' C' hsm hmean' hsucc'
  have := unbounded_mean_bound (⟨hη0.le, hη1.le⟩ : η ∈ Set.Icc (0 : ℝ) 1) C' hmaj hlam hsm
    hmean' hgap hsucc' hn
  exact this.trans (hbd.trans (by linarith))

/-- The admissible code sizes under the mean constraint. -/
def meanSet (η Ns ε : ℝ) (n : ℕ) : Set ℕ :=
  {M | 1 ≤ M ∧ ∃ C : UCode n M, Summable (fun t : ℕ => (t : ℝ) * C.law t) ∧
    C.mean ≤ n * Ns ∧ ∃ hη : η ∈ Set.Icc (0 : ℝ) 1, 1 - ε ≤ C.success hη}

/-- **U2.** The largest code size under the mean constraint. -/
def meanMax (η Ns ε : ℝ) (n : ℕ) : ℕ := sSup (meanSet η Ns ε n)

/-- The admissible set is eventually nonempty and bounded, its supremum is attained, and the
supremum obeys the sharp two-sided expansion. -/
theorem meanMax_spec {η Ns ε : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      (meanSet η Ns ε n).Nonempty ∧ BddAbove (meanSet η Ns ε n) ∧
      meanMax η Ns ε n ∈ meanSet η Ns ε n ∧
      |Real.logb 2 (meanMax η Ns ε n) -
        (n * g (meanX η Ns ε) - √(meanV η Ns ε * n * Real.log n))| ≤ A * √(n : ℝ) := by
  obtain ⟨A, hA⟩ := mean_second_order_sharp_unbounded hη0 hη1 hNs hε0 hε1
  refine ⟨A, ?_⟩
  filter_upwards [hA] with n hn
  obtain ⟨⟨M₀, hM₀, C₀, hs₀, hm₀, hc₀, hr₀⟩, hconv⟩ := hn
  have hηI : η ∈ Set.Icc (0 : ℝ) 1 := ⟨hη0.le, hη1.le⟩
  have hmem₀ : M₀ ∈ meanSet η Ns ε n := ⟨hM₀, C₀, hs₀, hm₀, hηI, hc₀⟩
  have hub : ∀ M ∈ meanSet η Ns ε n, Real.logb 2 M ≤
      n * g (meanX η Ns ε) - √(meanV η Ns ε * n * Real.log n) + A * √(n : ℝ) := by
    rintro M ⟨hM, C, hs, hm, hη', hc⟩
    exact hconv M hM C hs hm hc
  have hbdd : BddAbove (meanSet η Ns ε n) := by
    refine ⟨⌈(2 : ℝ) ^ (n * g (meanX η Ns ε) - √(meanV η Ns ε * n * Real.log n) +
      A * √(n : ℝ))⌉₊, fun M hM => ?_⟩
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM.1
    have h := hub M hM
    have h2 : (M : ℝ) ≤ (2 : ℝ) ^ (n * g (meanX η Ns ε) -
        √(meanV η Ns ε * n * Real.log n) + A * √(n : ℝ)) := by
      calc (M : ℝ) = (2 : ℝ) ^ Real.logb 2 M :=
            (Real.rpow_logb (by norm_num) (by norm_num) hMpos).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    exact_mod_cast h2.trans (Nat.le_ceil _)
  have hmem : meanMax η Ns ε n ∈ meanSet η Ns ε n := Nat.sSup_mem ⟨M₀, hmem₀⟩ hbdd
  refine ⟨⟨M₀, hmem₀⟩, hbdd, hmem, ?_⟩
  have hle : M₀ ≤ meanMax η Ns ε n := le_csSup hbdd hmem₀
  have hlog : Real.logb 2 M₀ ≤ Real.logb 2 (meanMax η Ns ε n) :=
    Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hM₀) (by exact_mod_cast hle)
  have hup := hub _ hmem
  rw [abs_le]
  constructor <;> linarith

/-- **U2, sharp form.** -/
theorem meanMax_sharp {η Ns ε : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      |Real.logb 2 (meanMax η Ns ε n) -
        (n * g (meanX η Ns ε) - √(meanV η Ns ε * n * Real.log n))| ≤ A * √(n : ℝ) := by
  obtain ⟨A, hA⟩ := meanMax_spec hη0 hη1 hNs hε0 hε1
  exact ⟨A, hA.mono fun n hn => hn.2.2.2⟩

/-- **U2, exact limit.** -/
theorem mean_limit {η Ns ε : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) * g (meanX η Ns ε) - Real.logb 2 (meanMax η Ns ε n)) /
      √((n : ℝ) * Real.log n)) atTop (𝓝 (√(meanV η Ns ε))) := by
  obtain ⟨A, hA⟩ := meanMax_sharp hη0 hη1 hNs hε0 hε1
  have hV : 0 ≤ meanV η Ns ε := by
    have hx : 0 ≤ meanX η Ns ε := div_nonneg (mul_pos hη0 hNs).le (by linarith)
    exact mul_nonneg (mul_nonneg (by linarith) hx) (sq_nonneg _)
  have hlogtend : Tendsto (fun n : ℕ => √(Real.log n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ => A / √(Real.log n)) atTop (𝓝 0) :=
    hlogtend.const_div_atTop A
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hA, eventually_ge_atTop 3] with n hn hn3
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hsl : 0 < √(Real.log n) := Real.sqrt_pos.2 hlogpos
  have hT : √((n : ℝ) * Real.log n) = √(n : ℝ) * √(Real.log n) := Real.sqrt_mul hn0.le _
  have hVT : √(meanV η Ns ε * n * Real.log n) =
      √(meanV η Ns ε) * √((n : ℝ) * Real.log n) := by
    rw [mul_assoc, Real.sqrt_mul hV]
  rw [hVT] at hn
  have hTpos : 0 < √((n : ℝ) * Real.log n) := by rw [hT]; positivity
  set T := √((n : ℝ) * Real.log n) with hTdef
  have e : ((n : ℝ) * g (meanX η Ns ε) - Real.logb 2 (meanMax η Ns ε n)) / T - √(meanV η Ns ε) =
      -(Real.logb 2 (meanMax η Ns ε n) -
        (n * g (meanX η Ns ε) - √(meanV η Ns ε) * T)) / T := by
    field_simp
    ring
  rw [e, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hTpos, div_le_iff₀ hTpos]
  refine hn.trans (le_of_eq ?_)
  rw [hT]
  field_simp

/-- **U3.** The occupation-constraint second-order theorem over all Fock-space codes. -/
theorem second_order_asymptotics_unbounded {η Ns δ q B : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hNs : 0 < Ns) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hB : 0 ≤ B) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      (∃ M : ℕ, 1 ≤ M ∧ ∃ C : UCode n M,
        1 - (1 - δ) * Φ q ≤ C.success (⟨hη0.le, hη1.le⟩ : η ∈ Set.Icc (0 : ℝ) 1) ∧
        C.leak (cutoff Ns n) ≤ δ ∧
        n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) - A * Real.log n ≤ Real.logb 2 M) ∧
      (∀ M : ℕ, 1 ≤ M → ∀ C : UCode n M, C.leak (cutoff Ns n) ≤ δ + B / √(n : ℝ) →
        1 - (1 - δ) * Φ q ≤ C.success (⟨hη0.le, hη1.le⟩ : η ∈ Set.Icc (0 : ℝ) 1) →
        Real.logb 2 M ≤ n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) + A * Real.log n) := by
  obtain ⟨A₁, h₁⟩ := second_order_asymptotics (q := q) hη0 hη1 hNs hδ0 hδ1 hB
  obtain ⟨A₂, -, h₂⟩ := unbounded_converse_log (q := q) hη0 hη1 hNs hδ0 hδ1 hB
  refine ⟨max A₁ A₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_ge_atTop 1] with n hn₁ hn₂ hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg hnr
  have k₁ : A₁ * Real.log n ≤ max A₁ A₂ * Real.log n :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hl
  have k₂ : A₂ * Real.log n ≤ max A₁ A₂ * Real.log n :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hl
  obtain ⟨⟨L', M, hM, -, ⟨C, hsucc, hleak⟩, hrate⟩, -⟩ := hn₁
  refine ⟨⟨M, hM, C.toUCode, hsucc.trans_eq (C.toUCode_success _).symm,
    by rw [C.toUCode_leak]; exact hleak, le_trans (by linarith) hrate⟩, ?_⟩
  intro M' hM' C' hleak' hsucc'
  exact (hn₂ M' C' hM' hleak' hsucc').trans (by linarith)

/-- `A log n < τ √n` eventually. -/
lemma eventually_log_lt_sqrt (A : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop, A * Real.log n < τ * √(n : ℝ) := by
  have hlo := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hc : 0 < τ / (|A| + 1) := by positivity
  filter_upwards [hlo.def hc, eventually_ge_atTop 1] with n hn hn1
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hl : 0 ≤ Real.log n := Real.log_nonneg hnr
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  simp only [Function.comp_apply, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg hl,
    abs_of_pos hs] at hn
  have h1 : A * Real.log n ≤ |A| * Real.log n :=
    mul_le_mul_of_nonneg_right (le_abs_self A) hl
  have h2 : |A| * Real.log n ≤ |A| * (τ / (|A| + 1) * √(n : ℝ)) :=
    mul_le_mul_of_nonneg_left hn (abs_nonneg A)
  have h3 : |A| * (τ / (|A| + 1) * √(n : ℝ)) < τ * √(n : ℝ) := by
    have hA1 : 0 < |A| + 1 := by positivity
    have e : |A| * (τ / (|A| + 1) * √(n : ℝ)) = (|A| / (|A| + 1)) * (τ * √(n : ℝ)) := by
      field_simp
    rw [e]
    have hlt : |A| / (|A| + 1) < 1 := by
      rw [div_lt_one hA1]; linarith
    have hp : 0 < τ * √(n : ℝ) := by positivity
    nlinarith
  linarith

/-- **U4.** For `q < 0`, general finite-support codes strictly beat every countable mixture of
coherent states of energy at most `⌈n N_S⌉`, for all large `n`. -/
theorem coherent_strictly_suboptimal {η Ns q : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hq : q < 0) :
    ∀ᶠ n : ℕ in atTop, ∃ M : ℕ, 1 ≤ M ∧
      (∃ C : Code n (cutoff Ns n) M, 1 - Φ q ≤ C.success η) ∧
      ∀ (M' : ℕ) (C' : UCode n M'), 1 ≤ M' → C'.IsCoherentMixture (cutoff Ns n) →
        1 - Φ q ≤ C'.success (⟨hη0.le, hη1.le⟩ : η ∈ Set.Icc (0 : ℝ) 1) → M' < M := by
  have hsep := coherent_separation hη0 hη1 hNs hq
  set τ := (q * √(Vocc η Ns) - q * √(η * Ns) * gp (η * Ns)) / 2 with hτdef
  have hτ : 0 < τ := by rw [hτdef]; linarith
  obtain ⟨A, hA⟩ := second_order_asymptotics_cutoff (q := q) hη0 hη1 hNs
  have hconv := coherent_converse (q := q) hη0 hη1 hNs hτ
  filter_upwards [hA, hconv, eventually_log_lt_sqrt A hτ, eventually_ge_atTop 1]
    with n hn₁ hn₂ hlog hn
  obtain ⟨⟨M, hM, hC, hrate⟩, -⟩ := hn₁
  refine ⟨M, hM, hC, fun M' C' hM' hcoh hsucc => ?_⟩
  have hub := hn₂ M' C' hM' hcoh hsucc
  have hgap : q * √(Vocc η Ns) = q * √(η * Ns) * gp (η * Ns) + 2 * τ := by
    rw [hτdef]; ring
  have hlt : Real.logb 2 M' < Real.logb 2 M := by
    have e : (q * √(Vocc η Ns)) * √(n : ℝ) =
        (q * √(η * Ns) * gp (η * Ns) + τ) * √(n : ℝ) + τ * √(n : ℝ) := by
      rw [hgap]; ring
    linarith
  have hM'0 : (0 : ℝ) < M' := by exact_mod_cast hM'
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have := (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2) hM'0 hM0).1 hlt
  exact_mod_cast this

end

end QIQCOP
