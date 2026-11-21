import QIQCOP.LogConv
import QIQCOP.LogAch

/-!
# Second-order expansion with `O(log n)` remainder

Assuming the Berry–Esseen bound `BinomBE η` for the binomial distribution, the optimal code size
over `n` uses of the pure-loss channel satisfies, for every `q ∈ ℝ`,
`log₂ M* = n g(η N_S) + q √V_occ √n + O(log n)` at error `ε = (1 - δ) Φ(q)`:

* `second_order_log`: codes in any `≤ L'`-photon space with leakage above `⌈n N_S⌉` at most
  `δ` (existence) / at most `δ + B/√n` (converse).
* `second_order_log_cutoff`: codes in the strict cutoff space, `ε = Φ(q)`.
-/

open Real Filter

namespace QIQCOP

open SecondOrderLog

/-- Second-order expansion with O(log n) remainder, assuming Berry–Esseen for Bin(L, η).
Codes live in the ≤ L'-photon space (any L'); their inputs may have average weight at most
δ + B/√n above the cutoff ⌈n N_S⌉. With ε = (1 - δ) Φ(q):
  log₂ M* = n g(η N_S) + q √(V_occ) √n + O(log n). -/
theorem second_order_log {η Ns δ q B : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hB : 0 ≤ B) (hBE : BinomBE η) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      (∃ L' M : ℕ, 1 ≤ M ∧ cutoff Ns n ≤ L' ∧
        (∃ C : Code n L' M, 1 - (1 - δ) * Φ q ≤ C.success η ∧ C.leak (cutoff Ns n) ≤ δ) ∧
        n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) - A * Real.log n ≤ Real.logb 2 M) ∧
      (∀ (L' M : ℕ) (C : Code n L' M), 1 ≤ M →
        C.leak (cutoff Ns n) ≤ δ + B / √(n : ℝ) → 1 - (1 - δ) * Φ q ≤ C.success η →
          Real.logb 2 M ≤ n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) + A * Real.log n) := by
  obtain ⟨A₁, hA₁0, hA₁⟩ := ach_log (q := q) hη0 hη1 hNs hδ0 hδ1 hBE
  obtain ⟨A₂, hA₂0, hA₂⟩ := converse_log (q := q) hη0 hη1 hNs hδ0 hδ1 hB hBE
  refine ⟨A₁ + A₂, ?_⟩
  filter_upwards [hA₁, hA₂, eventually_ge_atTop 1] with n h1 h2 hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have e1 : A₁ * Real.log n ≤ (A₁ + A₂) * Real.log n :=
    mul_le_mul_of_nonneg_right (by linarith) hlog
  have e2 : A₂ * Real.log n ≤ (A₁ + A₂) * Real.log n :=
    mul_le_mul_of_nonneg_right (by linarith) hlog
  refine ⟨?_, ?_⟩
  · obtain ⟨L', M, hM, hL, hC, hb⟩ := h1
    exact ⟨L', M, hM, hL, hC, by linarith⟩
  · intro L' M C hM hl hs
    have := h2 L' M C hM hl hs
    linarith

/-- **Strict photon cutoff** (`δ = 0`, codes in the `≤ ⌈n N_S⌉`-photon space): with `ε = Φ(q)`,
`log₂ M* = n g(η N_S) + q √(V_occ) √n + O(log n)`, assuming Berry–Esseen for `Bin(L, η)`. -/
theorem second_order_log_cutoff {η Ns q : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hBE : BinomBE η) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      (∃ M : ℕ, 1 ≤ M ∧ (∃ C : Code n (cutoff Ns n) M, 1 - Φ q ≤ C.success η) ∧
        n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) - A * Real.log n ≤ Real.logb 2 M) ∧
      (∀ (M : ℕ) (C : Code n (cutoff Ns n) M), 1 ≤ M → 1 - Φ q ≤ C.success η →
        Real.logb 2 M ≤ n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) + A * Real.log n) := by
  obtain ⟨A₁, hA₁0, hA₁⟩ := ach_log_cutoff (q := q) hη0 hη1 hNs hBE
  obtain ⟨A₂, hA₂0, hA₂⟩ := converse_log (δ := 0) (q := q) (B := 0) hη0 hη1 hNs le_rfl one_pos
    le_rfl hBE
  refine ⟨A₁ + A₂, ?_⟩
  filter_upwards [hA₁, hA₂, eventually_ge_atTop 1] with n h1 h2 hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have e1 : A₁ * Real.log n ≤ (A₁ + A₂) * Real.log n :=
    mul_le_mul_of_nonneg_right (by linarith) hlog
  have e2 : A₂ * Real.log n ≤ (A₁ + A₂) * Real.log n :=
    mul_le_mul_of_nonneg_right (by linarith) hlog
  refine ⟨?_, ?_⟩
  · obtain ⟨M, hM, hC, hb⟩ := h1
    exact ⟨M, hM, hC, by linarith⟩
  · intro M C hM hs
    have := h2 _ M C hM (by rw [C.leak_self]; simp) (by simpa using hs)
    linarith

end QIQCOP
