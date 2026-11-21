import QIQCOP.BerryEsseen
import QIQCOP.LogMain

/-!
# Second-order asymptotics with an `O(log n)` remainder

The unconditional statements, obtained by combining the Berry–Esseen bound for the binomial
distribution (`binomBE`) with `second_order_log`.
-/

open Real Filter

namespace QIQCOP

/-- **Second-order asymptotics under the occupation constraint.** Codes live in the
`≤ L'`-photon space for an arbitrary `L'`; their inputs may have average weight at most
`δ + B/√n` above the cutoff `⌈n N_S⌉`. With `ε = (1 - δ) Φ(q)`, i.e. `q = Φ⁻¹(ε/(1-δ))`,
`log₂ M* = n g(η N_S) + q √V_occ √n + O(log n)`. -/
theorem second_order_asymptotics {η Ns δ q B : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hB : 0 ≤ B) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      (∃ L' M : ℕ, 1 ≤ M ∧ cutoff Ns n ≤ L' ∧
        (∃ C : Code n L' M, 1 - (1 - δ) * Φ q ≤ C.success η ∧ C.leak (cutoff Ns n) ≤ δ) ∧
        n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) - A * Real.log n ≤ Real.logb 2 M) ∧
      (∀ (L' M : ℕ) (C : Code n L' M), 1 ≤ M →
        C.leak (cutoff Ns n) ≤ δ + B / √(n : ℝ) → 1 - (1 - δ) * Φ q ≤ C.success η →
          Real.logb 2 M ≤ n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) + A * Real.log n) :=
  second_order_log hη0 hη1 hNs hδ0 hδ1 hB (binomBE hη0 hη1)

/-- **Strict cutoff.** For codes with inputs in the `≤ ⌈n N_S⌉`-photon space and `ε = Φ(q)`,
`log₂ M* = n g(η N_S) + q √V_occ √n + O(log n)`. -/
theorem second_order_asymptotics_cutoff {η Ns q : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hNs : 0 < Ns) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      (∃ M : ℕ, 1 ≤ M ∧ (∃ C : Code n (cutoff Ns n) M, 1 - Φ q ≤ C.success η) ∧
        n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) - A * Real.log n ≤ Real.logb 2 M) ∧
      (∀ (M : ℕ) (C : Code n (cutoff Ns n) M), 1 ≤ M → 1 - Φ q ≤ C.success η →
        Real.logb 2 M ≤ n * g (η * Ns) + q * √(Vocc η Ns) * √(n : ℝ) + A * Real.log n) :=
  second_order_log_cutoff hη0 hη1 hNs (binomBE hη0 hη1)

end QIQCOP
