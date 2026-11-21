import QIQCOP.MeanAch
import QIQCOP.MeanConv

/-!
# Second-order asymptotics under a mean photon-number constraint

`mean_second_order`: with `x_ε = η N_S/(1-ε)` and `V_ε = (1-η) x_ε g'(x_ε)²`, for every
`κ ∈ (0,1)` and all large `n`,

  `n g(x_ε) - √((1+κ) V_ε n ln n) ≤ log₂ M*(n, ε) ≤ n g(x_ε) - √((1-κ) V_ε n ln n)`,

where `M*` is the largest code size with mean photon number `≤ n N_S` and success `≥ 1 - ε`.
-/

open Real Filter

namespace QIQCOP

theorem mean_second_order {η Ns ε κ : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (∃ L' M : ℕ, 1 ≤ M ∧ ∃ C : Code n L' M, C.meanPhotons ≤ n * Ns ∧ 1 - ε ≤ C.success η ∧
        n * g (η * Ns / (1 - ε))
          - √((1 + κ) * ((1 - η) * (η * Ns / (1 - ε)) * gp (η * Ns / (1 - ε)) ^ 2) * n *
              Real.log n)
          ≤ Real.logb 2 M) ∧
      (∀ (L' M : ℕ) (C : Code n L' M), 1 ≤ M → C.meanPhotons ≤ n * Ns → 1 - ε ≤ C.success η →
        Real.logb 2 M ≤ n * g (η * Ns / (1 - ε))
          - √((1 - κ) * ((1 - η) * (η * Ns / (1 - ε)) * gp (η * Ns / (1 - ε)) ^ 2) * n *
              Real.log n)) :=
  (mean_ach hη0 hη1 hNs hε0 hε1 hκ0 hκ1).and (mean_converse hη0 hη1 hNs hε0 hε1 hκ0 hκ1)

end QIQCOP
