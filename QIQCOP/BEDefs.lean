import QIQCOP.Gaussian

/-!
# Berry–Esseen statement for the binomial distribution

`BinomBE η` is the uniform Berry–Esseen bound for `Bin(L, η)`:
`|Pr{K < t} - Φ((t - ηL)/√(Lη(1-η)))| ≤ C/√L` for all `L ≥ 1` and all `t`.
It is proved in `QIQCOP/BerryEsseen.lean` and used in `QIQCOP/LogMain.lean`.
-/

open Real

namespace QIQCOP

/-- Uniform Berry–Esseen bound for the binomial distribution with success probability `η`. -/
def BinomBE (η : ℝ) : Prop :=
  ∃ C : ℝ, ∀ L : ℕ, 1 ≤ L → ∀ t : ℕ,
    |binomLT L η t - Φ (((t : ℝ) - η * L) / √((L : ℝ) * (η * (1 - η))))| ≤ C / √(L : ℝ)

end QIQCOP
