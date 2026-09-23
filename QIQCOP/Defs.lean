import Mathlib

/-!
# Definitions for the QIQCOP pure-loss second-order problem

Problem: <https://qiqc-op.com/problem/op_89fb664ba06ba5de/>.
All logarithms are base two (`Real.logb 2`), matching the problem statement.
-/

open Real

noncomputable section

namespace QIQCOP

/-- Thermal entropy `g(x) = (x+1) log₂(x+1) - x log₂ x`, Eq. (3) of the problem. -/
def g (x : ℝ) : ℝ := (x + 1) * logb 2 (x + 1) - x * logb 2 x

/-- `g'(x) = log₂(1 + 1/x)`. -/
def gp (x : ℝ) : ℝ := logb 2 (1 + 1 / x)

/-- Thermal entropy variance `v(x) = x(x+1)[log₂(x+1) - log₂ x]²`, Eq. (3) of the problem. -/
def vTh (x : ℝ) : ℝ := x * (x + 1) * (logb 2 (x + 1) - logb 2 x) ^ 2

/-- Fixed-photon dispersion `V_occ = η(1-η) N_S [log₂(1 + 1/(η N_S))]²` from the proof. -/
def Vocc (η Ns : ℝ) : ℝ := η * (1 - η) * Ns * gp (η * Ns) ^ 2

/-- Photon cutoff `L = ⌈n N_S⌉`. -/
def cutoff (Ns : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) * Ns⌉₊

/-- Dimension of the exactly-`k`-photon sector of `n` modes, `D_{n,k} = C(n+k-1, k)`. -/
def sectorDim (n k : ℕ) : ℝ := ((n + k - 1).choose k : ℕ)

/-- Binomial probability `Pr{K = k}` for `K ~ Bin(L, η)`. -/
def binomPMF (L : ℕ) (η : ℝ) (k : ℕ) : ℝ := (L.choose k : ℝ) * η ^ k * (1 - η) ^ (L - k)

/-- `Pr{K < t}` for `K ~ Bin(L, η)`. -/
def binomLT (L : ℕ) (η : ℝ) (t : ℕ) : ℝ := ∑ j ∈ Finset.range t, binomPMF L η j

/-- Eq. (7) of proof.md: in a `√n` window around `n x` (`x = η N_S`),
`log₂ D_{n,k} ≥ n g(x) + (k - n x) g'(x) - O(log n)`. -/
def StirlingExpansion (η Ns : ℝ) : Prop :=
  ∀ R : ℝ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ k : ℕ,
    |(k : ℝ) - n * (η * Ns)| ≤ R * √(n : ℝ) →
      n * g (η * Ns) + ((k : ℝ) - n * (η * Ns)) * gp (η * Ns) - B * log n ≤
        logb 2 (sectorDim n k)

end QIQCOP
