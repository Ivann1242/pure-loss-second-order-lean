# QIQCOP op_89fb664ba06ba5de: Lean verifier

Authors: Yue Tu and Yifan Jing (University of Michigan). License: Apache-2.0.

A Lean 4 + Mathlib formalization of the disproof ([proof note](https://github.com/Naixu-Guo/quantum-open-problems/blob/main/database/proofs/pure-loss-second-order.md)) of the candidate pure-loss
second-order converse, Eq. (4) of <https://qiqc-op.com/problem/op_89fb664ba06ba5de/>.
Build it with `lake build`.

## Main results (`QIQCOP/MainGeneral.lean`, `QIQCOP/Main.lean`)

| Theorem | Statement |
|---|---|
| `conjecture_false_all` | **For every `0<η<1`, `N_S>0` and `0<ε<1/2`**: `Φ⁻¹(ε)` exists (and is unique), and `¬ CandidateConverse η N_S ε Φ⁻¹(ε)` |
| `candidateConverse_false` | For `0<η<1`, `N_S>0`, `q<0` with `(1-η)/(1+ηN_S) < q²ε`: `¬ CandidateConverse η N_S ε q` |
| `counterexample` | `¬ CandidateConverse (9/10) 1 (Φ(-1)) (-1)`: a concrete instance with `ε = Φ(-1) ≈ 0.159`, `Φ⁻¹(ε) = -1` |
| `candidateConverse_false_near_one` | For every `q = Φ⁻¹(ε) < 0` (every `ε < 1/2`) and `N_S > 0`, the converse fails for all `η` close enough to `1` |
| `achievability_of_threshold` | Given a threshold with `Pr{K < ηL − s√(La)} ≤ ε−γ`: for large `n`, a code with success `≥ 1−ε` and `log₂ M ≥ n g(ηN_S) − √n·s√V_occ − O(log n)` |

`CandidateConverse η Ns ε q` is Eq. (4) with `q` in place of `Φ⁻¹(ε)`. It is asserted for every
`Code n ⌈nN_S⌉ M`, meaning inputs are density matrices on the space of at most `⌈nN_S⌉` photons in
`n` modes, and the decoder is any POVM. Such codes meet the problem's occupation constraint
Eq. (2) with `δ_n = 0`, so each satisfies `M ≤ M*_occ`. Hence Eq. (4) implies `CandidateConverse`,
and its negation refutes Eq. (4). `Φ` is the standard normal CDF, defined through Mathlib's
`gaussianReal 0 1`, and `Φ_injective` makes `q = Φ⁻¹(ε)` unique.

The build has no `sorry`, `admit` or custom `axiom`. `#print axioms` on the main theorems
reports only `propext`, `Classical.choice` and `Quot.sound`.

## Converse and constant leakage (`QIQCOP/ConverseMain.lean`, `QIQCOP/LeakAch.lean`, `QIQCOP/LeakMain.lean`)

| Theorem | Statement |
|---|---|
| `converse_finite` | Finite-blocklength converse: a code with leakage `≤ δ` above `L₀` photons and success `≥ 1−ε` has `M ≤ C(n+r,r) / (√(1−ε) − √((1−δ)·Pr{K>r} + δ))²`, `K ~ Bin(L₀, η)` |
| `converse_second_order` | If `ε < (1−δ)Φ(z)`: for large `n`, every code with leakage `≤ δ` (inputs in the `≤ L'`-photon space, any `L'`) has `log₂ M ≤ n g(ηN_S) + (z√V_occ + τ)√n` |
| `second_order_exact` | Strict cutoff, `ε = Φ(q)`, `q < 0`: for large `n` a code with `log₂ M ≥ n g + (q√V_occ − τ)√n` exists, and every code has `log₂ M ≤ n g + (q√V_occ + τ)√n` |
| `exists_leakCode`, `leak_achievability` | Two-level condensate codes `(1−δ)|u;L₀⟩⟨u;L₀| + δ|u;L'⟩⟨u;L'|` and their second-order achievability |
| `leak_second_order_exact` | Leakage `δ ∈ [0,1)`, `ε = (1−δ)Φ(q)`, `q < 0`: the same two-sided statement, i.e. coefficient `√V_occ · Φ⁻¹(ε/(1−δ))` |

## Second-order asymptotics with `O(log n)` remainder (`QIQCOP/Final.lean`)

| Theorem | Statement |
|---|---|
| `binomBE` (`BerryEsseen.lean`, `BE/`) | Berry–Esseen for the binomial: `|Pr{Bin(L,η) < t} − Φ((t−ηL)/√(Lη(1−η)))| ≤ C/√L` for all `L ≥ 1`, `t`; proved from scratch |
| `second_order_asymptotics` | For `δ ∈ [0,1)`, `B ≥ 0`, any real `q`, `ε = (1−δ)Φ(q)`: for large `n` a code with leakage `≤ δ` and `log₂ M ≥ n g + q√V_occ√n − A log n` exists, and every code with leakage `≤ δ + B/√n` has `log₂ M ≤ n g + q√V_occ√n + A log n` |
| `second_order_asymptotics_cutoff` | The same for codes with inputs in the `≤ ⌈nN_S⌉`-photon space (`δ = 0`) |

## General photon-number constraints (`QIQCOP/LawCode.lean`, `QIQCOP/MeanMain.lean`)

| Theorem | Statement |
|---|---|
| `converse_law`, `exists_lawCode` | Finite-blocklength converse and achievability for an arbitrary photon-number law `P` of the input (codewords `∑_ℓ P(ℓ) |u;ℓ⟩⟨u;ℓ|`) |
| `quantile_ach`, `quantile_conv` | Quantile principle: if `Pr{K_P < t} ≤ ε − γ` a code with law `P` and `M ≥ γ D_{n,t}/e − 1` exists; if `Pr{K_P ≤ r} ≥ ε + γ` every code with law `P` has `M ≤ 4γ⁻² C(n+r,r)` |
| `binomGT_le_linear` (`Majorant.lean`) | Linear majorant: `Pr{Bin(ℓ,η) > r} ≤ ℓ/λ_r`, `λ_r = (r + √((1−κ) log r)·√((1−η) r))/η`, for all `ℓ` and large `r` |
| `mean_second_order` | Mean photon-number constraint `≤ n N_S`: for every `κ ∈ (0,1)` and large `n`, a code with `log₂ M ≥ n g(x_ε) − √((1+κ) V_ε n ln n)` exists and every code has `log₂ M ≤ n g(x_ε) − √((1−κ) V_ε n ln n)`, where `x_ε = ηN_S/(1−ε)`, `V_ε = (1−η) x_ε g'(x_ε)²` |

Supporting files: `ProjectorBound.lean` (success `≤ (√(D/M) + √q)²`), `Counting.lean` (photon
counting in the Heisenberg picture, binomial tail monotonicity, `dim = C(n+r,r)`),
`StirlingUpper.lean` (`log₂ C(n+k,k) ≤ n g(x) + (k − n x) g'(x)`, threshold asymptotics).
Not formalized: input states with unbounded photon number, and the equivalence of the Kraus
form with the beam-splitter definition.

## Modeling choice (the one place physics enters)

`lossChannel` (`QIQCOP/Fock.lean`) is the `n`-mode pure-loss channel `𝒩_η^{⊗n}` in its standard
Fock-basis operator-sum form, restricted to the `≤ L`-photon space. Pure loss never increases
photon number, so this subspace is invariant:

`A_ℓ |m⟩ = ∏ⱼ √(C(mⱼ,ℓⱼ) η^{mⱼ−ℓⱼ} (1−η)^{ℓⱼ}) |m−ℓ⟩`.

Trace preservation is proved (`lossKraus_complete`). The equivalence of this Kraus form with the
beam-splitter definition in Eq. (1) is the standard textbook derivation. It is not formalized,
because Mathlib has no infinite-dimensional Fock space.

## Differences from the paper proof (all make the formal statement easier to check)

* **Random codebook.** The paper proof averages over Haar-random directions on the complex sphere.
  Here the directions come from a finite ensemble: amplitudes `√(rⱼ/R)`, where `r` is a
  composition of `R`, and phases that are `N`-th roots of unity. Its overlap moment is at most
  `e / C(n+t−1,t)` (`Ensemble.lean`), compared with exactly `1/C(n+t−1,t)` for Haar. The extra
  factor `e` only changes `log₂ M` by a constant.
* **Threshold.** For the general theorem, the threshold `t_n` comes from de Moivre–Laplace
  (`BinomialCLT.lean`: characteristic functions, Lévy continuity and Portmanteau from Mathlib),
  not Berry–Esseen. The achieved `√n` coefficient is `−s·√V_occ` for any `s > −Φ⁻¹(ε)`, which
  comes arbitrarily close to the sharp value and beats `√v·Φ⁻¹(ε)` because `V_occ < v`. The
  older Chebyshev version (`candidateConverse_false`, `counterexample`) is kept. The exact
  `O(log n)` form of (T) and the converse half (§§3–4 of the proof note), are not formalized.

## File map

| File | Content |
|---|---|
| `Defs.lean` | `g`, `g'`, `v`, `V_occ`, cutoff, `D_{n,k}`, binomial distribution, Stirling statement |
| `Dispersion.lean` | `V_occ = (1−η)/(1+ηN_S)·v` |
| `Asymptotic.lean` | `δ√n ≤ K log n` fails eventually |
| `Sector.lean` | Fock sectors, stars and bars `#sector = C(n+k−1,k)` |
| `Fock.lean` | loss channel, condensates `|u;k⟩`, `⟨u;k|v;k⟩ = ⟨u|v⟩^k`, loss identity (2) |
| `GramBound.lean` | SRM Gram estimate (4) |
| `Polar.lean` | isometric polar factor, giving the SRM measurement vectors |
| `Ensemble.lean` | finite ensemble moment bound; averaging over codebooks |
| `Code.lean` | codes, the condensate code, finite-block achievability (5) |
| `Binomial.lean` | binomial facts, Chebyshev threshold |
| `Stirling.lean` | Stirling + Taylor lower bound (7) |
| `Gaussian.lean` | `Φ`, strict monotonicity, `1/10 ≤ Φ(−1) < 1` |
| `Main.lean` | achievability from any threshold, the Chebyshev disproof |
| `BinomialCLT.lean` | `Pr{K < ηL + z√(Lη(1−η))} → Φ(z)` |
| `GaussianInv.lean` | `Φ` continuous, `Φ 0 = 1/2`, `Φ⁻¹` exists |
| `MainGeneral.lean` | the disproof for all parameters |
