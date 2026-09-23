import QIQCOP.Main
import QIQCOP.GaussianInv
import QIQCOP.BinomialCLT

/-!
# The candidate converse fails for *all* parameters with `ε < 1/2`

Using the de Moivre–Laplace threshold (`binomLT_tendsto`) instead of Chebyshev, the achievable
`√n` coefficient can be made arbitrarily close to the sharp `√V_occ · Φ⁻¹(ε)`. Because
`V_occ < v(η N_S)`, it beats the conjectured `√v · Φ⁻¹(ε)` for every `0 < η < 1`, `N_S > 0` and
`0 < ε < 1/2`.
-/

open Real Filter Topology

namespace QIQCOP

lemma tendsto_cutoff {Ns : ℝ} (hNs : 0 < Ns) : Tendsto (cutoff Ns) atTop atTop := by
  unfold cutoff
  exact tendsto_nat_ceil_atTop.comp
    (tendsto_natCast_atTop_atTop.atTop_mul_const hNs)

lemma Vocc_pos {η Ns : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns) : 0 < Vocc η Ns := by
  have := gp_pos (mul_pos hη0 hNs)
  unfold Vocc
  have : 0 < 1 - η := by linarith
  positivity

/-- **General disproof**, given the de Moivre–Laplace threshold. -/
theorem candidateConverse_false_all_of_clt {η Ns q : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hNs : 0 < Ns) (hq : q < 0)
    (hclt : ∀ z : ℝ, Tendsto (fun L : ℕ => binomLT L η ⌈η * L + z * √(L * (η * (1 - η)))⌉₊)
      atTop (𝓝 (Φ z))) :
    ¬ CandidateConverse η Ns (Φ q) q := by
  have hV := Vocc_pos hη0 hη1 hNs
  have hv := vTh_pos hη0 hNs
  have hVv := Vocc_lt_vTh hη0 hη1 hNs
  have hsV : 0 < √(Vocc η Ns) := Real.sqrt_pos.2 hV
  have hsVv : √(Vocc η Ns) < √(vTh (η * Ns)) := Real.sqrt_lt_sqrt hV.le hVv
  -- ρ = √v / √V_occ > 1, and the slack s ∈ (-q, -q ρ)
  set ρ := √(vTh (η * Ns)) / √(Vocc η Ns) with hρ
  have hρ1 : 1 < ρ := by rw [hρ, one_lt_div hsV]; exact hsVv
  set s := -q * (1 + ρ) / 2 with hs
  have hs0 : 0 ≤ s := by rw [hs]; nlinarith
  have hsq : -s < q := by rw [hs]; nlinarith
  have hgap : s * √(Vocc η Ns) < √(vTh (η * Ns)) * (-q) := by
    have h1 : s < -q * ρ := by rw [hs]; nlinarith
    have h2 : -q * ρ * √(Vocc η Ns) = √(vTh (η * Ns)) * (-q) := by
      rw [hρ]; field_simp
    nlinarith
  -- threshold with Φ(-s) < Φ(q)
  have hΦ : Φ (-s) < Φ q := Φ_strictMono hsq
  set γ := min ((Φ q - Φ (-s)) / 2) 1 with hγ
  have hγ0 : 0 < γ := lt_min (by linarith) one_pos
  have hγ1 : γ ≤ 1 := min_le_right _ _
  have hγle : γ ≤ (Φ q - Φ (-s)) / 2 := min_le_left _ _
  have hlt : Φ (-s) < Φ q - γ := by linarith
  have hth : ∀ᶠ n : ℕ in atTop, binomLT (cutoff Ns n) η
      ⌈η * (cutoff Ns n : ℝ) - s * √((cutoff Ns n : ℝ) * (η * (1 - η)))⌉₊ ≤ Φ q - γ := by
    have h := ((hclt (-s)).comp (tendsto_cutoff hNs)).eventually (gt_mem_nhds hlt)
    filter_upwards [h] with n hn
    simp only [Function.comp_apply, neg_mul, ← sub_eq_add_neg] at hn
    exact hn.le
  exact not_candidateConverse_of_threshold hη0 hη1 hNs hγ0 hγ1 hs0 hth hgap

/-- **General disproof (all parameters).** For every `0 < η < 1`, `N_S > 0` and `q < 0`,
the candidate converse fails at `ε = Φ(q)`. -/
theorem candidateConverse_false_all {η Ns q : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hq : q < 0) : ¬ CandidateConverse η Ns (Φ q) q :=
  candidateConverse_false_all_of_clt hη0 hη1 hNs hq (binomLT_tendsto hη0 hη1)

/-- **The open problem, answered.** For every `0 < η < 1`, `N_S > 0` and `0 < ε < 1/2`,
`Φ⁻¹(ε)` exists (and is unique by `Φ_injective`), and Eq. (4) with `q = Φ⁻¹(ε)` fails. -/
theorem conjecture_false_all {η Ns ε : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    (∃ q, Φ q = ε) ∧ ∀ q, Φ q = ε → ¬ CandidateConverse η Ns ε q := by
  refine ⟨exists_Φ_eq hε0 (by linarith), fun q hqε => ?_⟩
  subst hqε
  exact candidateConverse_false_all hη0 hη1 hNs (Φ_lt_half_iff.1 hε)

end QIQCOP
