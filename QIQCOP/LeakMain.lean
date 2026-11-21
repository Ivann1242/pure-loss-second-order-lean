import QIQCOP.ConverseMain
import QIQCOP.LeakAch

/-!
# Second-order coefficient with a constant leakage above the photon cutoff

Codes live in the `≤ L'`-photon space for an arbitrary `L'`, and their inputs may carry average
weight at most `δ` above the cutoff `⌈n N_S⌉`. For `q < 0` and error `ε = (1 - δ) Φ(q)`, i.e.
`q = Φ⁻¹(ε / (1 - δ))`, the optimal `log₂ M` is `n g(η N_S) + q √V_occ √n + o(√n)`:
both the existence of codes and the bound for all codes are proved.
-/

open Real Filter

namespace QIQCOP

lemma leakAbove_eq_leak {n L M : ℕ} (C : Code n L M) (L₀ : ℕ) : leakAbove C L₀ = C.leak L₀ := rfl

/-- **Exact second-order coefficient with constant leakage `δ`.** -/
theorem leak_second_order_exact {η Ns δ q : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hq : q < 0) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop,
      (∃ L' M : ℕ, 1 ≤ M ∧ cutoff Ns n ≤ L' ∧
        (∃ C : Code n L' M, 1 - (1 - δ) * Φ q ≤ C.success η ∧ C.leak (cutoff Ns n) ≤ δ) ∧
        n * g (η * Ns) + (q * √(Vocc η Ns) - τ) * √(n : ℝ) ≤ logb 2 M) ∧
      (∀ (L' M : ℕ) (C : Code n L' M), 1 ≤ M → C.leak (cutoff Ns n) ≤ δ →
        1 - (1 - δ) * Φ q ≤ C.success η →
          logb 2 M ≤ n * g (η * Ns) + (q * √(Vocc η Ns) + τ) * √(n : ℝ)) := by
  have hV : 0 < √(Vocc η Ns) := Real.sqrt_pos.2 (Vocc_pos hη0 hη1 hNs)
  have hd : 0 < 1 - δ := by linarith
  set c := τ / (2 * √(Vocc η Ns)) with hc
  have hc0 : 0 < c := by positivity
  have hcV : c * √(Vocc η Ns) = τ / 2 := by
    rw [hc]; field_simp
  have hlo : (1 - δ) * Φ (q - c) < (1 - δ) * Φ q :=
    mul_lt_mul_of_pos_left (Φ_strictMono (by linarith)) hd
  have hhi : (1 - δ) * Φ q < (1 - δ) * Φ (q + c) :=
    mul_lt_mul_of_pos_left (Φ_strictMono (by linarith)) hd
  have hA := leak_achievability (ε := (1 - δ) * Φ q) hη0 hη1 hNs hδ0 hδ1.le
    (show q - c ≤ 0 by linarith) hlo (half_pos hτ)
  have hC := converse_second_order (ε := (1 - δ) * Φ q) hη0 hη1 hNs hδ0 hδ1 hhi (half_pos hτ)
  filter_upwards [hA, hC] with n hAn hCn
  refine ⟨?_, ?_⟩
  · obtain ⟨L', M, hM, hL, ⟨C, hs, hl⟩, hb⟩ := hAn
    refine ⟨L', M, hM, hL, ⟨C, hs, by rwa [← leakAbove_eq_leak]⟩, ?_⟩
    have : (q - c) * √(Vocc η Ns) - τ / 2 = q * √(Vocc η Ns) - τ := by
      rw [sub_mul, hcV]; ring
    rw [this] at hb
    exact hb
  · intro L' M C hM hl hs
    have h := hCn L' M C hM hl hs
    have : (q + c) * √(Vocc η Ns) + τ / 2 = q * √(Vocc η Ns) + τ := by
      rw [add_mul, hcV]; ring
    rw [this] at h
    exact h

end QIQCOP
