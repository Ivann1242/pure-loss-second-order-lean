import QIQCOP.ProjectorBound
import QIQCOP.Counting
import QIQCOP.StirlingUpper

/-!
# Second-order converse for photon-number-constrained codes over the pure-loss channel

* `lossChannel_posSemidef`, `lossChannel_trace`: the channel maps states to states.
* `Code.leak`: average weight of the input states above `L₀` photons.
* `converse_finite`: finite-blocklength converse from the projector bound and photon counting.
* `converse_second_order`: `log₂ M ≤ n g(ηN_S) + (z √V_occ + τ) √n` eventually, whenever
  `ε < (1-δ) Φ(z)`, for all codes (in any truncation) with leakage `≤ δ` above `⌈n N_S⌉`.
* `converse_second_order_cutoff`: the strict cutoff case (`δ = 0`).
* `second_order_exact`: two-sided second-order statement for the strict cutoff, `ε = Φ(q) < 1/2`.
-/

open Finset Matrix Real Filter Topology
open scoped ComplexOrder

namespace QIQCOP

noncomputable section

variable {n L : ℕ}

/-! ### The channel output is a state -/

theorem lossChannel_posSemidef (η : ℝ) {ρ : Matrix (Occ n L) (Occ n L) ℂ} (hρ : ρ.PosSemidef) :
    (lossChannel η ρ).PosSemidef := by
  unfold lossChannel
  exact posSemidef_sum _ fun ℓ _ => hρ.mul_mul_conjTranspose_same _

theorem lossChannel_trace {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (ρ : Matrix (Occ n L) (Occ n L) ℂ) : (lossChannel η ρ).trace = ρ.trace := by
  unfold lossChannel
  rw [trace_sum]
  have h : ∀ ℓ : Occ n L, (lossKraus η ℓ * ρ * (lossKraus η ℓ)ᴴ).trace =
      (((lossKraus η ℓ)ᴴ * lossKraus η ℓ) * ρ).trace := by
    intro ℓ; rw [trace_mul_comm, ← Matrix.mul_assoc]
  simp_rw [h]
  rw [← trace_sum, ← Finset.sum_mul, lossKraus_complete hη0 hη1, one_mul]

/-! ### The low-photon projector on the truncated space -/

lemma lowProj_min (r : ℕ) : lowProj (n := n) (L := L) (min r L) = lowProj r := by
  unfold lowProj
  congr 1
  ext m
  have hm : photons (m : Fin n → ℕ) ≤ L := mem_occSet.1 m.2
  have h : (photons (m : Fin n → ℕ) ≤ min r L) ↔ photons (m : Fin n → ℕ) ≤ r := by omega
  simp only [h]

lemma lowProj_trace_re_le (r : ℕ) :
    ((lowProj (n := n) (L := L) r).trace).re ≤ ((n + r).choose r : ℝ) := by
  rw [← lowProj_min, lowProj_trace (min_le_right r L)]
  have h : (n + min r L).choose (min r L) ≤ (n + r).choose r := by
    rw [← Nat.choose_symm_add, ← Nat.choose_symm_add]
    exact Nat.choose_le_choose n (by omega)
  simp only [Complex.natCast_re]
  exact_mod_cast h

lemma one_sub_lowProj_self :
    (1 : Matrix (Occ n L) (Occ n L) ℂ) - lowProj (n := n) (L := L) L = 0 := by
  rw [one_sub_lowProj]
  ext i j
  have hm : photons (i : Fin n → ℕ) ≤ L := mem_occSet.1 i.2
  simp [Matrix.diagonal_apply, hm]

/-! ### Finite-blocklength converse -/

/-- Average weight of the code's input states above `L₀` photons. -/
def Code.leak {n L M : ℕ} (C : Code n L M) (L₀ : ℕ) : ℝ :=
  (∑ i, (((1 - lowProj L₀) * C.state i).trace).re) / M

/-- A code in the `≤ L` space has no weight above `L` photons. -/
theorem Code.leak_self {n L M : ℕ} (C : Code n L M) : C.leak L = 0 := by
  unfold Code.leak
  simp [one_sub_lowProj_self]

private lemma rearrange {s D M q Q e ch : ℝ} (hM : 0 < M)
    (h : s ≤ (√(D / M) + √q) ^ 2) (hs : e ≤ s) (hqQ : q ≤ Q) (hQ0 : 0 ≤ Q) (hQ : Q < e)
    (hD : D ≤ ch) : M ≤ ch / (√e - √Q) ^ 2 := by
  have h1 : √e ≤ √(D / M) + √q := by
    rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg (D / M)) (Real.sqrt_nonneg q))]
    exact Real.sqrt_le_sqrt (hs.trans h)
  have h2 : √q ≤ √Q := Real.sqrt_le_sqrt hqQ
  have hc : 0 < √e - √Q := sub_pos.2 (Real.sqrt_lt_sqrt hQ0 hQ)
  have h3 : √e - √Q ≤ √(D / M) := by linarith
  have hDM : 0 ≤ D / M := by
    by_contra hneg
    rw [not_le] at hneg
    rw [Real.sqrt_eq_zero_of_nonpos hneg.le] at h3
    linarith
  have h4 : (√e - √Q) ^ 2 ≤ D / M := by
    have := pow_le_pow_left₀ hc.le h3 2
    rwa [Real.sq_sqrt hDM] at this
  rw [le_div_iff₀ (pow_pos hc 2)]
  rw [le_div_iff₀ hM] at h4
  nlinarith

/-- **Finite-blocklength converse.** -/
theorem converse_finite {η ε δ : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {n L M : ℕ} (hM : 1 ≤ M)
    (C : Code n L M) (L₀ r : ℕ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hleak : C.leak L₀ ≤ δ)
    (hs : 1 - ε ≤ C.success η)
    (hq : (1 - δ) * binomGT L₀ η r + δ < 1 - ε) :
    (M : ℝ) ≤ ((n + r).choose r : ℝ) / (√(1 - ε) - √((1 - δ) * binomGT L₀ η r + δ)) ^ 2 := by
  have hMpos : 0 < M := hM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hb0 := binomGT_nonneg hη0 hη1 L₀ r
  have hb1 := binomGT_le_one hη0 hη1 L₀ r
  have hpb := projector_bound hMpos (fun i => lossChannel η (C.state i)) C.povm
    (fun i => lossChannel_posSemidef η (C.state_psd i))
    (fun i => by rw [lossChannel_trace hη0 hη1, C.state_trace])
    C.povm_psd C.povm_sum (lowProj r) (lowProj_isHermitian r) (lowProj_idem r)
  obtain ⟨w, hw⟩ : ∃ w : Fin M → ℝ, w = fun i => (((1 - lowProj L₀) * C.state i).trace).re :=
    ⟨_, rfl⟩
  have hq' : (∑ i, (((1 - lowProj r) * lossChannel η (C.state i)).trace).re) / M ≤
      (1 - δ) * binomGT L₀ η r + δ := by
    have h1 : ∑ i, (((1 - lowProj r) * lossChannel η (C.state i)).trace).re ≤
        ∑ i : Fin M, ((1 - w i) * binomGT L₀ η r + w i) := by
      rw [hw]
      exact Finset.sum_le_sum fun i _ =>
        high_weight_le_of_leak hη0 hη1 r L₀ _ (C.state_psd i) (C.state_trace i)
    have h2 : ∑ i : Fin M, ((1 - w i) * binomGT L₀ η r + w i) =
        M * binomGT L₀ η r + (∑ i, w i) * (1 - binomGT L₀ η r) := by
      have h : ∀ i : Fin M, (1 - w i) * binomGT L₀ η r + w i =
          binomGT L₀ η r + w i * (1 - binomGT L₀ η r) := fun i => by ring
      simp only [h]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp
    have hleak' : (∑ i, w i) / M ≤ δ := by rw [hw]; exact hleak
    rw [div_le_iff₀ hMr] at hleak' ⊢
    have h3 := mul_le_mul_of_nonneg_right hleak' (sub_nonneg.2 hb1)
    nlinarith
  have hQ0 : 0 ≤ (1 - δ) * binomGT L₀ η r + δ := by
    have := mul_nonneg (sub_nonneg.2 hδ1) hb0
    linarith
  exact rearrange hMr hpb hs hq' hQ0 hq (lowProj_trace_re_le r)

/-! ### Asymptotic second-order converse -/

/-- **Second-order converse with constant leakage.** -/
theorem converse_second_order {η Ns ε δ z : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hz : ε < (1 - δ) * Φ z) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (L' M : ℕ) (C : Code n L' M), 1 ≤ M →
      C.leak (cutoff Ns n) ≤ δ → 1 - ε ≤ C.success η →
        Real.logb 2 M ≤ n * g (η * Ns) + (z * √(Vocc η Ns) + τ) * √(n : ℝ) := by
  have hx : 0 < η * Ns := mul_pos hη0 hNs
  have hgp := gp_pos hx
  have hgs := gp_mul_sqrt_eq_sqrt_Vocc hη0 hη1 hNs
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((1 - δ) * Φ z - ε) / 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; linarith
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℕ, r = fun n : ℕ =>
      ⌈η * (cutoff Ns n : ℝ) + z * Real.sqrt ((cutoff Ns n : ℝ) * (η * (1 - η)))⌉₊ := ⟨_, rfl⟩
  have hlim : Tendsto (fun n : ℕ => binomLT (cutoff Ns n) η (r n)) atTop (𝓝 (Φ z)) := by
    rw [hr]; exact binomLT_cutoff_tendsto hη0 hη1 hNs z
  have hev1 : ∀ᶠ n : ℕ in atTop,
      (1 - δ) * binomGT (cutoff Ns n) η (r n) + δ ≤ 1 - ε - c := by
    filter_upwards [hlim.eventually (lt_mem_nhds (show Φ z - c < Φ z by linarith))] with n hn
    have hmono : binomLT (cutoff Ns n) η (r n) ≤ binomLT (cutoff Ns n) η (r n + 1) := by
      unfold binomLT
      rw [Finset.sum_range_succ]
      linarith [binomPMF_nonneg hη0.le hη1.le (L := cutoff Ns n) (r n)]
    have hG : binomGT (cutoff Ns n) η (r n) ≤ 1 - Φ z + c := by unfold binomGT; linarith
    have h1δ : 0 ≤ 1 - δ := by linarith
    have h1 := mul_le_mul_of_nonneg_left hG h1δ
    have h2 := mul_nonneg hδ0 hc0.le
    have h3 : (1 - δ) * Φ z = 2 * c + ε := by rw [hc]; ring
    nlinarith
  -- the constant
  have hQ0 : 0 ≤ 1 - ε - c := by
    obtain ⟨n0, hn0⟩ := hev1.exists
    have := mul_nonneg (sub_nonneg.2 hδ1.le) (binomGT_nonneg hη0.le hη1.le (cutoff Ns n0) (r n0))
    linarith
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = √(1 - ε) - √(1 - ε - c) := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by
    rw [hc']; exact sub_pos.2 (Real.sqrt_lt_sqrt hQ0 (by linarith))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = -Real.logb 2 (c' ^ 2) := ⟨_, rfl⟩
  have hsqrt : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hth : ∀ᶠ n : ℕ in atTop, ((r n : ℕ) : ℝ) - n * (η * Ns) ≤
      (z * Real.sqrt (η * (1 - η) * Ns) + τ / (2 * gp (η * Ns))) * Real.sqrt n := by
    rw [hr]
    exact converse_threshold hη0 hη1 hNs z (τ / (2 * gp (η * Ns))) (by positivity)
  filter_upwards [hev1, hth, hsqrt.eventually_ge_atTop (K / (τ / 2))] with n h1 h2 h3
  intro L' M C hM hleak hs
  rw [div_le_iff₀ (by positivity)] at h3
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hb0 := binomGT_nonneg hη0.le hη1.le (cutoff Ns n) (r n)
  have hq0 : 0 ≤ (1 - δ) * binomGT (cutoff Ns n) η (r n) + δ := by
    have := mul_nonneg (sub_nonneg.2 hδ1.le) hb0
    linarith
  have hfin := converse_finite hη0.le hη1.le hM C (cutoff Ns n) (r n) hδ0 hδ1.le hleak hs
    (by linarith)
  have hcn : c' ≤ √(1 - ε) - √((1 - δ) * binomGT (cutoff Ns n) η (r n) + δ) := by
    rw [hc']
    have := Real.sqrt_le_sqrt h1
    linarith
  have hch : (0 : ℝ) < ((n + r n).choose (r n) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left _ _)
  have hM' : (M : ℝ) ≤ ((n + r n).choose (r n) : ℝ) / c' ^ 2 := by
    rw [le_div_iff₀ (pow_pos hc'0 2)]
    rw [le_div_iff₀ (pow_pos (hc'0.trans_le hcn) 2)] at hfin
    have := pow_le_pow_left₀ hc'0.le hcn 2
    nlinarith
  have hlog : Real.logb 2 M ≤ Real.logb 2 ((n + r n).choose (r n) : ℝ) + K := by
    have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hMr hM'
    rw [Real.logb_div hch.ne' (pow_pos hc'0 2).ne'] at this
    rw [hK]; linarith
  have hst := logb_choose_le n (r n) hx
  have h4 := mul_le_mul_of_nonneg_right h2 hgp.le
  have h5 : (z * Real.sqrt (η * (1 - η) * Ns) + τ / (2 * gp (η * Ns))) * Real.sqrt n *
      gp (η * Ns) = (z * √(Vocc η Ns) + τ / 2) * √(n : ℝ) := by
    rw [← hgs]
    field_simp
  rw [h5] at h4
  have h6 : (z * √(Vocc η Ns) + τ) * √(n : ℝ) =
      (z * √(Vocc η Ns) + τ / 2) * √(n : ℝ) + τ / 2 * √(n : ℝ) := by ring
  rw [h6]
  linarith

/-- **Second-order converse for the strict photon cutoff** (the code class of
`CandidateConverse`). -/
theorem converse_second_order_cutoff {η Ns ε z : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hz : ε < Φ z) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (M : ℕ) (C : Code n (cutoff Ns n) M), 1 ≤ M →
      1 - ε ≤ C.success η →
        Real.logb 2 M ≤ n * g (η * Ns) + (z * √(Vocc η Ns) + τ) * √(n : ℝ) := by
  have h := converse_second_order (δ := 0) hη0 hη1 hNs le_rfl one_pos
    (by simpa using hz) hτ
  filter_upwards [h] with n hn M C hM hs
  exact hn _ M C hM (by rw [C.leak_self]) hs

/-! ### Two-sided second-order statement for the strict cutoff -/

private lemma eventually_log_le (A : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop, A * Real.log n ≤ τ * √(n : ℝ) := by
  have hsqrt : Tendsto (fun n : ℕ => √(√(n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hsqrt.eventually_ge_atTop (4 * |A| / τ), eventually_ge_atTop 1] with n h1 h2
  rw [div_le_iff₀ hτ] at h1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h2
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hu0 : 0 ≤ √(√(n : ℝ)) := Real.sqrt_nonneg _
  have huu : √(√(n : ℝ)) * √(√(n : ℝ)) = √(n : ℝ) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hl : Real.log n = 4 * Real.log (√(√(n : ℝ))) := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (by linarith)]; ring
  have hupos : 0 < √(√(n : ℝ)) := Real.sqrt_pos.2 (Real.sqrt_pos.2 (by linarith))
  have hle : Real.log (√(√(n : ℝ))) ≤ √(√(n : ℝ)) := by
    have := Real.log_le_sub_one_of_pos hupos
    linarith
  have hA : A * Real.log n ≤ |A| * Real.log n :=
    mul_le_mul_of_nonneg_right (le_abs_self A) hlog0
  have hA2 : |A| * Real.log n ≤ 4 * |A| * √(√(n : ℝ)) := by
    rw [hl]
    have := mul_le_mul_of_nonneg_left hle (abs_nonneg A)
    linarith
  have hA3 : 4 * |A| * √(√(n : ℝ)) ≤ τ * √(n : ℝ) := by
    have := mul_le_mul_of_nonneg_right h1 hu0
    nlinarith
  linarith

/-- **Exact second-order asymptotics for the strict photon cutoff**, for `ε = Φ(q) < 1/2`:
the optimal `log₂ M` is `n g(ηN_S) + q √(n V_occ) + o(√n)`. -/
theorem second_order_exact {η Ns q : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hNs : 0 < Ns)
    (hq : q < 0) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (∃ M : ℕ, 1 ≤ M ∧ (∃ C : Code n (cutoff Ns n) M, 1 - Φ q ≤ C.success η) ∧
        n * g (η * Ns) + (q * √(Vocc η Ns) - τ) * √(n : ℝ) ≤ Real.logb 2 M) ∧
      (∀ (M : ℕ) (C : Code n (cutoff Ns n) M), 1 ≤ M → 1 - Φ q ≤ C.success η →
        Real.logb 2 M ≤ n * g (η * Ns) + (q * √(Vocc η Ns) + τ) * √(n : ℝ)) := by
  have hV := Vocc_pos hη0 hη1 hNs
  have hsV : 0 < √(Vocc η Ns) := Real.sqrt_pos.2 hV
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = τ / (2 * √(Vocc η Ns)) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hκV : κ * √(Vocc η Ns) = τ / 2 := by rw [hκ]; field_simp
  -- converse
  have hconv := converse_second_order_cutoff (ε := Φ q) (z := q + κ) hη0 hη1 hNs
    (Φ_strictMono (by linarith)) (half_pos hτ)
  -- achievability
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = -q + κ := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hΦ : Φ (-s) < Φ q := Φ_strictMono (by rw [hs]; linarith)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = min ((Φ q - Φ (-s)) / 2) 1 := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγ]; exact lt_min (by linarith) one_pos
  have hγ1 : γ ≤ 1 := by rw [hγ]; exact min_le_right _ _
  have hγle : γ ≤ (Φ q - Φ (-s)) / 2 := by rw [hγ]; exact min_le_left _ _
  have hlt : Φ (-s) < Φ q - γ := by linarith
  have hth : ∀ᶠ n : ℕ in atTop, binomLT (cutoff Ns n) η
      ⌈η * (cutoff Ns n : ℝ) - s * √((cutoff Ns n : ℝ) * (η * (1 - η)))⌉₊ ≤ Φ q - γ := by
    have h := ((binomLT_tendsto hη0 hη1 (-s)).comp (tendsto_cutoff hNs)).eventually
      (gt_mem_nhds hlt)
    filter_upwards [h] with n hn
    simp only [Function.comp_apply, neg_mul, ← sub_eq_add_neg] at hn
    exact hn.le
  obtain ⟨A, hA⟩ := achievability_of_threshold hη0 hη1 hNs hγ0 hγ1 hs0 hth
  filter_upwards [hconv, hA, eventually_log_le A (half_pos hτ)] with n h1 h2 h3
  refine ⟨?_, ?_⟩
  · obtain ⟨M, hM, hC, hlog⟩ := h2
    refine ⟨M, hM, hC, ?_⟩
    have e : s * √(Vocc η Ns) = -q * √(Vocc η Ns) + τ / 2 := by rw [hs, add_mul, hκV]
    rw [e] at hlog
    nlinarith
  · intro M C hM hsucc
    have := h1 M C hM hsucc
    have e : (q + κ) * √(Vocc η Ns) = q * √(Vocc η Ns) + τ / 2 := by rw [add_mul, hκV]
    rw [e] at this
    linarith

end

end QIQCOP

