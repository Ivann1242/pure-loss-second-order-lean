import QIQCOP.BEDefs
import QIQCOP.BE.Chernoff
import QIQCOP.BE.Pointwise

/-!
# Berry–Esseen bound for the binomial distribution

`binomBE : 0 < η → η < 1 → BinomBE η`, i.e. there is `C` (depending on `η`) with
`|Pr{K < t} - Φ((t - ηL)/√(Lη(1-η)))| ≤ C/√L` for all `L ≥ 1` and all `t`.

Proof (elementary, total-variation style).  With `h = 1/√(Lη(1-η))`, `z_k = (k - ηL)h`,
`p_k = binomPMF L η k` and `I_k = Φ(z_{k+1}) - Φ(z_k)` we have the telescoping identity
`binomLT t - Φ(z_t) = ∑_{k<t} (p_k - I_k) - Φ(z_0)`.
* `|I_k - h·phi(z_k)| ≤ C h²/(1+|z_k|)²` (`BE.abs_cell_sub_le`);
* inside the window `|k - ηL| < c L^{2/3}`: `|p_k - h·phi(z_k)| ≤ C h²/(1+|z_k|)²`
  (Stirling with relative error + entropy expansion, `BE.binomPMF_sub_le`);
* outside the window: `h·phi(z_k) ≤ C h²/(1+|z_k|)²` (`BE.phi_outside_le`) and the binomial mass
  is `≤ C h` by a Chernoff bound (`BE.binom_tail_le`);
* `∑_k h/(1+|z_k|)² ≤ 4` (`BE.sum_weight_le`) and `Φ(z_0) ≤ h` (Chebyshev).
-/

open Real Finset

namespace QIQCOP

namespace BE

lemma binomPMF_eq_zero_of_lt {L k : ℕ} (η : ℝ) (h : L < k) : binomPMF L η k = 0 := by
  unfold binomPMF
  rw [Nat.choose_eq_zero_of_lt h]
  simp

/-- A sum over `range t` of a nonnegative sequence vanishing beyond `L` is at most the sum over
`range (L+1)`. -/
lemma sum_range_le_of_support {f : ℕ → ℝ} {L : ℕ} (hf : ∀ k, 0 ≤ f k)
    (hz : ∀ k, L < k → f k = 0) (t : ℕ) :
    ∑ k ∈ range t, f k ≤ ∑ k ∈ range (L + 1), f k := by
  calc ∑ k ∈ range t, f k ≤ ∑ k ∈ range (max t (L + 1)), f k :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (le_max_left _ _))
          fun k _ _ => hf k
    _ = ∑ k ∈ range (L + 1), f k := by
        symm
        refine sum_subset (range_subset_range.2 (le_max_right _ _)) fun k _ hk => ?_
        exact hz k (by simpa [Nat.lt_succ_iff] using hk)

lemma Φ_nonneg (z : ℝ) : 0 ≤ Φ z := ENNReal.toReal_nonneg

lemma binomLT_nonneg {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (L t : ℕ) : 0 ≤ binomLT L η t :=
  sum_nonneg fun k _ => binomPMF_nonneg hη0.le hη1.le k

lemma binomLT_le_one {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (L t : ℕ) : binomLT L η t ≤ 1 := by
  rw [← sum_binomPMF L η]
  exact sum_range_le_of_support (fun k => binomPMF_nonneg hη0.le hη1.le k)
    (fun k hk => binomPMF_eq_zero_of_lt η hk) t

lemma exp_neg_le_two_div_sq {u : ℝ} (hu : 0 < u) : exp (-u) ≤ 2 / u ^ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg hu.le
  rw [exp_neg, inv_eq_one_div, div_le_div_iff₀ (exp_pos u) (by positivity)]
  nlinarith

/-- The constant in the core estimate. -/
noncomputable def cCore (η : ℝ) : ℝ :=
  4 * (cWin η + 1536 / (min η (1 - η) / 2) ^ 3 + 50688) + 64 / (min η (1 - η) / 2) ^ 4 + 1

lemma cWin_nonneg {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) : 0 ≤ cWin η := by
  have := cD_pos hη0 hη1
  unfold cWin; positivity

/-- Core estimate, in terms of `h = 1/√(Lη(1-η)) ≤ 1`. -/
theorem binomBE_core {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) {L : ℕ} (hL : 1 ≤ L) {h : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hh : h ^ 2 * (L * (η * (1 - η))) = 1) (t : ℕ) :
    |binomLT L η t - Φ (((t : ℝ) - η * L) * h)| ≤ cCore η * h := by
  have hη' : 0 < 1 - η := by linarith
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hq0 : 0 < η * (1 - η) := mul_pos hη0 hη'
  have hq1 : η * (1 - η) ≤ 1 := by nlinarith
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min η (1 - η) / 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; exact div_pos (lt_min hη0 hη') (by norm_num)
  have hc1 : c ≤ 1 := by
    have := min_le_left η (1 - η)
    rw [hcdef]; linarith
  -- cube root of `L`
  obtain ⟨m, hm3, hm1⟩ : ∃ m : ℝ, m ^ 3 = L ∧ 1 ≤ m := by
    refine ⟨(L : ℝ) ^ ((1 : ℝ) / 3), ?_, Real.one_le_rpow hLr (by norm_num)⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
  have hm0 : 0 < m := by linarith
  have hm2L : m ^ 2 ≤ L := by
    rw [← hm3]; exact pow_le_pow_right₀ hm1 (by norm_num)
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = c * m ^ 2 := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have hw3 : w ^ 3 = c ^ 3 * (L : ℝ) ^ 2 := by rw [hw, ← hm3]; ring
  set p : ℕ → ℝ := fun k => binomPMF L η k with hp
  set z : ℕ → ℝ := fun k => ((k : ℝ) - η * L) * h with hz
  set B : ℕ → ℝ := fun k => h ^ 2 / (1 + |z k|) ^ 2 with hB
  have hp0 : ∀ k, 0 ≤ p k := fun k => binomPMF_nonneg hη0.le hη1.le k
  have hzs : ∀ k : ℕ, z (k + 1) = z k + h := by
    intro k; simp only [hz]; push_cast; ring
  have hB0 : ∀ k, 0 ≤ B k := fun k => by simp only [hB]; positivity
  set Cpt : ℝ := cWin η + 1536 / c ^ 3 + 50688 with hCpt
  have hcW := cWin_nonneg hη0 hη1
  -- Claim A: pointwise bound
  have claimA : ∀ k : ℕ, |p k - (Φ (z (k + 1)) - Φ (z k))| ≤
      Cpt * B k + (if w ≤ |(k : ℝ) - η * L| then p k else 0) := by
    intro k
    have hcell : |Φ (z (k + 1)) - Φ (z k) - h * phi (z k)| ≤ 50688 * B k := by
      rw [hzs]
      have := abs_cell_sub_le (z := z k) hh0 hh1
      simp only [hB]
      rw [mul_div_assoc] at this
      exact this
    have htri : |p k - (Φ (z (k + 1)) - Φ (z k))| ≤
        |p k - h * phi (z k)| + |Φ (z (k + 1)) - Φ (z k) - h * phi (z k)| := by
      have := abs_sub_le (p k) (h * phi (z k)) (Φ (z (k + 1)) - Φ (z k))
      rwa [abs_sub_comm (h * phi (z k))] at this
    have hBk := hB0 k
    have hc3 : 0 ≤ 1536 / c ^ 3 * B k := by positivity
    have hcWB : 0 ≤ cWin η * B k := mul_nonneg hcW hBk
    by_cases hout : w ≤ |(k : ℝ) - η * L|
    · rw [ite_eq_left hout]
      have h1 : h * phi (z k) ≤ 1536 / c ^ 3 * B k := by
        have := phi_outside_le (x := (k : ℝ) - η * L) (L := L) hη0 hη1 hc0 hh0 hh
          (by rw [← hw3]; exact pow_le_pow_left₀ hw0.le hout 3)
        simp only [hB, hz]
        rw [mul_div_assoc] at this
        exact this
      have h2 : |p k - h * phi (z k)| ≤ p k + 1536 / c ^ 3 * B k := by
        have hphi : 0 ≤ h * phi (z k) := mul_nonneg hh0.le (phi_nonneg _)
        rw [abs_le]; constructor <;> linarith [hp0 k]
      rw [hCpt]; nlinarith
    · rw [ite_eq_right hout, add_zero]
      push Not at hout
      have hx1 : |(k : ℝ) - η * L| ≤ min η (1 - η) / 2 * L := by
        rw [← hcdef]
        calc |(k : ℝ) - η * L| ≤ c * m ^ 2 := by rw [← hw]; exact hout.le
          _ ≤ c * L := mul_le_mul_of_nonneg_left hm2L hc0.le
      have hx3 : |(k : ℝ) - η * L| ^ 3 ≤ (L : ℝ) ^ 2 := by
        calc |(k : ℝ) - η * L| ^ 3 ≤ w ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hout.le 3
          _ = c ^ 3 * (L : ℝ) ^ 2 := hw3
          _ ≤ 1 * (L : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hc0.le hc1) (by positivity)
          _ = (L : ℝ) ^ 2 := one_mul _
      have h1 : |p k - h * phi (z k)| ≤ cWin η * B k := by
        have := binomPMF_sub_le hη0 hη1 hL hh0 hh1 hh hx1 hx3
        simp only [hB, hz, hp]
        rw [mul_div_assoc] at this
        exact this
      rw [hCpt]; nlinarith
  -- Claim B: the weights sum to at most `4h`
  have claimB : ∑ k ∈ range t, B k ≤ 4 * h := by
    have := sum_weight_le hh0 hh1 (-(η * L) * h) t
    have e : ∑ k ∈ range t, B k = h * ∑ k ∈ range t, h / (1 + |-(η * L) * h + k * h|) ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      simp only [hB, hz]
      rw [show ((k : ℝ) - η * L) * h = -(η * L) * h + k * h by ring]
      ring
    rw [e]
    nlinarith
  -- Claim C: binomial mass outside the window
  have claimC : ∑ k ∈ range t, (if w ≤ |(k : ℝ) - η * L| then p k else 0) ≤ 64 / c ^ 4 * h := by
    have s1 : ∑ k ∈ range t, (if w ≤ |(k : ℝ) - η * L| then p k else 0) ≤
        ∑ k ∈ range (L + 1), (if w ≤ |(k : ℝ) - η * L| then p k else 0) := by
      refine sum_range_le_of_support (fun k => ?_) (fun k hk => ?_) t
      · split_ifs
        · exact hp0 k
        · exact le_rfl
      · simp only [hp]
        rw [binomPMF_eq_zero_of_lt η hk]; simp
    have hlam0 : 0 ≤ c / (2 * m) := by positivity
    have hlam1 : c / (2 * m) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have s2 : ∑ k ∈ range (L + 1), (if w ≤ |(k : ℝ) - η * L| then p k else 0) ≤
        2 * exp ((c / (2 * m)) ^ 2 * (η * (1 - η)) * L - c / (2 * m) * w) := by
      rw [← sum_filter]
      exact binom_tail_le w hη0 hη1 hlam0 hlam1 L
    have hexp : (c / (2 * m)) ^ 2 * (η * (1 - η)) * L - c / (2 * m) * w ≤ -(c ^ 2 * m / 4) := by
      have e : (c / (2 * m)) ^ 2 * (η * (1 - η)) * L - c / (2 * m) * w =
          c ^ 2 * m / 4 * (η * (1 - η)) - c ^ 2 * m / 2 := by
        rw [hw, ← hm3]; field_simp; ring
      rw [e]
      have : 0 ≤ c ^ 2 * m / 4 := by positivity
      nlinarith
    have s3 : exp (-(c ^ 2 * m / 4)) ≤ 2 / (c ^ 2 * m / 4) ^ 2 :=
      exp_neg_le_two_div_sq (by positivity)
    have s4 : 1 / m ^ 2 ≤ h := by
      have h1 : (1 / m ^ 2) ^ 2 ≤ h ^ 2 := by
        have e1 : h ^ 2 = 1 / (L * (η * (1 - η))) := by
          field_simp; linarith
        rw [e1, div_pow, one_pow]
        refine one_div_le_one_div_of_le (by positivity) ?_
        calc (L : ℝ) * (η * (1 - η)) ≤ L * 1 := by gcongr
          _ = m ^ 3 := by rw [mul_one, hm3]
          _ ≤ m ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
          _ = (m ^ 2) ^ 2 := by ring
      exact (pow_le_pow_iff_left₀ (by positivity) hh0.le (by norm_num)).1 h1
    calc _ ≤ 2 * exp ((c / (2 * m)) ^ 2 * (η * (1 - η)) * L - c / (2 * m) * w) := s1.trans s2
      _ ≤ 2 * (2 / (c ^ 2 * m / 4) ^ 2) := by
        have := (exp_le_exp.2 hexp).trans s3
        linarith
      _ = 64 / c ^ 4 * (1 / m ^ 2) := by field_simp; ring
      _ ≤ 64 / c ^ 4 * h := mul_le_mul_of_nonneg_left s4 (by positivity)
  -- Claim D: the Gaussian mass below `z 0`
  have claimD : Φ (z 0) ≤ h := by
    have hu : 0 < η * L * h := by positivity
    have e : z 0 = -(η * L * h) := by simp only [hz]; push_cast; ring
    rw [e]
    refine (Φ_neg_le hu).trans ?_
    have e2 : (η * L * h) ^ 2 * (h ^ 2 * (1 - η) ^ 2) = η ^ 2 * (h ^ 2 * (L * (η * (1 - η)))) ^ 2 /
        η ^ 2 := by field_simp
    have e3 : 1 / (η * L * h) ^ 2 = h ^ 2 * (1 - η) ^ 2 := by
      rw [div_eq_iff (by positivity), mul_comm, e2, hh]
      field_simp
    rw [e3]
    have : (1 - η) ^ 2 ≤ 1 := pow_le_one₀ hη'.le (by linarith)
    nlinarith
  -- telescoping identity
  have htel : binomLT L η t - Φ (z t) =
      ∑ k ∈ range t, (p k - (Φ (z (k + 1)) - Φ (z k))) - Φ (z 0) := by
    rw [sum_sub_distrib, Finset.sum_range_sub (fun k => Φ (z k))]
    simp only [binomLT, hp]
    ring
  have hfinal : |binomLT L η t - Φ (z t)| ≤ Cpt * (4 * h) + 64 / c ^ 4 * h + h := by
    rw [htel]
    have h1 := abs_sub (∑ k ∈ range t, (p k - (Φ (z (k + 1)) - Φ (z k)))) (Φ (z 0))
    have h2 : |∑ k ∈ range t, (p k - (Φ (z (k + 1)) - Φ (z k)))| ≤
        ∑ k ∈ range t, (Cpt * B k + (if w ≤ |(k : ℝ) - η * L| then p k else 0)) :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => claimA k)
    rw [sum_add_distrib, ← mul_sum] at h2
    have h3 : Cpt * ∑ k ∈ range t, B k ≤ Cpt * (4 * h) :=
      mul_le_mul_of_nonneg_left claimB (by rw [hCpt]; positivity)
    rw [abs_of_nonneg (Φ_nonneg (z 0))] at h1
    linarith
  refine hfinal.trans (le_of_eq ?_)
  rw [cCore, ← hcdef, hCpt]
  ring

end BE

open BE in
/-- **Berry–Esseen for the binomial distribution**: for fixed `η ∈ (0,1)` there is `C` with
`|Pr{K < t} - Φ((t - ηL)/√(Lη(1-η)))| ≤ C/√L` for all `L ≥ 1` and all `t`. -/
theorem binomBE {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) : BinomBE η := by
  have hη' : 0 < 1 - η := by linarith
  have hq0 : 0 < η * (1 - η) := mul_pos hη0 hη'
  refine ⟨max (cCore η) 1 / √(η * (1 - η)), fun L hL t => ?_⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hσ : 0 < √((L : ℝ) * (η * (1 - η))) := Real.sqrt_pos.2 (by positivity)
  set h : ℝ := (√((L : ℝ) * (η * (1 - η))))⁻¹ with hh
  have hh0 : 0 < h := inv_pos.2 hσ
  have hh2 : h ^ 2 * (L * (η * (1 - η))) = 1 := by
    rw [hh, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hC : max (cCore η) 1 / √(η * (1 - η)) / √(L : ℝ) = max (cCore η) 1 * h := by
    rw [hh, Real.sqrt_mul hL0.le, div_div, mul_comm (√(η * (1 - η))), div_eq_mul_inv]
  rw [hC, div_eq_mul_inv, ← hh]
  rcases le_or_gt h 1 with h1 | h1
  · refine (binomBE_core hη0 hη1 hL hh0 h1 hh2 t).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hh0.le
  · have a1 := binomLT_nonneg hη0 hη1 L t
    have a2 := binomLT_le_one hη0 hη1 L t
    have a3 := Φ_nonneg (((t : ℝ) - η * L) * h)
    have a4 := Φ_le_one (((t : ℝ) - η * L) * h)
    have a5 : (1 : ℝ) ≤ max (cCore η) 1 * h := by
      have := le_max_right (cCore η) 1
      nlinarith
    rw [abs_le]; constructor <;> linarith

end QIQCOP
