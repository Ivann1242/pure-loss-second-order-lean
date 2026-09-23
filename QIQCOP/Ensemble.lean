import QIQCOP.Sector

/-!
# A finite random-coding ensemble for condensate codes

Codeword directions are `u = (√(rⱼ/R) · ω^{aⱼ})ⱼ` with `r` a composition of `R` into `n`
parts and `a ∈ (ℤ/N)ⁿ`, `ω = e^{2πi/N}`, chosen uniformly. This replaces the Haar-random
directions of proof.md §1: for `N > t` and `R ≥ t(n+t)` the average `t`-th overlap moment is
at most `e / C(n+t-1, t)` (Haar gives exactly `1/C(n+t-1,t)`), which is all the
random-coding bound (5) needs.
-/

open Finset Matrix
open scoped Nat

namespace QIQCOP

/-- Index set of the finite ensemble. -/
abbrev Ens (n R N : ℕ) := ↥(sector n R) × (Fin n → Fin N)

/-- The codeword direction attached to an ensemble element. -/
noncomputable def ensVec {n R N : ℕ} (e : Ens n R N) : Fin n → ℂ := fun j =>
  ((√((((e.1 : Fin n → ℕ) j : ℕ) : ℝ) / R) : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (((e.2 j : ℕ) : ℂ)) / N)

/-- The phase `ω^b`, `ω = e^{2πi/N}`. -/
private noncomputable def ph (N : ℕ) (b : Fin N) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (((b : ℕ) : ℂ)) / N)

private lemma ensVec_apply {n R N : ℕ} (e : Ens n R N) (j : Fin n) :
    ensVec e j = ((√((((e.1 : Fin n → ℕ) j : ℕ) : ℝ) / R) : ℝ) : ℂ) * ph N (e.2 j) := rfl

private lemma star_ph (N : ℕ) (b : Fin N) :
    star (ph N b) = Complex.exp (-(2 * Real.pi * Complex.I * (((b : ℕ) : ℂ)) / N)) := by
  rw [ph, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_div₀, map_ofNat]
  ring

private lemma star_ph_mul_ph (N : ℕ) (b : Fin N) : star (ph N b) * ph N b = 1 := by
  rw [star_ph, ph, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- Ensemble directions are unit vectors. -/
theorem ensVec_norm {n R N : ℕ} (hR : 0 < R) (e : Ens n R N) :
    star (ensVec e) ⬝ᵥ ensVec e = 1 := by
  simp only [dotProduct, Pi.star_apply, ensVec_apply]
  have hsum : ∑ j, (((e.1 : Fin n → ℕ) j : ℕ) : ℝ) = R := by
    have := (mem_sector.1 e.1.2)
    simp only [photons] at this
    exact_mod_cast this
  have : ∀ j, star (((√((((e.1 : Fin n → ℕ) j : ℕ) : ℝ) / R) : ℝ) : ℂ) * ph N (e.2 j)) *
      (((√((((e.1 : Fin n → ℕ) j : ℕ) : ℝ) / R) : ℝ) : ℂ) * ph N (e.2 j)) =
      (((((e.1 : Fin n → ℕ) j : ℕ) : ℝ) / R : ℝ) : ℂ) := by
    intro j
    rw [star_mul', mul_mul_mul_comm, star_ph_mul_ph, mul_one, Complex.star_def,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  simp_rw [this]
  rw [← Complex.ofReal_sum, ← Finset.sum_div, hsum, div_self (by positivity), Complex.ofReal_one]


private lemma sum_ph {N t : ℕ} (hN : t < N) (p q : ℕ) (hp : p ≤ t) (hq : q ≤ t) :
    ∑ b : Fin N, star (ph N b) ^ p * ph N b ^ q = if p = q then (N : ℂ) else 0 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  set w := Complex.exp (2 * Real.pi * Complex.I * ((q : ℂ) - p) / N) with hw
  have hterm : ∀ b : Fin N, star (ph N b) ^ p * ph N b ^ q = w ^ (b : ℕ) := by
    intro b
    rw [star_ph, ph, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, hw,
      ← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun i => w ^ i) N]
  split_ifs with hpq
  · subst hpq
    simp [w]
  · have hwN : w ^ N = 1 := by
      rw [hw, ← Complex.exp_nat_mul]
      have : (N : ℂ) * (2 * Real.pi * Complex.I * ((q : ℂ) - p) / N) =
          (((q : ℤ) - p : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    have hw1 : w ≠ 1 := by
      intro h
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have hc : ((q : ℂ) - p) = k * N := by
        calc ((q : ℂ) - p) = (2 * Real.pi * Complex.I * ((q : ℂ) - p) / N) * N /
              (2 * Real.pi * Complex.I) := by field_simp
          _ = k * N := by rw [hk]; field_simp
      have hz : ((q : ℤ) - p : ℤ) = k * N := by exact_mod_cast hc
      have hdvd : (N : ℤ) ∣ (q : ℤ) - p := ⟨k, by rw [hz]; ring⟩
      have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
      omega
    rw [geom_sum_eq hw1, hwN, sub_self, zero_div]

private lemma sum_ph_vec {n N t : ℕ} (hN : t < N) (m m' : Fin n → ℕ) (hm : ∀ j, m j ≤ t)
    (hm' : ∀ j, m' j ≤ t) :
    ∑ a : Fin n → Fin N, ∏ j, star (ph N (a j)) ^ m j * ph N (a j) ^ m' j =
      if m = m' then (N : ℂ) ^ n else 0 := by
  rw [← Fintype.prod_sum (fun j b => star (ph N b) ^ m j * ph N b ^ m' j)]
  simp_rw [sum_ph hN _ _ (hm _) (hm' _)]
  split_ifs with h
  · subst h; simp
  · obtain ⟨j, hj⟩ : ∃ j, m j ≠ m' j := by
      exact Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])


private lemma sum_comm4 {α β γ δ M : Type*} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (C : Finset γ) (D : Finset δ) (F : α → β → γ → δ → M) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, F a b c d =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, F a b c d := by
  calc ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, F a b c d
      = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ D, F a b c d :=
        sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ d ∈ D, ∑ b ∈ B, F a b c d :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ d ∈ D, ∑ b ∈ B, F a b c d := Finset.sum_comm
    _ = ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, F a b c d :=
        sum_congr rfl fun _ _ => Finset.sum_comm

private lemma sum_comm3 {α β γ M : Type*} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (C : Finset γ) (F : α → β → γ → M) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, F a b c := by
  calc ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, F a b c :=
        sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, F a b c := Finset.sum_comm

private lemma norm_pow_two_mul (z : ℂ) (t : ℕ) : ((‖z‖ : ℂ)) ^ (2 * t) = z ^ t * (star z) ^ t := by
  rw [pow_mul, ← Complex.mul_conj', mul_pow]
  rfl

private lemma phase_sum {n N t : ℕ} (hN : t < N) (s s' : Fin n → ℝ) :
    ∑ a : Fin n → Fin N, ∑ a' : Fin n → Fin N,
        ‖∑ j, star ((s j : ℂ) * ph N (a j)) * ((s' j : ℂ) * ph N (a' j))‖ ^ (2 * t) =
      (N : ℝ) ^ n * (N : ℝ) ^ n *
        ∑ m ∈ sector n t, (Nat.multinomial univ m : ℝ) ^ 2 * ∏ j, (s j ^ 2 * s' j ^ 2) ^ m j := by
  classical
  apply Complex.ofReal_injective
  push_cast
  set S := sector n t with hS
  have hSle : ∀ m ∈ S, ∀ j, m j ≤ t := by
    intro m hm j
    have := (mem_sector.1 hm)
    rw [← this]
    exact Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set c : Fin n → ℂ := fun j => ((s j * s' j : ℝ) : ℂ) with hc
  have hz : ∀ a a' : Fin n → Fin N,
      ∑ j, star ((s j : ℂ) * ph N (a j)) * ((s' j : ℂ) * ph N (a' j)) =
        ∑ j, c j * (star (ph N (a j)) * ph N (a' j)) := by
    intro a a'
    refine sum_congr rfl fun j _ => ?_
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, hc]
    push_cast
    ring
  have hsz : ∀ a a' : Fin n → Fin N,
      star (∑ j, c j * (star (ph N (a j)) * ph N (a' j))) =
        ∑ j, c j * (star (ph N (a' j)) * ph N (a j)) := by
    intro a a'
    rw [star_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [star_mul', star_mul', star_star, hc, Complex.star_def, Complex.conj_ofReal]
    ring
  -- expand
  calc ∑ a : Fin n → Fin N, ∑ a' : Fin n → Fin N,
        ((‖∑ j, star ((s j : ℂ) * ph N (a j)) * ((s' j : ℂ) * ph N (a' j))‖ : ℂ)) ^ (2 * t)
      = ∑ a : Fin n → Fin N, ∑ a' : Fin n → Fin N, ∑ m ∈ S, ∑ m' ∈ S,
          ((Nat.multinomial univ m : ℂ) * (Nat.multinomial univ m' : ℂ) *
            ∏ j, c j ^ (m j + m' j)) *
          (∏ j, star (ph N (a j)) ^ m j * ph N (a j) ^ m' j) *
          (∏ j, star (ph N (a' j)) ^ m' j * ph N (a' j) ^ m j) := by
        refine sum_congr rfl fun a _ => sum_congr rfl fun a' _ => ?_
        rw [norm_pow_two_mul, hz, hsz, sum_pow_eq_sum_piAntidiag, sum_pow_eq_sum_piAntidiag,
          sum_mul_sum]
        refine sum_congr rfl fun m _ => sum_congr rfl fun m' _ => ?_
        have hj : ∀ j, (c j * (star (ph N (a j)) * ph N (a' j))) ^ m j *
            (c j * (star (ph N (a' j)) * ph N (a j))) ^ m' j =
            c j ^ (m j + m' j) * (star (ph N (a j)) ^ m j * ph N (a j) ^ m' j) *
              (star (ph N (a' j)) ^ m' j * ph N (a' j) ^ m j) := fun j => by ring
        calc _ = (Nat.multinomial univ m : ℂ) * (Nat.multinomial univ m' : ℂ) *
              ∏ j, ((c j * (star (ph N (a j)) * ph N (a' j))) ^ m j *
                (c j * (star (ph N (a' j)) * ph N (a j))) ^ m' j) := by
                rw [prod_mul_distrib]; ring
          _ = _ := by simp_rw [hj]; rw [prod_mul_distrib, prod_mul_distrib]; ring
    _ = ∑ m ∈ S, ∑ m' ∈ S,
          ((Nat.multinomial univ m : ℂ) * (Nat.multinomial univ m' : ℂ) *
            ∏ j, c j ^ (m j + m' j)) *
          (∑ a : Fin n → Fin N, ∏ j, star (ph N (a j)) ^ m j * ph N (a j) ^ m' j) *
          (∑ a' : Fin n → Fin N, ∏ j, star (ph N (a' j)) ^ m' j * ph N (a' j) ^ m j) := by
        rw [sum_comm4]
        refine sum_congr rfl fun m _ => sum_congr rfl fun m' _ => ?_
        rw [mul_sum, Finset.sum_comm]
        refine sum_congr rfl fun a' _ => ?_
        rw [mul_sum, sum_mul]
    _ = ∑ m ∈ S, ∑ m' ∈ S,
          ((Nat.multinomial univ m : ℂ) * (Nat.multinomial univ m' : ℂ) *
            ∏ j, c j ^ (m j + m' j)) *
          (if m = m' then (N : ℂ) ^ n else 0) * (if m' = m then (N : ℂ) ^ n else 0) := by
        refine sum_congr rfl fun m hm => sum_congr rfl fun m' hm' => ?_
        rw [sum_ph_vec hN m m' (hSle m hm) (hSle m' hm'),
          sum_ph_vec hN m' m (hSle m' hm') (hSle m hm)]
    _ = ∑ m ∈ S, ((Nat.multinomial univ m : ℂ) * (Nat.multinomial univ m : ℂ) *
            ∏ j, c j ^ (m j + m j)) * (N : ℂ) ^ n * (N : ℂ) ^ n := by
        refine sum_congr rfl fun m hm => ?_
        rw [sum_eq_single m]
        · simp
        · intro m' _ hne
          simp [Ne.symm hne]
        · intro h; exact absurd hm h
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun m _ => ?_
        have : ∀ j, c j ^ (m j + m j) = ((s j : ℂ) ^ 2 * (s' j : ℂ) ^ 2) ^ m j := by
          intro j; rw [hc]; push_cast; ring
        simp_rw [this]
        ring

private lemma sum_piAntidiag_eq_sum_finsuppAntidiag {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (R : ℕ) (F : (ι → ℕ) → ℝ) :
    ∑ r ∈ piAntidiag s R, F r = ∑ l ∈ finsuppAntidiag s R, F l := by
  rw [finsuppAntidiag, sum_map, ← sum_attach (piAntidiag s R)]
  rfl

/-- Stars-and-bars convolution: `∑_{r ∈ sector n R} ∏ⱼ C(mⱼ + rⱼ, mⱼ) = C(d - 1 + R, d - 1)`
with `d = ∑ⱼ (mⱼ + 1)`. -/
private lemma sum_sector_prod_choose (n : ℕ) (m : Fin n → ℕ) (R : ℕ) (h : 0 < ∑ j, (m j + 1)) :
    ∑ r ∈ sector n R, ∏ j, (((m j + r j).choose (m j) : ℕ) : ℝ) =
      (((∑ j, (m j + 1)) - 1 + R).choose ((∑ j, (m j + 1)) - 1) : ℕ) := by
  classical
  have key : ∏ j, (PowerSeries.invOneSubPow ℝ (m j + 1)).val =
      (PowerSeries.invOneSubPow ℝ (∑ j, (m j + 1))).val := by
    rw [← Units.coe_prod]
    congr 1
    simp_rw [PowerSeries.invOneSubPow_eq_inv_one_sub_pow]
    rw [prod_pow_eq_pow_sum]
  have := congrArg (PowerSeries.coeff R) key
  rw [PowerSeries.coeff_prod, PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ h,
    PowerSeries.coeff_mk] at this
  simp_rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk] at this
  rw [← this, sector, sum_piAntidiag_eq_sum_finsuppAntidiag]


private lemma choose_identity (n' t R : ℕ) :
    t ! * (t + n' + R).choose (t + n') * (n' + t).choose t =
      (n' + R).choose R * (R + n' + 1).ascFactorial t := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.factorial_pos n') (Nat.factorial_pos R))
  have e1 := Nat.add_choose_mul_factorial_mul_factorial n' t
  have e2 : (t + n' + R).choose (t + n') * (t + n')! * R ! = (t + n' + R)! := by
    have := Nat.choose_mul_factorial_mul_factorial (n := t + n' + R) (k := t + n') (by omega)
    rwa [Nat.add_sub_cancel_left] at this
  have e3 := Nat.add_choose_mul_factorial_mul_factorial n' R
  have e4 := Nat.factorial_mul_ascFactorial (n' + R) t
  have h5 : R + n' + 1 = n' + R + 1 := by ring
  rw [h5]
  calc t ! * (t + n' + R).choose (t + n') * (n' + t).choose t * (n' ! * R !)
      = (t + n' + R).choose (t + n') * ((n' + t).choose t * n' ! * t !) * R ! := by ring
    _ = (t + n' + R).choose (t + n') * (t + n')! * R ! := by
        rw [e1, show n' + t = t + n' by ring]
    _ = (n' + R + t)! := by rw [e2, show t + n' + R = n' + R + t by ring]
    _ = (n' + R)! * (n' + R + 1).ascFactorial t := e4.symm
    _ = (n' + R).choose R * (n' + R + 1).ascFactorial t * (n' ! * R !) := by
        rw [← e3]; ring

private lemma pow_le_exp_mul (R n' t : ℕ) (hR : 0 < R) (h : t * (n' + 1 + t) ≤ R) :
    (((R + n' + t : ℕ) : ℝ)) ^ t ≤ Real.exp 1 * (R : ℝ) ^ t := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have h1 : ((R + n' + t : ℕ) : ℝ) ≤ R * Real.exp ((n' + t : ℝ) / R) := by
    have := Real.add_one_le_exp ((n' + t : ℝ) / R)
    push_cast
    calc (R : ℝ) + n' + t = R * ((n' + t) / R + 1) := by field_simp; ring
      _ ≤ R * Real.exp ((n' + t : ℝ) / R) := by gcongr
  have h2 : (t : ℝ) * ((n' + t : ℝ) / R) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hRpos]
    have : t * (n' + t) ≤ R := le_trans (Nat.mul_le_mul_left _ (by omega)) h
    exact_mod_cast this
  calc (((R + n' + t : ℕ) : ℝ)) ^ t ≤ (R * Real.exp ((n' + t : ℝ) / R)) ^ t :=
        pow_le_pow_left₀ (by positivity) h1 t
    _ = (R : ℝ) ^ t * Real.exp (t * ((n' + t : ℝ) / R)) := by
        rw [mul_pow, ← Real.exp_nat_mul]
    _ ≤ (R : ℝ) ^ t * Real.exp 1 := by gcongr
    _ = Real.exp 1 * (R : ℝ) ^ t := mul_comm _ _

private lemma T_bound (n' t R : ℕ) (hR : 0 < R) (hRt : t * (n' + 1 + t) ≤ R)
    (m : Fin (n' + 1) → ℕ) (hm : m ∈ sector (n' + 1) t) :
    (Nat.multinomial univ m : ℝ) * ∑ r ∈ sector (n' + 1) R, ∏ j, ((r j : ℝ) / R) ^ m j ≤
      Real.exp 1 * (sector (n' + 1) R).card / sectorDim (n' + 1) t := by
  have hmt : ∑ j, m j = t := mem_sector.1 hm
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have step1 : ∀ r ∈ sector (n' + 1) R, ∏ j, ((r j : ℝ) / R) ^ m j =
      (∏ j, ((r j : ℝ)) ^ m j) / (R : ℝ) ^ t := by
    intro r _
    rw [← hmt, ← prod_pow_eq_pow_sum, ← prod_div_distrib]
    simp_rw [div_pow]
  have step2 : ∀ r : Fin (n' + 1) → ℕ, ∏ j, ((r j : ℝ)) ^ m j ≤
      ∏ j, (((m j)! : ℕ) : ℝ) * (((m j + r j).choose (m j) : ℕ) : ℝ) := by
    intro r
    apply Finset.prod_le_prod₀ (fun j _ => by positivity)
    intro j _
    have : (r j) ^ (m j) ≤ (m j)! * (m j + r j).choose (m j) := by
      rw [add_comm (m j), ← Nat.ascFactorial_eq_factorial_mul_choose]
      exact le_trans (Nat.pow_le_pow_left (Nat.le_succ _) _) (Nat.pow_succ_le_ascFactorial _ _)
    exact_mod_cast this
  have hd : ∑ j : Fin (n' + 1), (m j + 1) = t + (n' + 1) := by
    rw [sum_add_distrib, hmt]; simp
  have hconv := sum_sector_prod_choose (n' + 1) m R (by rw [hd]; omega)
  rw [hd, show t + (n' + 1) - 1 = t + n' by omega] at hconv
  have hspec := Nat.multinomial_spec (univ : Finset (Fin (n' + 1))) m
  rw [hmt] at hspec
  have hK : ((sector (n' + 1) R).card : ℝ) = ((n' + R).choose R : ℕ) := by
    rw [card_sector, show n' + 1 + R - 1 = n' + R by omega]
  have hD : sectorDim (n' + 1) t = ((n' + t).choose t : ℕ) := by
    rw [sectorDim, show n' + 1 + t - 1 = n' + t by omega]
  have hDpos : (0 : ℝ) < ((n' + t).choose t : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  -- main chain
  have hsum_le : ∑ r ∈ sector (n' + 1) R, ∏ j, ((r j : ℝ) / R) ^ m j ≤
      (∏ j, (((m j)! : ℕ) : ℝ)) * (((t + n' + R).choose (t + n') : ℕ) : ℝ) / (R : ℝ) ^ t := by
    rw [sum_congr rfl step1, ← sum_div, ← hconv, mul_sum]
    gcongr with r _
    rw [← prod_mul_distrib]
    exact step2 r
  have hid := choose_identity n' t R
  have hasc := Nat.ascFactorial_le_pow_add (R + n') t
  have hexp := pow_le_exp_mul R n' t hR hRt
  rw [hK, hD, le_div_iff₀ hDpos]
  calc (Nat.multinomial univ m : ℝ) * (∑ r ∈ sector (n' + 1) R, ∏ j, ((r j : ℝ) / R) ^ m j) *
        ((n' + t).choose t : ℕ)
      ≤ (Nat.multinomial univ m : ℝ) * ((∏ j, (((m j)! : ℕ) : ℝ)) *
          (((t + n' + R).choose (t + n') : ℕ) : ℝ) / (R : ℝ) ^ t) * ((n' + t).choose t : ℕ) := by
        gcongr
    _ = ((t ! * (t + n' + R).choose (t + n') * (n' + t).choose t : ℕ) : ℝ) / (R : ℝ) ^ t := by
        rw [← hspec]; push_cast; ring
    _ = (((n' + R).choose R * (R + n' + 1).ascFactorial t : ℕ) : ℝ) / (R : ℝ) ^ t := by
        rw [hid]
    _ ≤ (((n' + R).choose R : ℕ) : ℝ) * ((R + n' + t : ℕ) : ℝ) ^ t / (R : ℝ) ^ t := by
        gcongr
        push_cast
        gcongr
        exact_mod_cast hasc
    _ ≤ (((n' + R).choose R : ℕ) : ℝ) * (Real.exp 1 * (R : ℝ) ^ t) / (R : ℝ) ^ t := by
        gcongr
    _ = Real.exp 1 * (((n' + R).choose R : ℕ) : ℝ) := by
        field_simp


/-- **Moment bound**: `𝔼_{u,v} |⟨u|v⟩|^{2t} ≤ e / C(n+t-1, t)`. -/
theorem ensemble_moment {n t R N : ℕ} (hn : 1 ≤ n) (hN : t < N) (hR : 0 < R)
    (hRt : t * (n + t) ≤ R) :
    ∑ e : Ens n R N, ∑ e' : Ens n R N, ‖star (ensVec e) ⬝ᵥ ensVec e'‖ ^ (2 * t) ≤
      Real.exp 1 / sectorDim n t * (Fintype.card (Ens n R N) : ℝ) ^ 2 := by
  classical
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  set K := (sector (n' + 1) R).card with hKdef
  set x : ↥(sector (n' + 1) R) → Fin (n' + 1) → ℝ := fun r j => ((r.1 j : ℕ) : ℝ) / R with hx
  set T : (Fin (n' + 1) → ℕ) → ℝ := fun m =>
    ∑ r : ↥(sector (n' + 1) R), (Nat.multinomial univ m : ℝ) * ∏ j, (x r j) ^ m j with hT
  have hx0 : ∀ r j, 0 ≤ x r j := fun r j => by positivity
  have hxsum : ∀ r, ∑ j, x r j = 1 := by
    intro r
    have := (mem_sector.1 r.2)
    simp only [photons] at this
    have hs : ∑ j, ((r.1 j : ℕ) : ℝ) = R := by exact_mod_cast this
    rw [hx]
    dsimp only
    rw [← Finset.sum_div, hs, div_self (by positivity)]
  -- Step 1: rewrite the moment sum
  have hLHS : ∑ e : Ens (n' + 1) R N, ∑ e' : Ens (n' + 1) R N,
      ‖star (ensVec e) ⬝ᵥ ensVec e'‖ ^ (2 * t) =
      (N : ℝ) ^ (n' + 1) * (N : ℝ) ^ (n' + 1) * ∑ m ∈ sector (n' + 1) t, T m ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    calc _ = ∑ r : ↥(sector (n' + 1) R), ∑ r' : ↥(sector (n' + 1) R),
          ∑ a : Fin (n' + 1) → Fin N, ∑ a' : Fin (n' + 1) → Fin N,
            ‖star (ensVec (r, a)) ⬝ᵥ ensVec (r', a')‖ ^ (2 * t) :=
          sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ r : ↥(sector (n' + 1) R), ∑ r' : ↥(sector (n' + 1) R),
          (N : ℝ) ^ (n' + 1) * (N : ℝ) ^ (n' + 1) *
            ∑ m ∈ sector (n' + 1) t, (Nat.multinomial univ m : ℝ) ^ 2 *
              ∏ j, (x r j * x r' j) ^ m j := by
          refine sum_congr rfl fun r _ => sum_congr rfl fun r' _ => ?_
          have := phase_sum hN (fun j => √(x r j)) (fun j => √(x r' j))
          simp only [Real.sq_sqrt (hx0 _ _)] at this
          rw [← this]
          rfl
      _ = _ := by
          simp_rw [← mul_sum]
          congr 1
          rw [sum_comm3]
          refine sum_congr rfl fun m _ => ?_
          rw [hT]
          dsimp only
          conv_rhs => rw [sq, sum_mul_sum]
          refine sum_congr rfl fun r _ => sum_congr rfl fun r' _ => ?_
          simp_rw [mul_pow]
          rw [prod_mul_distrib]
          ring
  -- Step 2: nonnegativity
  have hT0 : ∀ m, 0 ≤ T m := fun m => by
    rw [hT]; exact sum_nonneg fun r _ => by
      have := hx0 r; positivity
  -- Step 3: total mass
  have hTsum : ∑ m ∈ sector (n' + 1) t, T m = K := by
    rw [hT]
    dsimp only
    rw [Finset.sum_comm]
    calc ∑ r : ↥(sector (n' + 1) R), ∑ m ∈ sector (n' + 1) t,
          (Nat.multinomial univ m : ℝ) * ∏ j, (x r j) ^ m j
        = ∑ r : ↥(sector (n' + 1) R), (∑ j, x r j) ^ t := by
          refine sum_congr rfl fun r _ => ?_
          rw [sum_pow_eq_sum_piAntidiag]
      _ = K := by simp [hxsum, hKdef]
  -- Step 4: pointwise bound
  set B := Real.exp 1 * (K : ℝ) / sectorDim (n' + 1) t with hB
  have hTB : ∀ m ∈ sector (n' + 1) t, T m ≤ B := by
    intro m hm
    have := T_bound n' t R hR (by simpa [add_assoc] using hRt) m hm
    rw [hT]
    dsimp only
    rw [← mul_sum]
    convert this using 2
    rw [← Finset.sum_coe_sort (sector (n' + 1) R)]
  -- Step 5
  have hsq : ∑ m ∈ sector (n' + 1) t, T m ^ 2 ≤ K * B := by
    calc ∑ m ∈ sector (n' + 1) t, T m ^ 2 ≤ ∑ m ∈ sector (n' + 1) t, T m * B := by
          refine sum_le_sum fun m hm => ?_
          rw [sq]
          exact mul_le_mul_of_nonneg_left (hTB m hm) (hT0 m)
      _ = K * B := by rw [← sum_mul, hTsum]
  have hcard : (Fintype.card (Ens (n' + 1) R N) : ℝ) = K * (N : ℝ) ^ (n' + 1) := by
    simp [Fintype.card_prod, hKdef]
  rw [hLHS, hcard]
  calc (N : ℝ) ^ (n' + 1) * (N : ℝ) ^ (n' + 1) * ∑ m ∈ sector (n' + 1) t, T m ^ 2
      ≤ (N : ℝ) ^ (n' + 1) * (N : ℝ) ^ (n' + 1) * (K * B) := by gcongr
    _ = _ := by rw [hB]; ring

private lemma sum_fun_apply_pair {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S]
    (f : S → S → ℝ) (i j : ι) (hij : i ≠ j) :
    ∑ c : ι → S, f (c i) (c j) =
      (Fintype.card S : ℝ) ^ (Fintype.card ι - 2) * ∑ a, ∑ b, f a b := by
  classical
  have h1 : ∑ c : ι → S, f (c i) (c j) =
      ∑ p : S × ({k // k ≠ i} → S), f p.1 (p.2 ⟨j, hij.symm⟩) :=
    Fintype.sum_equiv (Equiv.funSplitAt i S) _ _ (fun c => rfl)
  have hcard : Fintype.card {k // k ≠ i} = Fintype.card ι - 1 := by
    simp
  rw [h1, Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  have := Fintype.sum_piFinset_apply (fun b => f a b) (univ : Finset S)
    (⟨j, hij.symm⟩ : {k // k ≠ i})
  rw [Fintype.piFinset_univ, hcard, card_univ, nsmul_eq_mul] at this
  rw [this]
  push_cast
  congr 2

/-- **Averaging over codebooks**: some codebook of `M` i.i.d. draws has off-diagonal
pair weight at most its expectation. -/
theorem exists_codebook {S : Type*} [Fintype S] [Nonempty S] (w : S → S → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (M : ℕ) :
    ∃ c : Fin M → S, ∑ i, ∑ j ∈ univ.filter (· ≠ i), w (c i) (c j) ≤
      (M : ℝ) * (M - 1) * (∑ a, ∑ b, w a b) / (Fintype.card S : ℝ) ^ 2 := by
  classical
  set W := ∑ a, ∑ b, w a b with hW
  have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have key : ∑ c : Fin M → S, ∑ i, ∑ j ∈ univ.filter (· ≠ i), w (c i) (c j) =
      ∑ _c : Fin M → S, (M : ℝ) * (M - 1) * W / (Fintype.card S : ℝ) ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (univ : Finset (Fin M → S)))]
    have hinner : ∀ i : Fin M, ∀ j ∈ univ.filter (· ≠ i),
        ∑ c : Fin M → S, w (c i) (c j) = (Fintype.card S : ℝ) ^ (M - 2) * W := by
      intro i j hj
      rw [mem_filter] at hj
      rw [sum_fun_apply_pair w i j (Ne.symm hj.2), Fintype.card_fin]
    rw [sum_congr rfl fun i _ => sum_congr rfl (hinner i)]
    simp only [sum_const, card_univ, Fintype.card_fin, Fintype.card_pi, prod_const,
      nsmul_eq_mul]
    have hfilt : ∀ i : Fin M, (univ.filter (· ≠ i)).card = M - 1 := by
      intro i
      rw [filter_ne', card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    simp only [hfilt, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.lt_or_ge M 2 with hM | hM
    · interval_cases M <;> simp
    · have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hM1]
      have : (Fintype.card S : ℝ) ^ M = (Fintype.card S : ℝ) ^ (M - 2) *
          (Fintype.card S : ℝ) ^ 2 := by
        rw [← pow_add, Nat.sub_add_cancel hM]
      rw [Nat.cast_pow, this]
      field_simp
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_sum_le univ_nonempty key.le
  exact ⟨c, hc⟩

end QIQCOP
