import QIQCOP.Fock

/-!
# The pure-loss Kraus form is the beam-splitter channel

The beam splitter is defined from creation operators only, through the relation
`a† ↦ √η b† + √(1-η) e†` applied to the two-mode vacuum. The binomial amplitudes are then
*derived* (`bsV_ket`), using the binomial theorem for the commuting operators `b†`, `e†`.

Main results:

* `commute_bDag_eDag` : `[b†, e†] = 0`.
* `bsV_vacuum`, `bsV_aDag` : `V|0⟩ = |0,0⟩` and `V a† = (√η b† + √(1-η) e†) V`.
* `bsV_ket` : `V|m⟩ = ∑_{l ≤ m} √(C(m,l) η^{m-l} (1-η)^l) |m-l,l⟩`.
* `bsV_isometry` : `⟨Vφ, Vψ⟩ = ⟨φ, ψ⟩` on finite-support vectors.
* `beamSplitterMat_col` : the `n`-mode expansion of the product isometry.
* `beamSplitterMat_isometry` : `Vᴴ V = 1`.
* `lossChannel_eq_partialTrace_beamSplitter` : `Tr_E (V ρ Vᴴ) = lossChannel η ρ`.
-/

open Finset Matrix

namespace QIQCOP

namespace BeamSplitter

noncomputable section

/-! ### Fock vectors and creation operators -/

/-- Finite-support single-mode Fock vectors. -/
abbrev OneFock := ℕ →₀ ℂ

/-- Finite-support two-mode (output `B`, environment `E`) Fock vectors. -/
abbrev TwoFock := (ℕ × ℕ) →₀ ℂ

/-- The single-mode number state `|m⟩`. -/
def ket (m : ℕ) : OneFock := Finsupp.single m 1

/-- The two-mode number state `|k,l⟩`. -/
def ket2 (k l : ℕ) : TwoFock := Finsupp.single (k, l) 1

/-- Input creation operator: `a†|m⟩ = √(m+1) |m+1⟩`. -/
def aDag : OneFock →ₗ[ℂ] OneFock :=
  Finsupp.linearCombination ℂ fun m => ((√((m : ℝ) + 1) : ℝ) : ℂ) • ket (m + 1)

/-- Output creation operator: `b†|k,l⟩ = √(k+1) |k+1,l⟩`. -/
def bDag : TwoFock →ₗ[ℂ] TwoFock :=
  Finsupp.linearCombination ℂ fun p => ((√((p.1 : ℝ) + 1) : ℝ) : ℂ) • ket2 (p.1 + 1) p.2

/-- Environment creation operator: `e†|k,l⟩ = √(l+1) |k,l+1⟩`. -/
def eDag : TwoFock →ₗ[ℂ] TwoFock :=
  Finsupp.linearCombination ℂ fun p => ((√((p.2 : ℝ) + 1) : ℝ) : ℂ) • ket2 p.1 (p.2 + 1)

@[simp] lemma aDag_ket (m : ℕ) : aDag (ket m) = ((√((m : ℝ) + 1) : ℝ) : ℂ) • ket (m + 1) := by
  simp [aDag, ket, Finsupp.linearCombination_single]

@[simp] lemma bDag_ket2 (k l : ℕ) :
    bDag (ket2 k l) = ((√((k : ℝ) + 1) : ℝ) : ℂ) • ket2 (k + 1) l := by
  simp [bDag, ket2, Finsupp.linearCombination_single]

@[simp] lemma eDag_ket2 (k l : ℕ) :
    eDag (ket2 k l) = ((√((l : ℝ) + 1) : ℝ) : ℂ) • ket2 k (l + 1) := by
  simp [eDag, ket2, Finsupp.linearCombination_single]

lemma one_ext {M : Type*} [AddCommMonoid M] [Module ℂ M] {f g : OneFock →ₗ[ℂ] M}
    (h : ∀ m, f (ket m) = g (ket m)) : f = g :=
  Finsupp.lhom_ext' fun m => LinearMap.ext_ring (h m)

lemma two_ext {M : Type*} [AddCommMonoid M] [Module ℂ M] {f g : TwoFock →ₗ[ℂ] M}
    (h : ∀ k l, f (ket2 k l) = g (ket2 k l)) : f = g :=
  Finsupp.lhom_ext' fun p => LinearMap.ext_ring (h p.1 p.2)

/-- `[b†, e†] = 0`. -/
theorem commute_bDag_eDag : Commute (bDag : Module.End ℂ TwoFock) eDag := by
  refine two_ext fun k l => ?_
  simp only [Module.End.mul_apply, bDag_ket2, eDag_ket2, map_smul]
  exact smul_comm _ _ _

/-- The transformed creation operator `√η b† + √(1-η) e†`. -/
def create (η : ℝ) : Module.End ℂ TwoFock :=
  ((√η : ℝ) : ℂ) • bDag + ((√(1 - η) : ℝ) : ℂ) • eDag

/-- The single-mode beam splitter `V|m⟩ = (1/√m!) (√η b† + √(1-η) e†)^m |0,0⟩`. -/
def bsV (η : ℝ) : OneFock →ₗ[ℂ] TwoFock :=
  Finsupp.linearCombination ℂ fun m =>
    ((1 / √(m.factorial : ℝ) : ℝ) : ℂ) • (create η ^ m) (ket2 0 0)

lemma bsV_ket_def (η : ℝ) (m : ℕ) :
    bsV η (ket m) = ((1 / √(m.factorial : ℝ) : ℝ) : ℂ) • (create η ^ m) (ket2 0 0) := by
  simp [bsV, ket, Finsupp.linearCombination_single]

/-- `V|0⟩ = |0,0⟩`. -/
theorem bsV_vacuum (η : ℝ) : bsV η (ket 0) = ket2 0 0 := by
  simp [bsV_ket_def]

lemma sqrt_succ_factorial (m : ℕ) :
    √(((m + 1).factorial : ℕ) : ℝ) = √((m : ℝ) + 1) * √(m.factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Real.sqrt_mul (by positivity)]

/-- Intertwining on number states. -/
lemma bsV_aDag_ket (η : ℝ) (m : ℕ) :
    bsV η (aDag (ket m)) = create η (bsV η (ket m)) := by
  have h0 : √((m : ℝ) + 1) ≠ 0 := by positivity
  have h1 : √(m.factorial : ℝ) ≠ 0 := by positivity
  rw [aDag_ket, map_smul, bsV_ket_def, bsV_ket_def, map_smul, smul_smul, pow_succ',
    Module.End.mul_apply]
  congr 1
  rw [← Complex.ofReal_mul, sqrt_succ_factorial]
  congr 1
  field_simp

/-- **Intertwining**: `V (a† ψ) = (√η b† + √(1-η) e†) (V ψ)` on finite-support vectors. -/
theorem bsV_aDag (η : ℝ) (ψ : OneFock) : bsV η (aDag ψ) = create η (bsV η ψ) := by
  have h : bsV η ∘ₗ aDag = create η ∘ₗ bsV η := one_ext fun m => by
    simpa using bsV_aDag_ket η m
  exact LinearMap.congr_fun h ψ

/-! ### The amplitude theorem -/

/-- The single-mode loss amplitude. -/
def bsAmp (η : ℝ) (m l : ℕ) : ℝ := √((m.choose l : ℝ) * η ^ (m - l) * (1 - η) ^ l)

lemma bDag_pow_vac (k l : ℕ) :
    (bDag ^ k) (ket2 0 l) = ((√(k.factorial : ℝ) : ℝ) : ℂ) • ket2 k l := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, bDag_ket2, smul_smul,
      sqrt_succ_factorial, Complex.ofReal_mul, mul_comm]

lemma eDag_pow_vac (k l : ℕ) :
    (eDag ^ l) (ket2 k 0) = ((√(l.factorial : ℝ) : ℝ) : ℂ) • ket2 k l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, eDag_ket2, smul_smul,
      sqrt_succ_factorial, Complex.ofReal_mul, mul_comm]

/-- Binomial expansion of the transformed creation operator on the vacuum. -/
lemma create_pow_vac (η : ℝ) (m : ℕ) :
    (create η ^ m) (ket2 0 0) = ∑ l ∈ range (m + 1),
      (((m.choose l : ℝ) * √η ^ (m - l) * √(1 - η) ^ l *
        (√((m - l).factorial : ℝ) * √(l.factorial : ℝ)) : ℝ) : ℂ) • ket2 (m - l) l := by
  have hc : Commute (((√(1 - η) : ℝ) : ℂ) • (eDag : Module.End ℂ TwoFock))
      (((√η : ℝ) : ℂ) • bDag) :=
    (commute_bDag_eDag.symm.smul_left _).smul_right _
  rw [create, add_comm, hc.add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_pow, smul_pow]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.natCast_apply,
    map_smul, bDag_pow_vac, eDag_pow_vac, smul_smul, ← Nat.cast_smul_eq_nsmul ℂ]
  congr 1
  push_cast
  ring

lemma sqrt_pow_eq {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : √(x ^ k) = √x ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx k), ih, pow_succ]

/-- The real identity turning binomial-theorem coefficients into the square-root amplitude.
Valid at the endpoints: `0 ^ 0 = 1` on both sides. -/
lemma amp_coeff {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {m l : ℕ} (hl : l ≤ m) :
    (1 / √(m.factorial : ℝ)) * ((m.choose l : ℝ) * √η ^ (m - l) * √(1 - η) ^ l *
      (√((m - l).factorial : ℝ) * √(l.factorial : ℝ))) = bsAmp η m l := by
  have h1η : 0 ≤ 1 - η := sub_nonneg.2 hη1
  have hC : (0 : ℝ) < m.choose l := by exact_mod_cast Nat.choose_pos hl
  have hfac : ((m.choose l : ℝ) * (l.factorial : ℝ)) * ((m - l).factorial : ℝ) =
      (m.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hl
  have hs : √(m.factorial : ℝ) =
      √(m.choose l : ℝ) * √(l.factorial : ℝ) * √((m - l).factorial : ℝ) := by
    rw [← hfac, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have h2 : √(m.choose l : ℝ) ≠ 0 := (Real.sqrt_pos.2 hC).ne'
  have h3 : √(l.factorial : ℝ) ≠ 0 := by positivity
  have h4 : √((m - l).factorial : ℝ) ≠ 0 := by positivity
  rw [bsAmp, Real.sqrt_mul (by positivity), Real.sqrt_mul hC.le, sqrt_pow_eq hη0,
    sqrt_pow_eq h1η, hs]
  field_simp
  rw [Real.sq_sqrt hC.le]

/-- **Amplitude theorem**: `V|m⟩ = ∑_{l ≤ m} √(C(m,l) η^{m-l} (1-η)^l) |m-l,l⟩`. -/
theorem bsV_ket {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (m : ℕ) :
    bsV η (ket m) = ∑ l ∈ range (m + 1), ((bsAmp η m l : ℝ) : ℂ) • ket2 (m - l) l := by
  rw [bsV_ket_def, create_pow_vac, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [smul_smul, ← Complex.ofReal_mul,
    amp_coeff hη0 hη1 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))]

/-- Coefficients of `V|m⟩`. -/
lemma bsV_ket_apply {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (m k l : ℕ) :
    bsV η (ket m) (k, l) = if k + l = m then ((bsAmp η m l : ℝ) : ℂ) else 0 := by
  classical
  rw [bsV_ket hη0 hη1, Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, ket2, Finsupp.single_apply, Prod.mk.injEq, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single l]
    · rw [ite_eq_left ⟨by omega, rfl⟩]
    · intro b _ hb; rw [ite_eq_right (fun h' => hb h'.2)]
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  · refine Finset.sum_eq_zero fun b hb => ite_eq_right ?_
    rintro ⟨h1, rfl⟩
    have := Finset.mem_range.1 hb
    omega

/-! ### Isometry -/

/-- The inner product on finite-support vectors, conjugate-linear in the first slot. -/
def ip {α : Type*} (φ ψ : α →₀ ℂ) : ℂ := φ.sum fun a c => star c * ψ a

lemma ip_add_left {α : Type*} (φ₁ φ₂ ψ : α →₀ ℂ) : ip (φ₁ + φ₂) ψ = ip φ₁ ψ + ip φ₂ ψ := by
  classical
  exact Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])

lemma ip_add_right {α : Type*} (φ ψ₁ ψ₂ : α →₀ ℂ) : ip φ (ψ₁ + ψ₂) = ip φ ψ₁ + ip φ ψ₂ := by
  simp [ip, mul_add, Finsupp.sum_add]

lemma ip_smul_left {α : Type*} (c : ℂ) (φ ψ : α →₀ ℂ) : ip (c • φ) ψ = star c * ip φ ψ := by
  classical
  rw [ip, Finsupp.sum_smul_index (by simp), ip, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  by_cases hc : c = 0
  · simp [hc]
  · exact Finset.sum_congr rfl fun a _ => by simp [mul_assoc]

lemma ip_smul_right {α : Type*} (c : ℂ) (φ ψ : α →₀ ℂ) : ip φ (c • ψ) = c * ip φ ψ := by
  simp only [ip, Finsupp.sum, Finset.mul_sum, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma ip_single_single {α : Type*} [DecidableEq α] (a b : α) (c d : ℂ) :
    ip (Finsupp.single a c) (Finsupp.single b d) = if a = b then star c * d else 0 := by
  rw [ip, Finsupp.sum_single_index (by simp), Finsupp.single_apply]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd h₁.symm h₂
  · exact absurd h₂.symm h₁
  · simp

/-- Binomial normalization. -/
lemma sum_bsAmp_sq {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (m : ℕ) :
    ∑ l ∈ range (m + 1), bsAmp η m l * bsAmp η m l = 1 := by
  have h1η : 0 ≤ 1 - η := sub_nonneg.2 hη1
  have h := add_pow (1 - η) η m
  rw [sub_add_cancel, one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [bsAmp, Real.mul_self_sqrt (by positivity)]
  ring

/-- **Orthonormal images**: `⟨V m, V m'⟩ = δ_{m m'}`. -/
theorem bsV_orthonormal {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (m m' : ℕ) :
    ip (bsV η (ket m)) (bsV η (ket m')) = if m = m' then 1 else 0 := by
  classical
  have hsupp : (bsV η (ket m)).support ⊆
      (range (m + 1)).image fun l => (m - l, l) := by
    intro p hp
    obtain ⟨k, l⟩ := p
    have hne : bsV η (ket m) (k, l) ≠ 0 := Finsupp.mem_support_iff.1 hp
    rw [bsV_ket_apply hη0 hη1] at hne
    have hkl : k + l = m := by
      by_contra h
      exact hne (ite_eq_right h)
    refine Finset.mem_image.2 ⟨l, Finset.mem_range.2 (by omega), ?_⟩
    simp only [Prod.mk.injEq, and_true]
    omega
  have hinj : Set.InjOn (fun l : ℕ => (m - l, l)) (range (m + 1) : Set ℕ) :=
    fun a _ b _ hab => (Prod.mk.inj hab).2
  rw [ip, Finsupp.sum_of_support_subset _ hsupp _ (by simp), Finset.sum_image hinj]
  have hterm : ∀ l ∈ range (m + 1),
      star (bsV η (ket m) (m - l, l)) * bsV η (ket m') (m - l, l) =
        if m = m' then ((bsAmp η m l * bsAmp η m l : ℝ) : ℂ) else 0 := by
    intro l hl
    have hle : l ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    rw [bsV_ket_apply hη0 hη1, bsV_ket_apply hη0 hη1, ite_eq_left (Nat.sub_add_cancel hle),
      Nat.sub_add_cancel hle]
    split_ifs with h
    · subst h
      simp [Complex.conj_ofReal]
    · simp
  rw [Finset.sum_congr rfl hterm]
  split_ifs with h
  · rw [← Complex.ofReal_sum, sum_bsAmp_sq hη0 hη1, Complex.ofReal_one]
  · simp

lemma single_eq_smul_ket (m : ℕ) (c : ℂ) : (Finsupp.single m c : OneFock) = c • ket m := by
  simp [ket]

/-- **Isometry** of the single-mode beam splitter on finite-support vectors. -/
theorem bsV_isometry {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (φ ψ : OneFock) :
    ip (bsV η φ) (bsV η ψ) = ip φ ψ := by
  classical
  induction φ using Finsupp.induction_linear with
  | zero => simp [ip]
  | add φ₁ φ₂ h₁ h₂ => rw [map_add, ip_add_left, ip_add_left, h₁, h₂]
  | single m c =>
    induction ψ using Finsupp.induction_linear with
    | zero => simp [ip]
    | add ψ₁ ψ₂ h₁ h₂ => rw [map_add, ip_add_right, ip_add_right, h₁, h₂]
    | single m' d =>
      rw [single_eq_smul_ket m c, single_eq_smul_ket m' d, map_smul, map_smul, ip_smul_left,
        ip_smul_right, bsV_orthonormal hη0 hη1, ip_smul_left, ip_smul_right, ket, ket,
        ip_single_single]
      simp

end

end BeamSplitter

/-! ### The `n`-mode beam splitter and the main theorem -/

open BeamSplitter

variable {n L : ℕ}

noncomputable section

/-- The `n`-mode beam splitter on `Occ n L`, as the componentwise product of the single-mode
isometry `bsV`. Rows are indexed by (output `B`, environment `E`) occupations. -/
def beamSplitterMat (η : ℝ) : Matrix (Occ n L × Occ n L) (Occ n L) ℂ :=
  fun p m => ∏ j, bsV η (ket ((m : Fin n → ℕ) j))
    (((p.1 : Fin n → ℕ) j), ((p.2 : Fin n → ℕ) j))

/-- Partial trace over the environment. -/
def partialTraceEnv (X : Matrix (Occ n L × Occ n L) (Occ n L × Occ n L) ℂ) :
    Matrix (Occ n L) (Occ n L) ℂ :=
  fun r r' => ∑ ℓ, X (r, ℓ) (r', ℓ)

/-- The occupation `m - ℓ` (truncated), which stays in `Occ n L`. -/
def subOcc (m ℓ : Occ n L) : Occ n L :=
  ⟨(m : Fin n → ℕ) - ℓ, mem_occSet.2 (le_trans (photons_mono tsub_le_self) (mem_occSet.1 m.2))⟩

/-- Entries of the `n`-mode beam splitter are the entries of the project's Kraus operators. -/
theorem beamSplitterMat_apply {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (r ℓ m : Occ n L) :
    beamSplitterMat η (r, ℓ) m = lossKraus η ℓ r m := by
  classical
  simp only [beamSplitterMat, lossKraus, bsV_ket_apply hη0 hη1]
  split_ifs with h
  · rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hj : (m : Fin n → ℕ) j = (r : Fin n → ℕ) j + (ℓ : Fin n → ℕ) j := congrFun h j
    rw [ite_eq_left hj.symm, bsAmp, hj, Nat.add_sub_cancel]
  · have : ∃ j, (r : Fin n → ℕ) j + (ℓ : Fin n → ℕ) j ≠ (m : Fin n → ℕ) j := by
      by_contra hne
      push Not at hne
      exact h (funext fun j => (hne j).symm)
    obtain ⟨j, hj⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

/-- **`n`-mode expansion**:
`V|m⟩ = ∑_{ℓ ≤ m} (∏ⱼ √(C(mⱼ,ℓⱼ) η^{mⱼ-ℓⱼ} (1-η)^{ℓⱼ})) |m-ℓ⟩_B |ℓ⟩_E`. -/
theorem beamSplitterMat_col {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (m : Occ n L) :
    (fun p => beamSplitterMat η p m) =
      ∑ ℓ ∈ (Finset.univ : Finset (Occ n L)).filter
          (fun ℓ : Occ n L => (ℓ : Fin n → ℕ) ≤ (m : Fin n → ℕ)),
        (((∏ j, bsAmp η ((m : Fin n → ℕ) j) ((ℓ : Fin n → ℕ) j) : ℝ)) : ℂ) •
          (Pi.single (subOcc m ℓ, ℓ) 1 : Occ n L × Occ n L → ℂ) := by
  classical
  funext ⟨r, ℓ⟩
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, Prod.mk.injEq, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [beamSplitterMat_apply hη0 hη1, lossKraus]
  by_cases h : (m : Fin n → ℕ) = (r : Fin n → ℕ) + (ℓ : Fin n → ℕ)
  · have hle : (ℓ : Fin n → ℕ) ≤ (m : Fin n → ℕ) := h ▸ le_add_self
    have hr : r = subOcc m ℓ := Subtype.ext (by
      change (r : Fin n → ℕ) = (m : Fin n → ℕ) - ℓ
      rw [h, add_tsub_cancel_right])
    rw [ite_eq_left h, Finset.sum_eq_single ℓ]
    · rw [ite_eq_left ⟨hr, rfl⟩]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      have hj : (m : Fin n → ℕ) j - (ℓ : Fin n → ℕ) j = (r : Fin n → ℕ) j := by
        rw [congrFun h j, Pi.add_apply, Nat.add_sub_cancel]
      rw [bsAmp, hj]
    · intro b _ hb
      exact ite_eq_right fun h' => hb h'.2.symm
    · intro hn
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ ℓ, hle⟩) hn
  · rw [ite_eq_right h]
    symm
    refine Finset.sum_eq_zero fun b hb => ite_eq_right ?_
    rintro ⟨h1, rfl⟩
    apply h
    have hle := (Finset.mem_filter.1 hb).2
    rw [h1]
    exact (tsub_add_cancel_of_le hle).symm

/-- **Isometry**: `Vᴴ V = 1`. -/
theorem beamSplitterMat_isometry {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (beamSplitterMat (n := n) (L := L) η)ᴴ * beamSplitterMat (n := n) (L := L) η = 1 := by
  rw [← lossKraus_complete (n := n) (L := L) hη0 hη1]
  ext m m'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Fintype.sum_prod_type, beamSplitterMat_apply hη0 hη1]
  exact Finset.sum_comm

/-- **Main theorem**: the project's Fock-basis Kraus channel is the partial trace over the
environment of the beam-splitter isometry. -/
theorem lossChannel_eq_partialTrace_beamSplitter {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (ρ : Matrix (Occ n L) (Occ n L) ℂ) :
    partialTraceEnv (beamSplitterMat (n := n) (L := L) η * ρ *
      (beamSplitterMat (n := n) (L := L) η)ᴴ) = lossChannel η ρ := by
  ext r r'
  simp only [partialTraceEnv, lossChannel, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, beamSplitterMat_apply hη0 hη1]

end

end QIQCOP
