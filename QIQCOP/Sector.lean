import QIQCOP.Defs

/-!
# Photon-number sectors of `n` bosonic modes

A Fock basis vector of `n` modes is an occupation vector `m : Fin n → ℕ`.
The `k`-photon sector is `sector n k = {m | ∑ j, m j = k}` and the truncated
space with at most `L` photons is `occSet n L`.
-/

open Finset

namespace QIQCOP

/-- Total photon number of an occupation vector. -/
def photons {n : ℕ} (m : Fin n → ℕ) : ℕ := ∑ j, m j

/-- Basis of the exactly-`k`-photon sector of `n` modes. -/
abbrev sector (n k : ℕ) : Finset (Fin n → ℕ) := piAntidiag univ k

/-- Basis of the space of at most `L` photons in `n` modes. -/
def occSet (n L : ℕ) : Finset (Fin n → ℕ) := (range (L + 1)).biUnion (sector n)

/-- Index type of the Fock basis truncated at `L` photons. -/
abbrev Occ (n L : ℕ) := ↥(occSet n L)

lemma mem_sector {n k : ℕ} {m : Fin n → ℕ} : m ∈ sector n k ↔ photons m = k := by
  simp [sector, photons, mem_piAntidiag]

lemma mem_occSet {n L : ℕ} {m : Fin n → ℕ} : m ∈ occSet n L ↔ photons m ≤ L := by
  simp only [occSet, mem_biUnion, mem_range, mem_sector]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨photons m, by omega, rfl⟩

/-- **Stars and bars**: the `k`-photon sector of `n` modes has `C(n+k-1, k)` basis vectors. -/
theorem card_sector (n k : ℕ) : (sector n k).card = (n + k - 1).choose k := by
  classical
  rw [sector, ← map_sym_eq_piAntidiag, card_map, sym_univ, card_univ, Sym.card_sym_eq_choose,
    Fintype.card_fin]

lemma card_sector_real (n k : ℕ) : ((sector n k).card : ℝ) = sectorDim n k := by
  rw [card_sector]; rfl

end QIQCOP
