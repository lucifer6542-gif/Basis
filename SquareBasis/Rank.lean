module

public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Combinatorics.Matroid.Rank.Finite
public import Mathlib.Combinatorics.Matroid.Circuit
public import Mathlib.Combinatorics.Matroid.Minor.Delete
public import Mathlib.Combinatorics.Matroid.Minor.Contract
public import Mathlib.Tactic.Linarith

/-!
# Integer-valued rank of a finite matroid

For a finite matroid we use the integer rank `r X = (M.eRk X).toNat`, viewed in `ℤ`,
and record the facts used later: monotonicity, submodularity, the rank of independent
sets and circuits, and the rank of the dual matroid.
-/

@[expose] public section

namespace SquareBasis

open Matroid Set

variable {α : Type*}

/-- The integer rank of a set. -/
noncomputable def rk (M : Matroid α) (X : Set α) : ℤ := ((M.eRk X).toNat : ℤ)

variable {M : Matroid α} [M.Finite] {X Y : Set α}

theorem eRk_eq_rk (M : Matroid α) [M.Finite] (X : Set α) :
    M.eRk X = ((M.eRk X).toNat : ℕ∞) :=
  (ENat.natCast_toNat ((M.eRk_ne_top_iff).2 (M.isRkFinite_set X))).symm

theorem rk_nonneg (M : Matroid α) (X : Set α) : 0 ≤ rk M X := by
  unfold rk; positivity

theorem rk_mono (M : Matroid α) [M.Finite] (h : X ⊆ Y) : rk M X ≤ rk M Y := by
  have h1 := M.eRk_mono h
  rw [eRk_eq_rk M X, eRk_eq_rk M Y] at h1
  unfold rk
  exact_mod_cast h1

theorem rk_submod (M : Matroid α) [M.Finite] (X Y : Set α) :
    rk M (X ∩ Y) + rk M (X ∪ Y) ≤ rk M X + rk M Y := by
  have h1 := M.eRk_inter_add_eRk_union_le X Y
  rw [eRk_eq_rk M X, eRk_eq_rk M Y, eRk_eq_rk M (X ∩ Y), eRk_eq_rk M (X ∪ Y)] at h1
  unfold rk
  exact_mod_cast h1

theorem rk_union_le (M : Matroid α) [M.Finite] (X Y : Set α) :
    rk M (X ∪ Y) ≤ rk M X + rk M Y := by
  have := rk_submod M X Y
  have := rk_nonneg M (X ∩ Y)
  linarith

theorem rk_indep {I : Set α} (hI : M.Indep I) : rk M I = I.ncard := by
  have h1 := hI.eRk_eq_encard
  have hfin : I.Finite := M.ground_finite.subset hI.subset_ground
  rw [eRk_eq_rk M I, ← hfin.cast_ncard_eq] at h1
  unfold rk
  exact_mod_cast h1

theorem rk_isBasis' {I : Set α} (hI : M.IsBasis' I X) : rk M X = I.ncard := by
  have h1 := hI.eRk_eq_encard
  have hfin : I.Finite := M.ground_finite.subset hI.indep.subset_ground
  rw [eRk_eq_rk M X, ← hfin.cast_ncard_eq] at h1
  unfold rk
  exact_mod_cast h1

theorem rk_le_ncard (M : Matroid α) [M.Finite] {X : Set α} (hX : X.Finite) :
    rk M X ≤ X.ncard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [rk_isBasis' hI]
  exact_mod_cast Set.ncard_le_ncard hI.subset hX

theorem rk_empty (M : Matroid α) [M.Finite] : rk M ∅ = 0 := by
  have := rk_le_ncard M (X := ∅) Set.finite_empty
  have := rk_nonneg M ∅
  simp at *; omega

theorem ncard_le_rk_of_indep {I : Set α} (hI : M.Indep I) (hIX : I ⊆ X) :
    (I.ncard : ℤ) ≤ rk M X :=
  rk_indep hI ▸ rk_mono M hIX

theorem rk_circuit_add_one {C : Set α} (hC : M.IsCircuit C) : rk M C + 1 = C.ncard := by
  have h1 := hC.eRk_add_one_eq
  have hfin : C.Finite := M.ground_finite.subset hC.subset_ground
  rw [eRk_eq_rk M C, ← hfin.cast_ncard_eq] at h1
  unfold rk
  exact_mod_cast h1

theorem rk_inter_ground (M : Matroid α) [M.Finite] (X : Set α) : rk M (X ∩ M.E) = rk M X := by
  unfold rk; rw [M.eRk_inter_ground]

theorem rk_ground_eq_of_isBase {B : Set α} (hB : M.IsBase B) : rk M M.E = B.ncard := by
  rw [← rk_indep hB.indep]
  unfold rk
  rw [hB.eRk_eq_eRank, ← M.eRk_ground]

theorem rk_singleton_le (M : Matroid α) [M.Finite] (e : α) : rk M {e} ≤ 1 := by
  have := rk_le_ncard M (Set.finite_singleton e)
  simpa using this

instance dual_finite (M : Matroid α) [M.Finite] : M✶.Finite := ⟨by simpa using M.ground_finite⟩

/-- Rank in the dual matroid: `r*(X) = |X| + r(E \ X) - r(E)` for `X ⊆ E`. -/
theorem rk_dual (M : Matroid α) [M.Finite] {X : Set α} (hX : X ⊆ M.E) :
    rk M✶ X = X.ncard + rk M (M.E \ X) - rk M M.E := by
  have h1 := M.eRk_dual_add_eRank X hX
  have hfin : X.Finite := M.ground_finite.subset hX
  rw [eRk_eq_rk M✶ X, eRk_eq_rk M (M.E \ X), ← hfin.cast_ncard_eq, ← M.eRk_ground,
    eRk_eq_rk M M.E] at h1
  unfold rk
  have h2 : (M✶.eRk X).toNat + (M.eRk M.E).toNat = (M.eRk (M.E \ X)).toNat + X.ncard := by
    exact_mod_cast h1
  omega

/-- A set `B` with `|B| = r(E)` that is independent is a base. -/
theorem isBase_of_indep_ncard {B : Set α} (hB : M.Indep B) (h : rk M M.E ≤ B.ncard) :
    M.IsBase B := by
  have hfin : B.Finite := M.ground_finite.subset hB.subset_ground
  refine hB.isBase_of_eRk_ge hfin ?_
  rw [← M.eRk_ground, eRk_eq_rk M M.E, hB.eRk_eq_encard, ← hfin.cast_ncard_eq]
  unfold rk at h
  exact_mod_cast h

end SquareBasis
