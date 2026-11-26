module

public import Mathlib.Combinatorics.Matroid.Dual
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# A Square Basis Theorem for Matroids — definitions

Youngsu Kim, *A Square Basis Theorem for Matroids*.

This file sets up the statement using Mathlib's own definition of a matroid
(`Matroid α`, `Matroid.IsBase`) and Mathlib's own notions of linear independence
and span over `ℤ`, so that the statement can be checked independently of the paper.

* `SquareBasis.Bases M` — the set 𝓑 of bases of `M`, used as an index type.
* `SquareBasis.incidence M` — the basis incidence matrix `A_M`, as the `ℤ`-linear map
  `ℤ^(𝓑) → ℤ^α`, `e_B ↦ 𝟙_B`.
* `SquareBasis.IsSquare M z` — `z = e_{B+i} - e_{B+j} - e_{B'+i} + e_{B'+j}` with
  `i ≠ j`, `B ≠ B'`, `i, j ∉ B ∪ B'` and all four sets bases (Definition 2.1).
* `SquareBasis.HasSquareBasis M` — `ker_ℤ A_M` has a `ℤ`-basis consisting of squares.

The main theorem is stated in `SquareBasis/PaperRoute.lean`.
-/

@[expose] public section

namespace SquareBasis

open Matroid

variable {α : Type*}

/-- The bases of `M`, as an index type. -/
abbrev Bases (M : Matroid α) := {B : Set α // M.IsBase B}

/-- The basis incidence matrix `A_M : ℤ^(𝓑) → ℤ^α`, sending `e_B` to the indicator of `B`. -/
noncomputable def incidence (M : Matroid α) : (Bases M →₀ ℤ) →ₗ[ℤ] (α → ℤ) :=
  Finsupp.linearCombination ℤ (fun B : Bases M => Set.indicator B.1 (fun _ => (1 : ℤ)))

/-- `z` is a square relation `e_{B+i} - e_{B+j} - e_{B'+i} + e_{B'+j}`. -/
def IsSquare (M : Matroid α) (z : Bases M →₀ ℤ) : Prop :=
  ∃ (i j : α) (B B' : Set α) (h₁ : M.IsBase (insert i B)) (h₂ : M.IsBase (insert j B))
    (h₃ : M.IsBase (insert i B')) (h₄ : M.IsBase (insert j B')),
    i ≠ j ∧ B ≠ B' ∧ i ∉ B ∧ j ∉ B ∧ i ∉ B' ∧ j ∉ B' ∧
    z = Finsupp.single ⟨_, h₁⟩ 1 - Finsupp.single ⟨_, h₂⟩ 1
        - Finsupp.single ⟨_, h₃⟩ 1 + Finsupp.single ⟨_, h₄⟩ 1

/-- Sanity check of the definitions: every square relation lies in `ker_ℤ A_M`. -/
theorem IsSquare.mem_ker {M : Matroid α} {z : Bases M →₀ ℤ} (hz : IsSquare M z) :
    z ∈ LinearMap.ker (incidence M) := by
  obtain ⟨i, j, B, B', h₁, h₂, h₃, h₄, hij, -, hiB, hjB, hiB', hjB', rfl⟩ := hz
  rw [LinearMap.mem_ker]
  funext a
  simp only [incidence, map_add, map_sub, Finsupp.linearCombination_single, one_smul,
    Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
  by_cases hai : a = i
  · subst hai
    simp [hij, hiB, hiB']
  · by_cases haj : a = j
    · subst haj
      simp [hai, hjB, hjB']
    · simp only [Set.indicator]
      split_ifs <;> simp_all

/-- `M` has a square basis: some set of square relations is a `ℤ`-basis of `ker_ℤ A_M`.
(Theorem 1.1, `square_basis_theorem_paper` in `PaperRoute.lean`, says that every matroid of
rank at least one has one.) -/
def HasSquareBasis (M : Matroid α) : Prop :=
  ∃ S : Set (Bases M →₀ ℤ), (∀ z ∈ S, IsSquare M z) ∧
    LinearIndependent ℤ (fun z : S => (z : Bases M →₀ ℤ)) ∧
    Submodule.span ℤ S = LinearMap.ker (incidence M)

end SquareBasis
