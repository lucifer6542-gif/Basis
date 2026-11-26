module

public import SquareBasis.Toric

/-!
# Theorem 1.1 with the count `N - rank A_M`, and Proposition 8.2

* `thm11` — **Theorem 1.1** as stated in the paper: for `rank M ≥ 1`, `ker_ℤ A_M` has a `ℤ`-basis
  consisting of `N - rank A_M` squares.
* `prop82` — **Proposition 8.2**: for `rank M ≥ 1`, the squares generate `ker_ℤ A_M`, i.e.
  `L_□(M) = ker_ℤ A_M` (here derived from Theorem 1.1; the second proof in the paper, from the
  theorem of Lasoń–Michałek, is not formalized).
-/

@[expose] public section

namespace SquareBasis

open Matroid Module

variable {α : Type*} (M : Matroid α) [M.Finite]

/-- **Theorem 1.1.** -/
theorem thm11 [M.RankPos] :
    ∃ R : Finset (Bases M →₀ ℤ), (∀ z ∈ R, IsSquare M z) ∧
      R.card = Nat.card (Bases M) - finrank ℤ (LinearMap.range (incidence M)) ∧
      LinearIndependent ℤ (fun z : R => (z : Bases M →₀ ℤ)) ∧
      Submodule.span ℤ (R : Set (Bases M →₀ ℤ)) = LinearMap.ker (incidence M) := by
  obtain ⟨R, hsq, hc, hli, hspan⟩ := exists_square_finset (M := M)
  exact ⟨R, hsq, hc.trans (codim_eq (M := M)), hli, hspan⟩

/-- **Proposition 8.2.** `L_□(M) = ker_ℤ A_M` if `rank M ≥ 1`. -/
theorem prop82 [M.RankPos] :
    Submodule.span ℤ {z : Bases M →₀ ℤ | IsSquare M z} = LinearMap.ker (incidence M) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    exact hz.mem_ker
  · obtain ⟨S, hsq, -, hspan⟩ := square_basis_theorem_paper M
    rw [← hspan]
    exact Submodule.span_mono hsq

end SquareBasis
