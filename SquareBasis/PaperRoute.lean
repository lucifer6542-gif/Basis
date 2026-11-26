module

public import SquareBasis.Section3
public import SquareBasis.Section4

/-!
# Theorem 1.1 along the route of the paper

The proof of Theorem 1.1 in the paper: delete loops (Proposition 2.3(b)); the resulting
matroid is the direct sum of connected components of rank at least one; each has a square
basis by Theorem 4.6, and Proposition 3.1 combines them. Here the direct-sum decomposition
is carried out one separator at a time, by induction on the size of the ground set.
-/

@[expose] public section

namespace SquareBasis

open Matroid Set

universe u

variable {α : Type u}

/-- **Proposition 2.3(a).** If `rank M = 0`, there are no squares, while `ker_ℤ A_M` is
everything (`𝓑 = {∅}`, so `ker_ℤ A_M = ℤ`). Hence the rank condition in Theorem 1.1 is
necessary. -/
theorem prop23a (M : Matroid α) (h : M.IsBase ∅) :
    (∀ z, ¬ IsSquare M z) ∧ LinearMap.ker (incidence M) = ⊤ ∧ ¬ HasSquareBasis M := by
  have hall : ∀ B, M.IsBase B → B = ∅ := fun B hB =>
    (h.eq_of_subset_isBase hB (empty_subset B)).symm
  have hnosq : ∀ z, ¬ IsSquare M z := by
    rintro z ⟨i, j, B, B', h₁, -, -, -, -, -, -, -, -, -, -⟩
    have := hall _ h₁
    exact (insert_nonempty i B).ne_empty this
  have hker : LinearMap.ker (incidence M) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    rw [LinearMap.mem_ker]
    funext a
    rw [incidence_apply]
    refine Finset.sum_eq_zero (fun B _ => ?_)
    have hB : (B : Set α) = ∅ := hall _ B.2
    simp [hB]
  refine ⟨hnosq, hker, ?_⟩
  rintro ⟨S, hS, hli, hspan⟩
  have hSe : S = ∅ := by
    ext z; simp only [mem_empty_iff_false, iff_false]
    exact fun hz => hnosq z (hS z hz)
  rw [hSe, Submodule.span_empty, hker] at hspan
  -- `ℤ^𝓑 ≠ 0` because `∅` is a base
  have : Finsupp.single (⟨∅, h⟩ : Bases M) (1 : ℤ) ∈ (⊥ : Submodule ℤ (Bases M →₀ ℤ)) := by
    rw [hspan]; exact Submodule.mem_top
  rw [Submodule.mem_bot] at this
  have := congrArg (fun F => F ⟨∅, h⟩) this
  simp at this

/-- **Proposition 2.3(b).** Deleting a loop changes neither `ker_ℤ A_M` nor the squares. -/
theorem prop23b (M : Matroid α) [M.Finite] {v : α} (hv : rk M {v} = 0)
    (h : HasSquareBasis (M ＼ {v})) : HasSquareBasis M := by
  have hvB : ∀ {B}, M.IsBase B → v ∉ B := by
    intro B hB hvB
    have := rk_indep (hB.indep.subset (singleton_subset_iff.2 hvB))
    rw [hv, ncard_singleton] at this
    norm_num at this
  have hrX : rk M (M.E \ {v}) = rk M M.E := by
    have h1 := rk_union_le M {v} (M.E \ {v})
    have h2 := rk_mono M (show M.E \ {v} ⊆ M.E from sdiff_subset)
    by_cases hvE : v ∈ M.E
    · rw [union_sdiff_cancel (singleton_subset_iff.2 hvE)] at h1
      linarith
    · rw [sdiff_singleton_eq_self hvE]
  have hbase : ∀ {B}, (M ＼ {v}).IsBase B ↔ M.IsBase B := by
    intro B
    rw [delete_isBase_iff_of_rk hrX]
    exact ⟨fun h => h.1, fun h => ⟨h, hvB h⟩⟩
  let e : Bases (M ＼ {v}) ≃ Bases M :=
    { toFun := fun B => ⟨B.1, hbase.1 B.2⟩
      invFun := fun B => ⟨B.1, hbase.2 B.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Φ : (Bases (M ＼ {v}) →₀ ℤ) ≃ₗ[ℤ] (Bases M →₀ ℤ) := Finsupp.domLCongr e
  have hinc : ∀ f, incidence M (Φ f) = incidence (M ＼ {v}) f := by
    intro f
    simp only [Φ, incidence, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_eq_mapDomain, Finsupp.linearCombination_mapDomain]
    rfl
  refine h.of_linearEquiv Φ (fun f => ?_) (fun z hz => ?_)
  · simp only [LinearMap.mem_ker, hinc]
  · obtain ⟨i, j, B, B', h₁, h₂, h₃, h₄, hij, hBB', hiB, hjB, hiB', hjB', rfl⟩ := hz
    refine ⟨i, j, B, B', hbase.1 h₁, hbase.1 h₂, hbase.1 h₃, hbase.1 h₄, hij, hBB', hiB, hjB,
      hiB', hjB', ?_⟩
    simp only [Φ, map_add, map_sub, Finsupp.domLCongr_single]
    rfl

/-- A nonempty loopless restriction has positive rank. -/
theorem rankPos_restrict {M : Matroid α} [M.Finite] {Z : Set α} (hZE : Z ⊆ M.E)
    (hZ : Z.Nonempty) (hloop : ∀ v ∈ M.E, rk M {v} ≠ 0) : (M ↾ Z).RankPos := by
  refine ⟨fun h => ?_⟩
  rw [isBase_restrict_iff'] at h
  have h1 := rk_isBasis' h
  obtain ⟨x, hx⟩ := hZ
  have h2 := rk_mono M (singleton_subset_iff.2 hx)
  have h3 := hloop x (hZE hx)
  have h4 := rk_nonneg M {x}
  rw [h1, ncard_empty] at h2
  push_cast at h2
  omega

/-- **Theorem 1.1, along the route of the paper.** -/
theorem hasSquareBasis_paper (n : ℕ) :
    ∀ (M : Matroid α) [M.Finite] [M.RankPos], M.E.ncard = n → HasSquareBasis M := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ hn
  by_cases hl : ∃ v ∈ M.E, rk M {v} = 0
  · -- delete a loop (Proposition 2.3(b))
    obtain ⟨v, hvE, hv⟩ := hl
    have hrX : rk M (M.E \ {v}) = rk M M.E := by
      have h1 := rk_union_le M {v} (M.E \ {v})
      have h2 := rk_mono M (show M.E \ {v} ⊆ M.E from sdiff_subset)
      rw [union_sdiff_cancel (singleton_subset_iff.2 hvE)] at h1
      linarith
    have : (M ＼ {v}).RankPos := rankPos_delete hrX
    have hlt : (M ＼ {v}).E.ncard < n := by
      rw [delete_ground, ← hn]; exact Set.ncard_sdiff_singleton_lt_of_mem hvE M.ground_finite
    exact prop23b M hv (ih _ hlt (M ＼ {v}) rfl)
  push Not at hl
  by_cases hconn : Conn M
  · -- a connected matroid (Theorem 4.6)
    exact thm46 _ M rfl hconn
  · -- a nontrivial separator splits `M` as a direct sum (Proposition 3.1)
    simp only [Conn, ConnIn, not_forall, not_or] at hconn
    obtain ⟨Z, hZE, hsplit, hZe, hZE'⟩ := hconn
    have hX : Sep M Z := ⟨hZE, hsplit⟩
    have hZne : Z.Nonempty := ne_empty_iff_nonempty.1 hZe
    have hCne : (M.E \ Z).Nonempty := by
      rw [← ne_empty_iff_nonempty]
      intro h
      exact hZE' (subset_antisymm hZE (sdiff_eq_empty.1 h))
    have : (M ↾ Z).Finite := restrict_finite (M.ground_finite.subset hZE)
    have : (M ↾ (M.E \ Z)).Finite := restrict_finite (M.ground_finite.subset sdiff_subset)
    have : (M ↾ Z).RankPos := rankPos_restrict hZE hZne hl
    have : (M ↾ (M.E \ Z)).RankPos := rankPos_restrict sdiff_subset hCne hl
    have hlt1 : (M ↾ Z).E.ncard < n := by
      rw [restrict_ground_eq, ← hn]
      exact Set.ncard_lt_ncard (ssubset_of_subset_of_ne hZE hZE') M.ground_finite
    have hlt2 : (M ↾ (M.E \ Z)).E.ncard < n := by
      rw [restrict_ground_eq, ← hn]
      obtain ⟨z, hz⟩ := hZne
      refine Set.ncard_lt_ncard (ssubset_of_subset_of_ne sdiff_subset (fun h => ?_)) M.ground_finite
      have : z ∈ M.E \ Z := by rw [h]; exact hZE hz
      exact this.2 hz
    exact prop31 hX (ih _ hlt1 (M ↾ Z) rfl) (ih _ hlt2 (M ↾ (M.E \ Z)) rfl)

/-- **Square Basis Theorem** (Theorem 1.1), proved along the route of the paper:
Proposition 2.3(b), Proposition 3.1, Theorem 4.6 (Tutte's theorem, Theorem 4.5 with
Section 5, Proposition 4.4, Theorem 4.3) and Lemma 2.4. -/
theorem square_basis_theorem_paper (M : Matroid α) [M.Finite] [M.RankPos] :
    ∃ S : Set (Bases M →₀ ℤ), (∀ z ∈ S, IsSquare M z) ∧
      LinearIndependent ℤ (fun z : S => (z : Bases M →₀ ℤ)) ∧
      Submodule.span ℤ S = LinearMap.ker (incidence M) :=
  hasSquareBasis_paper _ M rfl

end SquareBasis
