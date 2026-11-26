module

public import SquareBasis.Connectivity

/-!
# Exchange pairs avoiding a fixed element

`StarD M v` says: whenever `D ∋ v` and `D + i`, `D + j` are bases, there is `D' ∌ v` with
`D' + i`, `D' + j` bases. This is the condition under which a square basis of `M ＼ v`
lifts to `M`.
-/

@[expose] public section

namespace SquareBasis

open Matroid Set

variable {α : Type*} {M : Matroid α} [M.Finite]

/-- The exchange condition at `v`. -/
def StarD (M : Matroid α) (v : α) : Prop :=
  ∀ (D : Set α) (i j : α), i ≠ j → v ∈ D → i ∉ D → j ∉ D → M.IsBase (insert i D) →
    M.IsBase (insert j D) →
    ∃ D', v ∉ D' ∧ i ∉ D' ∧ j ∉ D' ∧ M.IsBase (insert i D') ∧ M.IsBase (insert j D')

/-- A circuit through `i ≠ j` avoiding a non-coloop `v` yields bases `D' + i`, `D' + j`
with `v ∉ D'`. -/
theorem exists_pair_of_isCircuit {K : Set α} {i j v : α} (hK : M.IsCircuit K) (hiK : i ∈ K)
    (hjK : j ∈ K) (hij : i ≠ j) (hvK : v ∉ K) (hv : rk M (M.E \ {v}) = rk M M.E) :
    ∃ D', v ∉ D' ∧ i ∉ D' ∧ j ∉ D' ∧ M.IsBase (insert i D') ∧ M.IsBase (insert j D') := by
  have hKj : M.Indep (K \ {j}) := hK.ssubset_indep
    (ssubset_of_subset_of_ne sdiff_subset (fun h => by
      have : j ∈ K \ {j} := by rw [h]; exact hjK
      exact this.2 rfl))
  have hKjE : K \ {j} ⊆ M.E \ {v} := fun x hx =>
    ⟨hK.subset_ground hx.1, fun h => hvK (by rw [mem_singleton_iff] at h; exact h ▸ hx.1)⟩
  obtain ⟨I, hI, hKI⟩ := hKj.subset_isBasis_of_subset hKjE sdiff_subset
  have hIbase : M.IsBase I := by
    apply isBase_of_indep_ncard hI.indep
    rw [← hv, ← rk_indep hI.indep]
    exact le_of_eq (by
      have h1 := rk_isBasis' hI.isBasis'
      rw [h1, rk_indep hI.indep])
  have hiI : i ∈ I := hKI ⟨hiK, fun h => hij (by rwa [mem_singleton_iff] at h)⟩
  have hjI : j ∉ I := by
    intro hjI
    apply hK.dep.not_indep (hI.indep.subset _)
    intro x hx
    by_cases hxj : x = j
    · exact hxj ▸ hjI
    · exact hKI ⟨hx, hxj⟩
  have hvI : v ∉ I := fun h => (hI.subset h).2 rfl
  have hind : M.Indep (insert j (I \ {i})) := by
    by_contra hdep
    have hsub : insert j (I \ {i}) ⊆ M.E :=
      insert_subset (hK.subset_ground hjK) (sdiff_subset.trans hI.indep.subset_ground)
    obtain ⟨K', hK's, hK'⟩ := (show M.Dep (insert j (I \ {i})) from ⟨hdep, hsub⟩).exists_isCircuit_subset
    have hjK' : j ∈ K' := by
      by_contra h
      apply hK'.dep.not_indep (hI.indep.subset _)
      intro x hx
      rcases hK's hx with rfl | hx'
      · exact absurd hx h
      · exact hx'.1
    have hne : K ≠ K' := by
      intro h
      rw [← h] at hK's
      rcases hK's hiK with h' | h'
      · exact hij h'
      · exact h'.2 rfl
    obtain ⟨K'', hK''s, hK''⟩ := hK.elimination hK' hne j
    apply hK''.dep.not_indep (hI.indep.subset _)
    intro x hx
    obtain ⟨hx1, hx2⟩ := hK''s hx
    rw [mem_singleton_iff] at hx2
    rcases hx1 with hx1 | hx1
    · by_cases hxj : x = j
      · exact absurd hxj hx2
      · exact hKI ⟨hx1, hxj⟩
    · rcases hK's hx1 with h | h
      · exact absurd h hx2
      · exact h.1
  refine ⟨I \ {i}, fun h => hvI h.1, fun h => h.2 rfl, fun h => hjI h.1, ?_, ?_⟩
  · rwa [insert_sdiff_singleton, insert_eq_of_mem hiI]
  · exact insert_isBase_of_insert_indep (e := i) (fun h => h.2 rfl) (fun h => hjI h.1)
      (by rwa [insert_sdiff_singleton, insert_eq_of_mem hiI]) hind

/-- If `v` is a loop, `StarD M v` holds vacuously. -/
theorem starD_of_rk_zero {v : α} (hv : rk M {v} = 0) : StarD M v := by
  intro D i j _ hvD _ _ hi _
  exfalso
  have hind : M.Indep {v} := hi.indep.subset (singleton_subset_iff.2 (mem_insert_of_mem _ hvD))
  have := rk_indep hind
  rw [hv] at this
  simp at this

/-- **The exchange condition from connectivity.** Let `C` be a separator of `M` with `v ∈ C`
such that `C \ {v}` is connected, and let `v` be a non-coloop. Then `StarD M v` holds. -/
theorem starD_of_connIn {C : Set α} {v : α} (hC : Sep M C) (hvC : v ∈ C)
    (hconn : ConnIn M (C \ {v})) (hv : rk M (M.E \ {v}) = rk M M.E) : StarD M v := by
  intro D i j hij hvD hiD hjD hi hj
  have hjE : j ∈ M.E := hj.subset_ground (mem_insert _ _)
  have hjnot : j ∉ insert i D := by
    rintro (h | h)
    · exact hij h.symm
    · exact hjD h
  obtain ⟨K, hKs, hK⟩ := (hi.insert_dep ⟨hjE, hjnot⟩).exists_isCircuit_subset
  have hjK : j ∈ K := by
    by_contra h
    apply hK.dep.not_indep (hi.indep.subset _)
    intro x hx
    rcases hKs hx with rfl | hx'
    · exact absurd hx h
    · exact hx'
  have hiK : i ∈ K := by
    by_contra h
    apply hK.dep.not_indep (hj.indep.subset _)
    intro x hx
    rcases hKs hx with rfl | rfl | hx'
    · exact mem_insert _ _
    · exact absurd hx h
    · exact mem_insert_of_mem _ hx'
  by_cases hvK : v ∈ K
  · rcases subset_or_subset_of_sep hC hK with hKC | hKC
    · have hiv : i ≠ v := fun h => hiD (h ▸ hvD)
      have hjv : j ≠ v := fun h => hjD (h ▸ hvD)
      obtain ⟨K', hK', hK's, hiK', hjK'⟩ := exists_isCircuit_of_connIn hconn
        ⟨hKC hiK, hiv⟩ ⟨hKC hjK, hjv⟩ hij
      exact exists_pair_of_isCircuit hK' hiK' hjK' hij (fun h => (hK's h).2 rfl) hv
    · exact absurd hvC (hKC hvK).2
  · exact exists_pair_of_isCircuit hK hiK hjK hij hvK hv

end SquareBasis
