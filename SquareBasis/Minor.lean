module

public import SquareBasis.Connectivity

/-!
# Ranks and connectivity of single-element minors

* `rk_delete`, `rk_contract_elem` : the rank functions of `M ＼ D` and `M ／ {e}`.
* `Conn M` : `M` is connected (no nontrivial separator); `conn_dual` : `M` is connected
  if and only if `M✶` is.
* `tutte_minor` : Tutte's theorem, `M ＼ e` or `M ／ e` is connected.
* `conn_of_forall_isCircuit` : if every element shares a circuit with `v`, `M` is connected.
* `contract_isCircuit_of_not_mem_closure` : a circuit `C` with `e ∉ cl(C)` is a circuit of
  `M ／ e`.
-/

@[expose] public section

namespace SquareBasis

open Matroid Set

variable {α : Type*}

theorem rk_delete (M : Matroid α) [M.Finite] (D : Set α) {Y : Set α} (hY : Y ⊆ M.E \ D) :
    rk (M ＼ D) Y = rk M Y := by
  unfold rk; rw [delete_eq_restrict, restrict_eRk_eq _ hY]

theorem rk_contract_elem (M : Matroid α) [M.Finite] {e : α} (he : e ∈ M.E) {Y : Set α}
    (hY : Y ⊆ M.E \ {e}) : rk (M ／ {e}) Y = rk M (insert e Y) - rk M {e} := by
  have h1 : M ／ {e} = (M✶ ＼ {e})✶ := (dual_delete_dual M {e}).symm
  have hground : (M✶ ＼ {e}).E = M.E \ {e} := by simp
  rw [h1, rk_dual (M✶ ＼ {e}) (by rw [hground]; exact hY), hground,
    rk_delete M✶ {e} (by simp only [dual_ground]; exact sdiff_subset),
    rk_delete M✶ {e} (by simp only [dual_ground]; exact subset_rfl)]
  rw [rk_dual M (sdiff_subset.trans sdiff_subset), rk_dual M sdiff_subset]
  have e1 : M.E \ ((M.E \ {e}) \ Y) = insert e Y := by
    ext x
    have := @hY x
    simp only [mem_sdiff, mem_singleton_iff, mem_insert_iff] at this ⊢
    by_cases hxe : x = e
    · subst hxe; tauto
    · tauto
  have e2 : M.E \ (M.E \ {e}) = {e} := sdiff_sdiff_cancel_left (singleton_subset_iff.2 he)
  rw [e1, e2]
  have hfin := M.ground_finite
  have c1 := Set.ncard_sdiff_add_ncard_of_subset hY (hfin.subset sdiff_subset)
  have c2 := Set.ncard_sdiff_singleton_add_one he hfin
  have c1' : (((M.E \ {e}) \ Y).ncard : ℤ) + Y.ncard = (M.E \ {e}).ncard := by exact_mod_cast c1
  have c2' : ((M.E \ {e}).ncard : ℤ) + 1 = M.E.ncard := by exact_mod_cast c2
  linarith

/-- `M` is connected. -/
def Conn (M : Matroid α) : Prop := ConnIn M M.E

theorem conn_iff (M : Matroid α) : Conn M ↔ ∀ Z, Sep M Z → Z = ∅ ∨ Z = M.E := by
  constructor
  · intro h Z hZ; exact h Z hZ.1 hZ.2
  · intro h Z hZ hsplit; exact h Z ⟨hZ, hsplit⟩

theorem conn_dual (M : Matroid α) [M.Finite] : Conn M✶ ↔ Conn M := by
  rw [conn_iff, conn_iff]
  constructor
  · intro h Z hZ
    simpa using h Z (sep_dual hZ)
  · intro h Z hZ
    have := sep_dual hZ
    rw [dual_dual] at this
    simpa using h Z this

theorem conn_delete_iff (M : Matroid α) [M.Finite] (e : α) :
    Conn (M ＼ {e}) ↔ ConnIn M (M.E \ {e}) := by
  unfold Conn ConnIn
  rw [delete_ground]
  have hr : ∀ Z ⊆ M.E \ {e}, rk (M ＼ {e}) Z = rk M Z := fun Z hZ => rk_delete M {e} hZ
  constructor
  · intro h Z hZ hs
    apply h Z hZ
    rw [hr Z hZ, hr _ sdiff_subset, hr _ subset_rfl]; exact hs
  · intro h Z hZ hs
    apply h Z hZ
    rw [← hr Z hZ, ← hr _ sdiff_subset, ← hr _ subset_rfl]; exact hs

theorem conn_contract_iff (M : Matroid α) [M.Finite] (e : α) :
    Conn (M ／ {e}) ↔ ConnIn M✶ (M.E \ {e}) := by
  have h1 : M ／ {e} = (M✶ ＼ {e})✶ := (dual_delete_dual M {e}).symm
  rw [h1, conn_dual, conn_delete_iff, dual_ground]

/-- **Tutte's theorem.** If `M` is connected and `e ∈ E` with `|E| ≥ 2`, then `M ＼ e` or
`M ／ e` is connected. -/
theorem tutte_minor {M : Matroid α} [M.Finite] (hM : Conn M) {e : α} (he : e ∈ M.E)
    (hne : (M.E \ {e}).Nonempty) : Conn (M ＼ {e}) ∨ Conn (M ／ {e}) := by
  rw [conn_delete_iff, conn_contract_iff]
  exact tutte ⟨subset_rfl, by rw [sdiff_self, rk_empty, add_zero]⟩ hM he hne

/-- In a connected matroid with at least two elements, no element is a loop or a coloop. -/
theorem conn_rk_facts {M : Matroid α} [M.Finite] (hM : Conn M) {v : α} (hv : v ∈ M.E)
    (hne : (M.E \ {v}).Nonempty) : rk M {v} = 1 ∧ rk M (M.E \ {v}) = rk M M.E :=
  rk_facts_of_connIn hM hv hne

/-- Two distinct elements of a connected matroid lie in a common circuit. -/
theorem conn_exists_isCircuit {M : Matroid α} [M.Finite] (hM : Conn M) {x y : α}
    (hx : x ∈ M.E) (hy : y ∈ M.E) (hxy : x ≠ y) : ∃ K, M.IsCircuit K ∧ x ∈ K ∧ y ∈ K := by
  obtain ⟨K, hK, -, hxK, hyK⟩ := exists_isCircuit_of_connIn hM hx hy hxy
  exact ⟨K, hK, hxK, hyK⟩

/-- If every element lies in a common circuit with `v`, then `M` is connected. -/
theorem conn_of_forall_isCircuit {M : Matroid α} [M.Finite] {v : α} (hv : v ∈ M.E)
    (h : ∀ y ∈ M.E, y = v ∨ ∃ K, M.IsCircuit K ∧ v ∈ K ∧ y ∈ K) : Conn M := by
  rw [conn_iff]
  intro Z hZ
  by_cases hvZ : v ∈ Z
  · right
    refine subset_antisymm hZ.1 (fun y hy => ?_)
    rcases h y hy with rfl | ⟨K, hK, hvK, hyK⟩
    · exact hvZ
    · rcases subset_or_subset_of_sep hZ hK with hKZ | hKZ
      · exact hKZ hyK
      · exact absurd hvZ (hKZ hvK).2
  · left
    ext y
    simp only [mem_empty_iff_false, iff_false]
    intro hyZ
    rcases h y (hZ.1 hyZ) with rfl | ⟨K, hK, hvK, hyK⟩
    · exact hvZ hyZ
    · rcases subset_or_subset_of_sep hZ hK with hKZ | hKZ
      · exact hvZ (hKZ hvK)
      · exact (hKZ hyK).2 hyZ

theorem indep_iff_rk {M : Matroid α} [M.Finite] {I : Set α} (hI : I ⊆ M.E) :
    M.Indep I ↔ rk M I = I.ncard := by
  rw [indep_iff_eRk_eq_encard]
  have hfin : I.Finite := M.ground_finite.subset hI
  rw [eRk_eq_rk M I, ← hfin.cast_ncard_eq]
  unfold rk
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- A circuit `C` of `M` with `e ∉ C` and `e ∉ cl(C)` is a circuit of `M ／ {e}`. -/
theorem contract_isCircuit_of_rk {M : Matroid α} [M.Finite] {C : Set α} {e : α}
    (hC : M.IsCircuit C) (he : e ∈ M.E) (heC : e ∉ C) (hr : rk M (insert e C) = rk M C + 1)
    (hre : rk M {e} = 1) : (M ／ {e}).IsCircuit C := by
  have hCE : C ⊆ M.E \ {e} := fun x hx =>
    ⟨hC.subset_ground hx, fun h => heC (by rw [mem_singleton_iff] at h; exact h ▸ hx)⟩
  have hfin : C.Finite := M.ground_finite.subset hC.subset_ground
  have hCr := rk_circuit_add_one hC
  rw [isCircuit_iff_dep_forall_sdiff_singleton_indep]
  constructor
  · refine ⟨fun hind => ?_, by simpa using hCE⟩
    rw [indep_iff_rk (by simpa using hCE), rk_contract_elem M he hCE, hr, hre] at hind
    omega
  · intro x hx
    have hsub : C \ {x} ⊆ M.E \ {e} := sdiff_subset.trans hCE
    rw [indep_iff_rk (by simpa using hsub), rk_contract_elem M he hsub, hre]
    have hind : M.Indep (C \ {x}) := hC.ssubset_indep
      (ssubset_of_subset_of_ne sdiff_subset (fun h => by
        have : x ∈ C \ {x} := by rw [h]; exact hx
        exact this.2 rfl))
    have h1 := rk_indep hind
    have hcard := Set.ncard_sdiff_singleton_add_one hx hfin
    -- submodularity: `r(C + e) ≤ r(C - x + e) + r(C) - r(C - x)`
    have h2 := rk_submod M (insert e (C \ {x})) C
    have e1 : insert e (C \ {x}) ∩ C = C \ {x} := by
      ext y; simp only [mem_inter_iff, mem_insert_iff, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨rfl | h, hy⟩
        · exact absurd hy heC
        · exact h
      · intro h; exact ⟨Or.inr h, h.1⟩
    have e2 : insert e (C \ {x}) ∪ C = insert e C := by
      ext y; simp only [mem_union, mem_insert_iff, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ((rfl | ⟨h, -⟩) | h)
        · exact Or.inl rfl
        · exact Or.inr h
        · exact Or.inr h
      · rintro (rfl | h)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr h
    rw [e1, e2] at h2
    have hfin' : (C \ {x}).Finite := hfin.subset sdiff_subset
    have h3 := rk_le_ncard M (hfin'.insert e)
    have h4 : (insert e (C \ {x})).ncard = (C \ {x}).ncard + 1 :=
      Set.ncard_insert_of_notMem (fun h => heC h.1) hfin'
    have hcard' : ((C \ {x}).ncard : ℤ) + 1 = C.ncard := by exact_mod_cast hcard
    rw [h4] at h3
    push_cast at h3
    linarith

end SquareBasis
