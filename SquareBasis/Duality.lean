module

public import SquareBasis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Abel

/-!
# Basic facts: coordinate sums, transfer along linear equivalences, duality

* `incidence_apply` : `(A_M f)_a = ∑_{B ∋ a} f(B)`.
* `total_eq_zero_of_mem_ker` : for rank at least one, every `f ∈ ker_ℤ A_M` has
  coordinate sum `0` (Section 2 of the paper).
* `IsSquare.neg` : the negative of a square is a square (swap `B` and `B'`).
* `HasSquareBasis.of_linearEquiv` : a square basis is transported along a linear
  equivalence that matches the kernels and maps squares to squares.
* `hasSquareBasis_dual_iff` : Lemma 2.4 (duality).
-/

@[expose] public section

namespace SquareBasis

open Matroid

variable {α : Type*}

open scoped Classical in
theorem incidence_apply (M : Matroid α) (f : Bases M →₀ ℤ) (a : α) :
    incidence M f a = f.sum (fun B c => if a ∈ B.1 then c else 0) := by
  simp only [incidence, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, Set.indicator_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- The coordinate sum of `f`. -/
def total {ι : Type*} (f : ι →₀ ℤ) : ℤ := f.sum (fun _ c => c)

open scoped Classical in
/-- Every element of `ker_ℤ A_M` has coordinate sum zero when `rank M ≥ 1`. -/
theorem total_eq_zero_of_mem_ker (M : Matroid α) [M.Finite] [M.RankPos]
    {f : Bases M →₀ ℤ} (hf : f ∈ LinearMap.ker (incidence M)) : total f = 0 := by
  obtain ⟨B₀, hB₀⟩ := M.exists_isBase
  set E := M.ground_finite.toFinset with hE
  have hcard : ∀ B : Bases M, ((E.filter (· ∈ B.1)).card : ℤ) = B₀.ncard := by
    intro B
    have h1 : ((E.filter (· ∈ B.1) : Finset α) : Set α) = B.1 := by
      ext x
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hE]
      exact ⟨fun h => h.2, fun h => ⟨B.2.subset_ground h, h⟩⟩
    have h2 := Set.ncard_coe_finset (E.filter (· ∈ B.1))
    rw [h1] at h2
    rw [← h2, B.2.ncard_eq_ncard_of_isBase hB₀]
  have key : ∑ a ∈ E, incidence M f a = (B₀.ncard : ℤ) * total f := by
    simp_rw [total, incidence_apply, Finsupp.sum]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      hcard B, mul_comm]
  have hzero : ∑ a ∈ E, incidence M f a = 0 := by
    rw [LinearMap.mem_ker] at hf
    simp [hf]
  have hpos : (B₀.ncard : ℤ) ≠ 0 := by
    have := (Set.ncard_pos (M.ground_finite.subset hB₀.subset_ground)).2 hB₀.nonempty
    omega
  rw [key] at hzero
  exact (mul_eq_zero.1 hzero).resolve_left hpos

/-- The negative of a square is a square: `-z_{i,j;B,B'} = z_{i,j;B',B}`. -/
theorem IsSquare.neg {M : Matroid α} {z : Bases M →₀ ℤ} (hz : IsSquare M z) :
    IsSquare M (-z) := by
  obtain ⟨i, j, B, B', h₁, h₂, h₃, h₄, hij, hBB', hiB, hjB, hiB', hjB', rfl⟩ := hz
  exact ⟨i, j, B', B, h₃, h₄, h₁, h₂, hij, hBB'.symm, hiB', hjB', hiB, hjB, by abel⟩

/-- Transport of a square basis along a linear equivalence that matches the integer
kernels and maps squares to squares. -/
theorem HasSquareBasis.of_linearEquiv {β : Type*} {M : Matroid α} {M' : Matroid β}
    (φ : (Bases M →₀ ℤ) ≃ₗ[ℤ] (Bases M' →₀ ℤ))
    (hker : ∀ f, f ∈ LinearMap.ker (incidence M) ↔ φ f ∈ LinearMap.ker (incidence M'))
    (hsq : ∀ z, IsSquare M z → IsSquare M' (φ z)) (h : HasSquareBasis M) :
    HasSquareBasis M' := by
  obtain ⟨S, hS, hli, hspan⟩ := h
  refine ⟨(φ : (Bases M →₀ ℤ) →ₗ[ℤ] (Bases M' →₀ ℤ)) '' S, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hsq z (hS z hz)
  · have : LinearIndepOn ℤ id S := hli
    exact this.image (by simp [LinearEquiv.ker])
  · rw [Submodule.span_image, hspan]
    ext g
    simp only [Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (hker f).1 hf
    · intro hg
      refine ⟨φ.symm g, (hker _).2 (by simpa using hg), by simp⟩

/-! ### Duality (Lemma 2.4) -/

/-- Complementation `B ↦ E \ B` from the bases of `M` to the bases of `M✶`. -/
def complEquiv (M : Matroid α) : Bases M ≃ Bases M✶ where
  toFun B := ⟨M.E \ B.1, B.2.compl_isBase_dual⟩
  invFun C := ⟨M.E \ C.1, C.2.compl_isBase_of_dual⟩
  left_inv B := Subtype.ext (Set.sdiff_sdiff_cancel_left B.2.subset_ground)
  right_inv C := Subtype.ext (Set.sdiff_sdiff_cancel_left (by simpa using C.2.subset_ground))

/-- The isomorphism `e_I ↦ e_{E \ I}`. -/
noncomputable def dualMap (M : Matroid α) : (Bases M →₀ ℤ) ≃ₗ[ℤ] (Bases M✶ →₀ ℤ) :=
  Finsupp.domLCongr (complEquiv M)

theorem total_dualMap (M : Matroid α) (f : Bases M →₀ ℤ) : total (dualMap M f) = total f := by
  simp only [total, dualMap, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain]
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

open scoped Classical in
theorem incidence_dualMap (M : Matroid α) (f : Bases M →₀ ℤ) {a : α} (ha : a ∈ M.E) :
    incidence M✶ (dualMap M f) a + incidence M f a = total f := by
  rw [incidence_apply, incidence_apply]
  simp only [dualMap, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain]
  rw [Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => by split_ifs <;> simp), total,
    ← Finsupp.sum_add]
  refine Finsupp.sum_congr fun B _ => ?_
  simp only [complEquiv, Equiv.coe_fn_mk, Set.mem_sdiff]
  by_cases h : a ∈ B.1 <;> simp [h, ha]

theorem incidence_eq_zero_of_notMem (M : Matroid α) (f : Bases M →₀ ℤ) {a : α}
    (ha : a ∉ M.E) : incidence M f a = 0 := by
  classical
  rw [incidence_apply]
  refine Finset.sum_eq_zero fun B _ => ?_
  have : a ∉ B.1 := fun h => ha (B.2.subset_ground h)
  simp [this]

theorem mem_ker_iff_dualMap (M : Matroid α) [M.Finite] [M.RankPos] [M✶.RankPos]
    (f : Bases M →₀ ℤ) :
    f ∈ LinearMap.ker (incidence M) ↔ dualMap M f ∈ LinearMap.ker (incidence M✶) := by
  have : M✶.Finite := ⟨by simpa using M.ground_finite⟩
  simp only [LinearMap.mem_ker]
  constructor
  · intro hf
    have ht := total_eq_zero_of_mem_ker M (LinearMap.mem_ker.2 hf)
    funext a
    by_cases ha : a ∈ M.E
    · have := incidence_dualMap M f ha
      rw [hf, ht] at this
      simpa using this
    · exact incidence_eq_zero_of_notMem M✶ _ (by simpa using ha)
  · intro hf
    have ht := total_eq_zero_of_mem_ker M✶ (LinearMap.mem_ker.2 hf)
    rw [total_dualMap] at ht
    funext a
    by_cases ha : a ∈ M.E
    · have := incidence_dualMap M f ha
      rw [hf, ht] at this
      simpa using this
    · exact incidence_eq_zero_of_notMem M _ ha

/-- `E \ (B + i) = C + j` where `C = E \ (B + i + j)`. -/
theorem diff_insert_eq {E B : Set α} {i j : α} (hj : j ∈ E) (hij : i ≠ j) (hjB : j ∉ B) :
    E \ insert i B = insert j (E \ insert i (insert j B)) := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_insert_iff]
  by_cases hx : x = j
  · subst hx; simp [hj, hij.symm, hjB]
  · simp [hx]

theorem diff_diff_insert_insert {E B : Set α} {i j : α} (hB : B ⊆ E) (hi : i ∈ E) (hj : j ∈ E)
    (hiB : i ∉ B) (hjB : j ∉ B) :
    E \ insert i (insert j (E \ insert i (insert j B))) = B := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_insert_iff]
  by_cases hxi : x = i
  · subst hxi; simp [hiB]
  by_cases hxj : x = j
  · subst hxj; simp [hjB]
  by_cases hxB : x ∈ B
  · simp [hxi, hxj, hxB, hB hxB]
  · simp [hxi, hxj, hxB]

/-- Squares of `M` are mapped to squares of `M✶` (Lemma 2.4). -/
theorem IsSquare.dualMap {M : Matroid α} {z : Bases M →₀ ℤ} (hz : IsSquare M z) :
    IsSquare M✶ (dualMap M z) := by
  obtain ⟨i, j, B, B', h₁, h₂, h₃, h₄, hij, hBB', hiB, hjB, hiB', hjB', rfl⟩ := hz
  have hi : i ∈ M.E := h₁.subset_ground (Set.mem_insert _ _)
  have hj : j ∈ M.E := h₂.subset_ground (Set.mem_insert _ _)
  have hB : B ⊆ M.E := (Set.subset_insert _ _).trans h₁.subset_ground
  have hB' : B' ⊆ M.E := (Set.subset_insert _ _).trans h₃.subset_ground
  set C := M.E \ insert i (insert j B) with hC
  set C' := M.E \ insert i (insert j B') with hC'
  have e₁ : M.E \ insert i B = insert j C := diff_insert_eq hj hij hjB
  have e₂ : M.E \ insert j B = insert i C := by
    rw [diff_insert_eq hi hij.symm hiB, Set.insert_comm]
  have e₃ : M.E \ insert i B' = insert j C' := diff_insert_eq hj hij hjB'
  have e₄ : M.E \ insert j B' = insert i C' := by
    rw [diff_insert_eq hi hij.symm hiB', Set.insert_comm]
  have b₁ : M✶.IsBase (insert j C) := e₁ ▸ h₁.compl_isBase_dual
  have b₂ : M✶.IsBase (insert i C) := e₂ ▸ h₂.compl_isBase_dual
  have b₃ : M✶.IsBase (insert j C') := e₃ ▸ h₃.compl_isBase_dual
  have b₄ : M✶.IsBase (insert i C') := e₄ ▸ h₄.compl_isBase_dual
  have hCC' : C' ≠ C := by
    intro h
    apply hBB'
    rw [← diff_diff_insert_insert hB hi hj hiB hjB,
      ← diff_diff_insert_insert hB' hi hj hiB' hjB', ← hC, ← hC', h]
  refine ⟨i, j, C', C, b₄, b₃, b₂, b₁, hij, hCC', ?_, ?_, ?_, ?_, ?_⟩
  · simp [hC']
  · simp [hC']
  · simp [hC]
  · simp [hC]
  · have c₁ : complEquiv M ⟨insert i B, h₁⟩ = ⟨insert j C, b₁⟩ := Subtype.ext e₁
    have c₂ : complEquiv M ⟨insert j B, h₂⟩ = ⟨insert i C, b₂⟩ := Subtype.ext e₂
    have c₃ : complEquiv M ⟨insert i B', h₃⟩ = ⟨insert j C', b₃⟩ := Subtype.ext e₃
    have c₄ : complEquiv M ⟨insert j B', h₄⟩ = ⟨insert i C', b₄⟩ := Subtype.ext e₄
    simp only [SquareBasis.dualMap, map_add, map_sub, Finsupp.domLCongr_single, c₁, c₂, c₃, c₄]
    abel

/-- **Lemma 2.4 (duality).** If `1 ≤ rank M ≤ |E| - 1`, then `M` has a square basis if and
only if `M✶` does. -/
theorem hasSquareBasis_dual_iff (M : Matroid α) [M.Finite] [M.RankPos] [M✶.RankPos] :
    HasSquareBasis M✶ ↔ HasSquareBasis M := by
  constructor
  · intro h
    have : M✶.Finite := ⟨by simpa using M.ground_finite⟩
    have : M✶✶.RankPos := by rw [dual_dual]; infer_instance
    have h' := h.of_linearEquiv (dualMap M✶) (mem_ker_iff_dualMap M✶)
      (fun z hz => hz.dualMap)
    rwa [dual_dual] at h'
  · exact HasSquareBasis.of_linearEquiv (dualMap M) (mem_ker_iff_dualMap M)
      (fun z hz => hz.dualMap)

end SquareBasis
