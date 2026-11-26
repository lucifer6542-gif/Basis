module

public import SquareBasis.Section6
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Remark 7.5 of the paper

For `U_{2,5}` the five squares
`z_{1,2;{3},{4}}, z_{1,3;{2},{5}}, z_{1,4;{3},{5}}, z_{1,5;{2},{4}}, z_{2,3;{4},{5}}`
(paper indices; here every element is shifted down by one) are linearly independent,
`rank ker_ℤ A_{U_{2,5}} = 10 - 5 = 5`, and they generate a sublattice of index `2`
(`remark75`).

The index is computed from the `ℤ`-basis `r_s` (`s ∈ S`) of Proposition 6.2: the five squares
are `C r` for an explicit integer matrix `C` with `det C = 2`.
-/

@[expose] public section

namespace SquareBasis

open Finset Module Matrix

/-- `e_X` in `ℤ^{𝓑(U_{2,5})}`. -/
noncomputable abbrev e5 (X : Finset (Fin 5)) : Bases (unif 2 5) →₀ ℤ := eF 2 X

/-- The square `z_{i,j;{b},{b'}} = e_{b+i} - e_{b+j} - e_{b'+i} + e_{b'+j}` of `U_{2,5}`. -/
noncomputable def z5 (i j b b' : Fin 5) : Bases (unif 2 5) →₀ ℤ :=
  e5 {i, b} - e5 {j, b} - e5 {i, b'} + e5 {j, b'}

theorem base_pair {x y : Fin 5} (h : x ≠ y) : (unif 2 5).IsBase (insert x {y} : Set (Fin 5)) := by
  have := (unif_isBase_coe_iff (by norm_num : 2 ≤ 5)).2 (card_pair h)
  simpa using this

theorem e5_pair {x y : Fin 5} (h : x ≠ y) :
    e5 {x, y} = Finsupp.single ⟨insert x {y}, base_pair h⟩ 1 := by
  rw [e5, eF_of_card 2 (by norm_num) (card_pair h)]
  exact congrArg (fun t => Finsupp.single t (1 : ℤ)) (Subtype.ext (by simp))

theorem z5_isSquare {i j b b' : Fin 5} (hij : i ≠ j) (hbb : b ≠ b') (h1 : i ≠ b) (h2 : j ≠ b)
    (h3 : i ≠ b') (h4 : j ≠ b') : IsSquare (unif 2 5) (z5 i j b b') := by
  refine ⟨i, j, {b}, {b'}, base_pair h1, base_pair h2, base_pair h3, base_pair h4, hij,
    by simpa using hbb, by simpa using h1, by simpa using h2, by simpa using h3,
    by simpa using h4, ?_⟩
  rw [z5, e5_pair h1, e5_pair h2, e5_pair h3, e5_pair h4]

/-- The five squares of Remark 7.5. -/
noncomputable def zsq : Fin 5 → Bases (unif 2 5) →₀ ℤ :=
  ![z5 0 1 2 3, z5 0 2 1 4, z5 0 3 2 4, z5 0 4 1 3, z5 1 2 3 4]

/-- The basis `r_s` of Proposition 6.2 for `U_{2,5}`, for `s = 45, 35, 34, 25, 24` (paper
indices). -/
noncomputable def rv : Fin 5 → Bases (unif 2 5) →₀ ℤ :=
  ![z5 4 1 3 0, z5 4 1 2 0, z5 3 1 2 0, z5 4 2 1 0, z5 3 2 1 0]

/-- The sets `s ∈ S`. -/
def sv : Fin 5 → Finset (Fin 5) := ![{3, 4}, {2, 4}, {2, 3}, {1, 4}, {1, 3}]

theorem hk25 : 2 < 5 := by norm_num

theorem rv0 : rv 0 = rS 2 hk25 {3, 4} := by
  rw [rS, show iOf 2 hk25 {3, 4} = 4 by decide, show BOf 2 hk25 {3, 4} = {3} by decide,
    show jOf 2 hk25 {3, 4} = 1 by decide, show BpOf 2 hk25 {3, 4} = {0} by decide]
  rfl

theorem rv1 : rv 1 = rS 2 hk25 {2, 4} := by
  rw [rS, show iOf 2 hk25 {2, 4} = 4 by decide, show BOf 2 hk25 {2, 4} = {2} by decide,
    show jOf 2 hk25 {2, 4} = 1 by decide, show BpOf 2 hk25 {2, 4} = {0} by decide]
  rfl

theorem rv2 : rv 2 = rS 2 hk25 {2, 3} := by
  rw [rS, show iOf 2 hk25 {2, 3} = 3 by decide, show BOf 2 hk25 {2, 3} = {2} by decide,
    show jOf 2 hk25 {2, 3} = 1 by decide, show BpOf 2 hk25 {2, 3} = {0} by decide]
  rfl

theorem rv3 : rv 3 = rS 2 hk25 {1, 4} := by
  rw [rS, show iOf 2 hk25 {1, 4} = 4 by decide, show BOf 2 hk25 {1, 4} = {1} by decide,
    show jOf 2 hk25 {1, 4} = 2 by decide, show BpOf 2 hk25 {1, 4} = {0} by decide]
  rfl

theorem rv4 : rv 4 = rS 2 hk25 {1, 3} := by
  rw [rS, show iOf 2 hk25 {1, 3} = 3 by decide, show BOf 2 hk25 {1, 3} = {1} by decide,
    show jOf 2 hk25 {1, 3} = 2 by decide, show BpOf 2 hk25 {1, 3} = {0} by decide]
  rfl

theorem rv_eq (i : Fin 5) : rv i = rS 2 hk25 (sv i) := by
  fin_cases i
  exacts [rv0, rv1, rv2, rv3, rv4]

theorem Sset25 : Sset 2 hk25 = univ.image sv := by decide

theorem rv_li : LinearIndependent ℤ rv := by
  have hli := (prop62 2 (by norm_num) hk25).2.2.2.1
  let f : Fin 5 → (Sset 2 hk25) := fun i => ⟨sv i, by rw [Sset25]; exact mem_image_of_mem _ (mem_univ _)⟩
  have hf : Function.Injective f := by
    intro a b h
    have : sv a = sv b := congrArg Subtype.val h
    revert a b; decide
  have := hli.comp f hf
  convert this using 1
  funext i
  exact rv_eq i

theorem rv_span : Submodule.span ℤ (Set.range rv) = LinearMap.ker (incidence (unif 2 5)) := by
  rw [← (prop62 2 (by norm_num) hk25).2.2.2.2, Sset25, coe_image, coe_univ, Set.image_univ,
    ← Set.range_comp, show rS 2 hk25 ∘ sv = rv from funext fun i => (rv_eq i).symm]

/-- The transition matrix: `zsq i = ∑_j C i j • rv j`. -/
def Cmat : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 0, 0, 0, 1;
     0, 1, 0, 0, 0;
     1, 0, -1, 0, 1;
     1, 0, 0, -1, 1;
     0, 1, -1, -1, 1]

theorem zsq_eq (i : Fin 5) : zsq i = ∑ j, Cmat i j • rv j := by
  have e10 : ({1, 0} : Finset (Fin 5)) = {0, 1} := by decide
  have e20 : ({2, 0} : Finset (Fin 5)) = {0, 2} := by decide
  have e30 : ({3, 0} : Finset (Fin 5)) = {0, 3} := by decide
  have e40 : ({4, 0} : Finset (Fin 5)) = {0, 4} := by decide
  have e21 : ({2, 1} : Finset (Fin 5)) = {1, 2} := by decide
  have e31 : ({3, 1} : Finset (Fin 5)) = {1, 3} := by decide
  have e41 : ({4, 1} : Finset (Fin 5)) = {1, 4} := by decide
  have e32 : ({3, 2} : Finset (Fin 5)) = {2, 3} := by decide
  have e42 : ({4, 2} : Finset (Fin 5)) = {2, 4} := by decide
  have e43 : ({4, 3} : Finset (Fin 5)) = {3, 4} := by decide
  fin_cases i <;>
    simp [zsq, rv, Cmat, z5, Fin.sum_univ_five, e10, e20, e30, e40, e21, e31, e41, e32, e42,
      e43] <;>
    abel

theorem det_Cmat : Cmat.det = 2 := by
  simp [Cmat, det_succ_row_zero, Fin.sum_univ_succ]
  decide

theorem zsq_li : LinearIndependent ℤ zsq := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h : ∑ j, (∑ i, g i * Cmat i j) • rv j = 0 := by
    rw [← hg]
    simp only [zsq_eq, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  have h2 := (Fintype.linearIndependent_iff.1 rv_li) _ h
  have q0 := h2 0
  have q1 := h2 1
  have q2 := h2 2
  have q3 := h2 3
  have q4 := h2 4
  simp [Fin.sum_univ_five, Cmat] at q0 q1 q2 q3 q4
  intro i
  fin_cases i <;> simp <;> omega

theorem zsq_isSquare (i : Fin 5) : IsSquare (unif 2 5) (zsq i) := by
  fin_cases i
  · exact z5_isSquare (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact z5_isSquare (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact z5_isSquare (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact z5_isSquare (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact z5_isSquare (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem finrank_ker_unif25 : finrank ℤ (LinearMap.ker (incidence (unif 2 5))) = 5 := by
  have h := rank_nullity (unif 2 5)
  rw [(prop62 2 (by norm_num) hk25).1, card_bases_unif 2 (by norm_num)] at h
  have : (univ.powersetCard 2 : Finset (Finset (Fin 5))).card = 10 := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]; rfl
  omega

/-- **Remark 7.5.** The five squares of `U_{2,5}` are linearly independent,
`rank ker_ℤ A_{U_{2,5}} = 5`, and they generate a sublattice of index `2`. -/
theorem remark75 :
    (∀ i, IsSquare (unif 2 5) (zsq i)) ∧ LinearIndependent ℤ zsq ∧
      finrank ℤ (LinearMap.ker (incidence (unif 2 5))) = 5 ∧
      (Submodule.span ℤ (Set.range zsq)).toAddSubgroup.relIndex
        (LinearMap.ker (incidence (unif 2 5))).toAddSubgroup = 2 := by
  refine ⟨zsq_isSquare, zsq_li, finrank_ker_unif25, ?_⟩
  have H : (Submodule.span ℤ (Set.range zsq)).toAddSubgroup ≤
      (LinearMap.ker (incidence (unif 2 5))).toAddSubgroup := by
    intro x hx
    exact (Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩; exact (zsq_isSquare i).mem_ker)) hx
  let b₂ : Basis (Fin 5) ℤ (LinearMap.ker (incidence (unif 2 5))).toAddSubgroup.toIntSubmodule :=
    (Basis.span rv_li).map (LinearEquiv.ofEq _ _
      (rv_span.trans (Submodule.toAddSubgroup_toIntSubmodule _).symm))
  have hb₂ : ∀ j, (b₂ j : Bases (unif 2 5) →₀ ℤ) = rv j := fun j => by
    rw [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  let b₁ : Basis (Fin 5) ℤ (Submodule.span ℤ (Set.range zsq)).toAddSubgroup.toIntSubmodule :=
    (Basis.span zsq_li).map (LinearEquiv.ofEq _ _
      (Submodule.toAddSubgroup_toIntSubmodule _).symm)
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ H b₁ b₂]
  have hv : (fun i => (⟨b₁ i, H (SetLike.coe_mem _)⟩ :
      (LinearMap.ker (incidence (unif 2 5))).toAddSubgroup.toIntSubmodule)) =
      fun i => ∑ j, Cmat i j • b₂ j := by
    funext i
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, hb₂]
    rw [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
    exact zsq_eq i
  rw [hv, Basis.det_apply]
  have hT : b₂.toMatrix (fun i => ∑ j, Cmat i j • b₂ j) = Cmatᵀ := by
    ext i j
    rw [Basis.toMatrix_apply, b₂.repr_sum_self, transpose_apply]
  rw [hT, det_transpose, det_Cmat]
  rfl

end SquareBasis
