module

public import SquareBasis.Lifting
public import SquareBasis.Minor

/-!
# Section 3 of the paper: direct sums

For a separator `X` of `M`, the bases of `M` are the sets `I₁ ⊔ I₂` with `I₁` a basis of
`M₁ = M | X` and `I₂` a basis of `M₂ = M | (E - X)`, so `ℤ^𝓑 = V₁ ⊗ V₂`.

* `basesEquiv` : `𝓑(M) ≃ 𝓑(M₁) × 𝓑(M₂)`.
* `tensor_basis` : a basis of `K₁` gives the basis `{w ⊗ e_I}` of `K₁ ⊗ V₂`.
* `forest_basis` : a spanning forest of a finite graph gives independent edge vectors that
  span all edge vectors (Step 3).
* `prop31` : Proposition 3.1, the families (1), (2), (3) of the paper form a square basis
  of `ker_ℤ A_M`.
-/

@[expose] public section

namespace SquareBasis

open Matroid Set

universe u

variable {α : Type u}

theorem rk_restrict (M : Matroid α) {R Y : Set α} (hY : Y ⊆ R) :
    rk (M ↾ R) Y = rk M Y := by
  unfold rk; rw [restrict_eRk_eq _ hY]

theorem isBasis'_of_rk {M : Matroid α} [M.Finite] {I X : Set α} (hI : M.Indep I) (hIX : I ⊆ X)
    (h : rk M X ≤ I.ncard) : M.IsBasis' I X := by
  have hfin : I.Finite := M.ground_finite.subset hI.subset_ground
  refine hI.isBasis'_of_eRk_ge hfin hIX ?_
  rw [eRk_eq_rk M X, hI.eRk_eq_encard, ← hfin.cast_ncard_eq]
  unfold rk at h
  exact_mod_cast h

/-- The bases of `M` across a separator `X`. -/
theorem isBase_iff_of_sep {M : Matroid α} [M.Finite] {X : Set α} (hX : Sep M X) {B : Set α} :
    M.IsBase B ↔ B ⊆ M.E ∧ (M ↾ X).IsBase (B ∩ X) ∧ (M ↾ (M.E \ X)).IsBase (B \ X) := by
  simp only [isBase_restrict_iff']
  constructor
  · intro hB
    have hBfin : B.Finite := M.ground_finite.subset hB.subset_ground
    have h1 : M.Indep (B ∩ X) := hB.indep.subset inter_subset_left
    have h2 : M.Indep (B \ X) := hB.indep.subset sdiff_subset
    have c1 := ncard_le_rk_of_indep h1 (inter_subset_right : B ∩ X ⊆ X)
    have hBXsub : B \ X ⊆ M.E \ X := fun x hx => ⟨hB.subset_ground hx.1, hx.2⟩
    have c2 := ncard_le_rk_of_indep h2 hBXsub
    have c3 := rk_ground_eq_of_isBase hB
    have c4 : (B ∩ X).ncard + (B \ X).ncard = B.ncard :=
      Set.ncard_inter_add_ncard_sdiff_eq_ncard B X hBfin
    have c4' : ((B ∩ X).ncard : ℤ) + (B \ X).ncard = B.ncard := by exact_mod_cast c4
    have hs := hX.2
    refine ⟨hB.subset_ground, isBasis'_of_rk h1 inter_subset_right (by linarith),
      isBasis'_of_rk h2 hBXsub (by linarith)⟩
  · rintro ⟨hBE, h1, h2⟩
    have hfin1 : (B ∩ X).Finite := M.ground_finite.subset (inter_subset_left.trans hBE)
    have hfin2 : (B \ X).Finite := M.ground_finite.subset (sdiff_subset.trans hBE)
    have hsplit := sep_split hX (inter_subset_right : B ∩ X ⊆ X)
      (fun x hx => ⟨hBE hx.1, hx.2⟩ : B \ X ⊆ M.E \ X)
    rw [inter_union_sdiff, rk_indep h1.indep, rk_indep h2.indep] at hsplit
    have hcard : (B ∩ X).ncard + (B \ X).ncard = B.ncard :=
      Set.ncard_inter_add_ncard_sdiff_eq_ncard B X (M.ground_finite.subset hBE)
    have hcard' : ((B ∩ X).ncard : ℤ) + (B \ X).ncard = B.ncard := by exact_mod_cast hcard
    have hind : M.Indep B := by
      rw [indep_iff_rk hBE]; linarith
    apply isBase_of_indep_ncard hind
    rw [← hX.2, rk_isBasis' h1, rk_isBasis' h2]
    linarith

variable (M : Matroid α) [M.Finite] (X : Set α)

/-- `𝓑(M) ≃ 𝓑(M | X) × 𝓑(M | (E - X))` for a separator `X`. -/
noncomputable def basesEquiv (hX : Sep M X) : Bases M ≃ Bases (M ↾ X) × Bases (M ↾ (M.E \ X)) where
  toFun B := (⟨B.1 ∩ X, ((isBase_iff_of_sep hX).1 B.2).2.1⟩,
    ⟨B.1 \ X, ((isBase_iff_of_sep hX).1 B.2).2.2⟩)
  invFun p := ⟨p.1.1 ∪ p.2.1, by
    have h1 := p.1.2
    have h2 := p.2.2
    have s1 : p.1.1 ⊆ X := h1.subset_ground
    have s2 : p.2.1 ⊆ M.E \ X := h2.subset_ground
    have e1 : (p.1.1 ∪ p.2.1) ∩ X = p.1.1 := by
      ext x; simp only [mem_inter_iff, mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact absurd hx (s2 h).2
      · intro h; exact ⟨Or.inl h, s1 h⟩
    have e2 : (p.1.1 ∪ p.2.1) \ X = p.2.1 := by
      ext x; simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact absurd (s1 h) hx
        · exact h
      · intro h; exact ⟨Or.inr h, (s2 h).2⟩
    rw [isBase_iff_of_sep hX, e1, e2]
    exact ⟨union_subset (s1.trans hX.1) (s2.trans sdiff_subset), h1, h2⟩⟩
  left_inv B := Subtype.ext (inter_union_sdiff B.1 X)
  right_inv p := by
    have s1 : p.1.1 ⊆ X := p.1.2.subset_ground
    have s2 : p.2.1 ⊆ M.E \ X := p.2.2.subset_ground
    ext x
    · simp only [mem_inter_iff, mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact absurd hx (s2 h).2
      · intro h; exact ⟨Or.inl h, s1 h⟩
    · simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact absurd (s1 h) hx
        · exact h
      · intro h; exact ⟨Or.inr h, (s2 h).2⟩

theorem basesEquiv_symm_val (hX : Sep M X) (p : Bases (M ↾ X) × Bases (M ↾ (M.E \ X))) :
    ((basesEquiv M X hX).symm p).1 = p.1.1 ∪ p.2.1 := rfl

/-! ### The kernel in product coordinates (Step 1) -/

section Kernel

variable {M X}
variable {P Q : Type*}

/-- `A₁ ⊗ id`: the column-wise basis incidence map. -/
noncomputable def colInc (A : (P →₀ ℤ) →ₗ[ℤ] (α → ℤ)) : (P × Q →₀ ℤ) →ₗ[ℤ] (Q →₀ (α → ℤ)) :=
  Finsupp.linearCombination ℤ (fun pq : P × Q => Finsupp.single pq.2 (A (Finsupp.single pq.1 1)))

theorem colInc_apply (A : (P →₀ ℤ) →ₗ[ℤ] (α → ℤ)) (f : P × Q →₀ ℤ) (q : Q) :
    colInc (Q := Q) A f q = A (col q f) := by
  classical
  have : (Finsupp.lapply q) ∘ₗ (colInc (Q := Q) A) = A ∘ₗ (col q) := by
    apply Finsupp.lhom_ext
    intro pq c
    obtain ⟨p, q'⟩ := pq
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lapply_apply, colInc,
      Finsupp.linearCombination_single]
    have hc : col q (Finsupp.single (p, q') c) = if q' = q then Finsupp.single p c else 0 := by
      ext p'
      rw [col_apply]
      by_cases h : q' = q
      · subst h; simp [Finsupp.single_apply, Prod.ext_iff]
      · simp [Prod.ext_iff, h]
    rw [hc]
    by_cases h : q' = q
    · subst h
      simp only [Finsupp.smul_apply, Finsupp.single_eq_same, ite_true]
      rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    · simp [h]
  exact LinearMap.congr_fun this f

end Kernel

/-- `ℤ^𝓑(M) ≅ ℤ^(𝓑(M₁) × 𝓑(M₂))`. -/
noncomputable def splitEquiv (hX : Sep M X) :
    (Bases M →₀ ℤ) ≃ₗ[ℤ] (Bases (M ↾ X) × Bases (M ↾ (M.E \ X)) →₀ ℤ) :=
  Finsupp.domLCongr (basesEquiv M X hX)

theorem splitEquiv_symm_single (hX : Sep M X) (p : Bases (M ↾ X) × Bases (M ↾ (M.E \ X)))
    (c : ℤ) : (splitEquiv M X hX).symm (Finsupp.single p c) =
      Finsupp.single ((basesEquiv M X hX).symm p) c := by
  simp [splitEquiv, Finsupp.domLCongr_symm]

/-! ### Step 1 in product coordinates -/

section Step1

variable {M X}

omit [M.Finite] in
theorem restrict_bases_subset {R : Set α} (B : Bases (M ↾ R)) : B.1 ⊆ R := B.2.subset_ground

theorem inc_split (hX : Sep M X) (f : Bases (M ↾ X) × Bases (M ↾ (M.E \ X)) →₀ ℤ) :
    incidence M ((splitEquiv M X hX).symm f) =
      incidence (M ↾ X) (Finsupp.mapDomain Prod.fst f) +
        incidence (M ↾ (M.E \ X)) (Finsupp.mapDomain Prod.snd f) := by
  classical
  have : incidence M ∘ₗ ((splitEquiv M X hX).symm :
        (Bases (M ↾ X) × Bases (M ↾ (M.E \ X)) →₀ ℤ) →ₗ[ℤ] (Bases M →₀ ℤ)) =
      incidence (M ↾ X) ∘ₗ Finsupp.lmapDomain ℤ ℤ Prod.fst +
        incidence (M ↾ (M.E \ X)) ∘ₗ Finsupp.lmapDomain ℤ ℤ Prod.snd := by
    apply Finsupp.lhom_ext
    intro pq c
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      splitEquiv_symm_single, LinearMap.add_apply,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, incidence,
      Finsupp.linearCombination_single]
    rw [← smul_add]
    congr 1
    rw [basesEquiv_symm_val]
    exact Set.indicator_union_of_disjoint (Set.disjoint_left.2 (fun x h1 h2 =>
      (restrict_bases_subset pq.2 h2).2 (restrict_bases_subset pq.1 h1))) _
  exact LinearMap.congr_fun this f

theorem mem_ker_iff_split (hX : Sep M X) (f : Bases (M ↾ X) × Bases (M ↾ (M.E \ X)) →₀ ℤ) :
    (splitEquiv M X hX).symm f ∈ LinearMap.ker (incidence M) ↔
      Finsupp.mapDomain Prod.fst f ∈ LinearMap.ker (incidence (M ↾ X)) ∧
        Finsupp.mapDomain Prod.snd f ∈ LinearMap.ker (incidence (M ↾ (M.E \ X))) := by
  simp only [LinearMap.mem_ker, inc_split hX]
  constructor
  · intro h
    have z1 : ∀ a, a ∉ X → incidence (M ↾ X) (Finsupp.mapDomain Prod.fst f) a = 0 :=
      fun a ha => incidence_eq_zero_of_notMem _ _ (by simpa using ha)
    have z2 : ∀ a, a ∉ M.E \ X →
        incidence (M ↾ (M.E \ X)) (Finsupp.mapDomain Prod.snd f) a = 0 :=
      fun a ha => incidence_eq_zero_of_notMem _ _ (by simpa using ha)
    constructor
    · funext a
      by_cases ha : a ∈ X
      · have := congrFun h a
        simp only [Pi.add_apply, Pi.zero_apply] at this
        have hz := z2 a (fun h' => h'.2 ha)
        rw [hz, add_zero] at this
        exact this
      · exact z1 a ha
    · funext a
      by_cases ha : a ∈ M.E \ X
      · have := congrFun h a
        simp only [Pi.add_apply, Pi.zero_apply] at this
        have hz := z1 a ha.2
        rw [hz, zero_add] at this
        exact this
      · exact z2 a ha
  · rintro ⟨h1, h2⟩
    rw [h1, h2, add_zero]

theorem mapDomain_snd_apply {P Q : Type*} (f : P × Q →₀ ℤ) (q : Q) :
    Finsupp.mapDomain Prod.snd f q = total (col q f) := by
  classical
  have : (Finsupp.lapply q) ∘ₗ (Finsupp.lmapDomain ℤ ℤ (Prod.snd : P × Q → Q)) =
      (Finsupp.linearCombination ℤ (fun _ : P => (1 : ℤ))) ∘ₗ col q := by
    apply Finsupp.lhom_ext
    intro pq c
    obtain ⟨p, q'⟩ := pq
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lapply_apply,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    have hc : col q (Finsupp.single (p, q') c) = if q' = q then Finsupp.single p c else 0 := by
      ext p'
      rw [col_apply]
      by_cases h : q' = q
      · subst h; simp [Finsupp.single_apply, Prod.ext_iff]
      · simp [Prod.ext_iff, h]
    rw [hc]
    by_cases h : q' = q
    · subst h; simp
    · simp [h]
  have h2 := LinearMap.congr_fun this f
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lapply_apply,
    Finsupp.lmapDomain_apply] at h2
  rw [h2]
  simp [total, Finsupp.linearCombination_apply]

theorem sum_colInc {P Q : Type*} (A : (P →₀ ℤ) →ₗ[ℤ] (α → ℤ)) (f : P × Q →₀ ℤ) :
    Finsupp.lsum ℤ (fun _ : Q => (LinearMap.id : (α → ℤ) →ₗ[ℤ] (α → ℤ))) (colInc A f) =
      A (Finsupp.mapDomain Prod.fst f) := by
  have : (Finsupp.lsum ℤ (fun _ : Q => (LinearMap.id : (α → ℤ) →ₗ[ℤ] (α → ℤ)))) ∘ₗ colInc A =
      A ∘ₗ Finsupp.lmapDomain ℤ ℤ (Prod.fst : P × Q → P) := by
    apply Finsupp.lhom_ext
    intro pq c
    simp only [LinearMap.coe_comp, Function.comp_apply, colInc,
      Finsupp.linearCombination_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rw [map_smul, Finsupp.lsum_single, LinearMap.id_apply, ← map_smul, Finsupp.smul_single,
      smul_eq_mul, mul_one]
  exact LinearMap.congr_fun this f

end Step1

/-! ### Step 3: a spanning forest of the exchange graph -/

section Step3

open scoped Classical

/-- The map `ℤ^V → ℤ^α`, `e_x ↦ e_{x}`, for `V ⊆ α`. -/
noncomputable def vecOf (V : Set α) : (V →₀ ℤ) →ₗ[ℤ] (α → ℤ) :=
  Finsupp.linearCombination ℤ (fun x : V => Pi.single x.1 (1 : ℤ))

theorem vecOf_apply (V : Set α) (w : V →₀ ℤ) (x : V) : vecOf V w x.1 = w x := by
  classical
  have : (LinearMap.proj x.1 : (α → ℤ) →ₗ[ℤ] ℤ) ∘ₗ vecOf V = Finsupp.lapply x := by
    apply Finsupp.lhom_ext
    intro y c
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
      vecOf, Finsupp.linearCombination_single, Pi.smul_apply, Finsupp.lapply_apply,
      Finsupp.single_apply, smul_eq_mul]
    by_cases h : y = x
    · subst h; simp
    · have h' : x.1 ≠ y.1 := fun e => h (Subtype.ext e.symm)
      simp [h', h]
  exact LinearMap.congr_fun this w

theorem vecOf_injective (V : Set α) : Function.Injective (vecOf V) := by
  intro w w' h
  ext x
  rw [← vecOf_apply V w x, ← vecOf_apply V w' x, h]

theorem vecOf_single_sub (V : Set α) (x y : V) :
    vecOf V (Finsupp.single x 1 - Finsupp.single y 1) = Pi.single x.1 1 - Pi.single y.1 1 := by
  simp [vecOf]

theorem indicator_insert_sub {D : Set α} {a b : α} (ha : a ∉ D) (hb : b ∉ D) :
    Set.indicator (insert a D) (fun _ => (1 : ℤ)) - Set.indicator (insert b D) (fun _ => 1) =
      Pi.single a 1 - Pi.single b 1 := by
  classical
  funext x
  simp only [Pi.sub_apply, Set.indicator_apply, Set.mem_insert_iff, Pi.single_apply]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxD : x ∈ D <;> simp_all

/-- **Step 3.** For a finite matroid `N` there is a family of vectors `φ_i = e_a - e_b` (edges
of a spanning forest of the exchange graph), linearly independent, with
`φ_i = A_N u_i` for `u_i = e_{D+a} - e_{D+b}`, such that `A_N(V⁰) ⊆ span φ`. -/
theorem step3 (N : Matroid α) [N.Finite] :
    ∃ (ι : Type u) (φ : ι → (α → ℤ)) (u : ι → (Bases N →₀ ℤ)),
      LinearIndependent ℤ φ ∧ (∀ i, incidence N (u i) = φ i) ∧
      (∀ i, ∃ (a b : α) (D : Set α) (h₁ : N.IsBase (insert a D)) (h₂ : N.IsBase (insert b D)),
        a ≠ b ∧ a ∉ D ∧ b ∉ D ∧ u i = Finsupp.single ⟨_, h₁⟩ 1 - Finsupp.single ⟨_, h₂⟩ 1) ∧
      (∀ w, total w = 0 → incidence N w ∈ Submodule.span ℤ (range φ)) := by
  classical
  let V : Set α := N.E
  have : Finite V := N.ground_finite.to_subtype
  let Adj : V → V → Prop := fun x y => x ≠ y ∧ ∃ D, x.1 ∉ D ∧ y.1 ∉ D ∧
    N.IsBase (insert x.1 D) ∧ N.IsBase (insert y.1 D)
  have hsymm : ∀ x y, Adj x y → Adj y x := by
    rintro x y ⟨hxy, D, h1, h2, h3, h4⟩; exact ⟨Ne.symm hxy, D, h2, h1, h4, h3⟩
  obtain ⟨Nf, p, hpAdj, hli, hspanE⟩ := forest_basis Adj hsymm
  let φ : Nf → (α → ℤ) := fun a => Pi.single a.1.1 1 - Pi.single (p a).1 1
  have hφ : φ = vecOf V ∘ (fun a : Nf => Finsupp.single a.1 (1 : ℤ) - Finsupp.single (p a) 1) := by
    funext a; simp only [Function.comp_apply, vecOf_single_sub, φ]
  have hφli : LinearIndependent ℤ φ := by
    rw [hφ]
    exact hli.map' (vecOf V) (LinearMap.ker_eq_bot.2 (vecOf_injective V))
  choose hne D hD1 hD2 hb1 hb2 using hpAdj
  let u : Nf → (Bases N →₀ ℤ) := fun a =>
    Finsupp.single ⟨_, hb2 a⟩ 1 - Finsupp.single ⟨_, hb1 a⟩ 1
  refine ⟨Nf, φ, u, hφli, ?_, ?_, ?_⟩
  · intro a
    simp only [u, φ, map_sub, incidence, Finsupp.linearCombination_single, one_smul]
    exact indicator_insert_sub (hD2 a) (hD1 a)
  · intro a
    exact ⟨a.1.1, (p a).1, D a, hb2 a, hb1 a, fun h => hne a (Subtype.ext h.symm), hD2 a, hD1 a, rfl⟩
  · -- every edge vector lies in the span of `φ`
    have hedge : ∀ x y : V, Adj x y → Pi.single x.1 (1 : ℤ) - Pi.single y.1 1 ∈
        Submodule.span ℤ (range φ) := by
      intro x y hxy
      have h1 := hspanE x y hxy
      have h2 := Submodule.mem_map_of_mem (f := vecOf V) h1
      rw [← Submodule.span_image, ← range_comp, ← hφ] at h2
      rwa [vecOf_single_sub] at h2
    -- `1_J - 1_{J'}` lies in the span, by basis exchange
    have hpair : ∀ n, ∀ J J' : Bases N, (J.1 \ J'.1).ncard = n →
        Set.indicator J.1 (fun _ => (1 : ℤ)) - Set.indicator J'.1 (fun _ => 1) ∈
          Submodule.span ℤ (range φ) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro J J' hn
      by_cases hJJ : J = J'
      · subst hJJ; simp
      have hsub : ¬ J.1 ⊆ J'.1 := fun h => hJJ (Subtype.ext (J.2.eq_of_subset_isBase J'.2 h))
      obtain ⟨e, heJ, heJ'⟩ := not_subset.1 hsub
      obtain ⟨y, ⟨hyJ', hyJ⟩, hJ''⟩ := J.2.exchange J'.2 ⟨heJ, heJ'⟩
      let J'' : Bases N := ⟨_, hJ''⟩
      have hfin : (J.1 \ J'.1).Finite := N.ground_finite.subset (sdiff_subset.trans J.2.subset_ground)
      have hlt : (J''.1 \ J'.1).ncard < n := by
        rw [← hn]
        apply Set.ncard_lt_ncard _ hfin
        refine ⟨?_, fun h => ?_⟩
        · rintro x ⟨hx, hxJ'⟩
          rcases hx with rfl | ⟨hxJ, -⟩
          · exact absurd hyJ' hxJ'
          · exact ⟨hxJ, hxJ'⟩
        · have := h ⟨heJ, heJ'⟩
          rcases this.1 with h' | h'
          · rw [h'] at heJ'; exact heJ' hyJ'
          · exact h'.2 rfl
      have hstep : Set.indicator J.1 (fun _ => (1 : ℤ)) - Set.indicator J''.1 (fun _ => 1) =
          Pi.single e 1 - Pi.single y 1 := by
        have := indicator_insert_sub (D := J.1 \ {e}) (a := e) (b := y) (fun h => h.2 rfl)
          (fun h => hyJ h.1)
        rw [insert_sdiff_singleton, insert_eq_of_mem heJ] at this
        exact this
      have hey : e ≠ y := fun h => heJ' (h ▸ hyJ')
      have hadj : Adj ⟨e, J.2.subset_ground heJ⟩ ⟨y, hJ''.subset_ground (mem_insert _ _)⟩ := by
        refine ⟨fun h => hey (congrArg Subtype.val h), J.1 \ {e}, fun h => h.2 rfl,
          fun h => hyJ h.1, ?_, hJ''⟩
        rw [insert_sdiff_singleton, insert_eq_of_mem heJ]; exact J.2
      have e1 : Set.indicator J.1 (fun _ => (1 : ℤ)) - Set.indicator J'.1 (fun _ => 1) =
          (Set.indicator J.1 (fun _ => (1 : ℤ)) - Set.indicator J''.1 (fun _ => 1)) +
          (Set.indicator J''.1 (fun _ => (1 : ℤ)) - Set.indicator J'.1 (fun _ => 1)) := by abel
      rw [e1, hstep]
      exact Submodule.add_mem _ (hedge _ _ hadj) (ih _ hlt J'' J' rfl)
    obtain ⟨J₀, hJ₀⟩ := N.exists_isBase
    have hall : ∀ w : Bases N →₀ ℤ, incidence N w - total w • Set.indicator J₀ (fun _ => (1 : ℤ)) ∈
        Submodule.span ℤ (range φ) := by
      intro w
      induction w using Finsupp.induction_linear with
      | zero => simp [total]
      | add f g hf hg =>
        have e : incidence N (f + g) - total (f + g) • Set.indicator J₀ (fun _ => (1 : ℤ)) =
            (incidence N f - total f • Set.indicator J₀ (fun _ => (1 : ℤ))) +
            (incidence N g - total g • Set.indicator J₀ (fun _ => (1 : ℤ))) := by
          rw [map_add]
          have : total (f + g) = total f + total g := by
            simp only [total]; rw [Finsupp.sum_add_index'] <;> simp
          rw [this, add_smul]; abel
        rw [e]; exact Submodule.add_mem _ hf hg
      | single J c =>
        have e : incidence N (Finsupp.single J c) -
            total (Finsupp.single J c) • Set.indicator J₀ (fun _ => (1 : ℤ)) =
            c • (Set.indicator J.1 (fun _ => (1 : ℤ)) -
              Set.indicator (⟨J₀, hJ₀⟩ : Bases N).1 (fun _ => 1)) := by
          simp [incidence, total, smul_sub]
        rw [e]
        exact Submodule.smul_mem _ c (hpair _ J ⟨J₀, hJ₀⟩ rfl)
    intro w hw
    have := hall w
    rwa [hw, zero_smul, sub_zero] at this

end Step3

/-! ### Proposition 3.1 -/

theorem total_eq_lc {P : Type*} (f : P →₀ ℤ) :
    total f = Finsupp.linearCombination ℤ (fun _ : P => (1 : ℤ)) f := by
  simp [total, Finsupp.linearCombination_apply]

section Prop31

variable {M X}

/-- `s ↦ e_p ⊗ s`. -/
noncomputable def embL {P Q : Type*} (p : P) : (Q →₀ ℤ) →ₗ[ℤ] (P × Q →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun q => (p, q))

theorem basesEquiv_symm_mk (hX : Sep M X) {A B : Set α} (hA : (M ↾ X).IsBase A)
    (hB : (M ↾ (M.E \ X)).IsBase B) (h : M.IsBase (A ∪ B)) :
    (basesEquiv M X hX).symm (⟨A, hA⟩, ⟨B, hB⟩) = ⟨A ∪ B, h⟩ :=
  Subtype.ext (basesEquiv_symm_val M X hX _)

theorem isBase_union (hX : Sep M X) {A B : Set α} (hA : (M ↾ X).IsBase A)
    (hB : (M ↾ (M.E \ X)).IsBase B) : M.IsBase (A ∪ B) := by
  have := ((basesEquiv M X hX).symm (⟨A, hA⟩, ⟨B, hB⟩)).2
  rwa [basesEquiv_symm_val] at this

/-- Squares of family (1): `w ⊗ e_I = z_{i,j;D⊔I,D'⊔I}`. -/
theorem sq1 (hX : Sep M X) (q : Bases (M ↾ (M.E \ X))) {w : Bases (M ↾ X) →₀ ℤ}
    (hw : IsSquare (M ↾ X) w) : IsSquare M ((splitEquiv M X hX).symm (emb q w)) := by
  classical
  obtain ⟨i, j, D, D', h₁, h₂, h₃, h₄, hij, hDD', hiD, hjD, hiD', hjD', rfl⟩ := hw
  have hq : q.1 ⊆ M.E \ X := q.2.subset_ground
  have hDX : ∀ {i : α} {D : Set α}, (M ↾ X).IsBase (insert i D) → insert i D ⊆ X :=
    fun h => h.subset_ground
  have b₁ := isBase_union hX h₁ q.2
  have b₂ := isBase_union hX h₂ q.2
  have b₃ := isBase_union hX h₃ q.2
  have b₄ := isBase_union hX h₄ q.2
  rw [insert_union] at b₁ b₂ b₃ b₄
  have hnot : ∀ {x : α}, x ∈ X → x ∉ q.1 := fun hx h => (hq h).2 hx
  refine ⟨i, j, D ∪ q.1, D' ∪ q.1, b₁, b₂, b₃, b₄, hij, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hDD'
    have e : ∀ {E : Set α}, E ⊆ X → (E ∪ q.1) ∩ X = E := by
      intro E hE
      ext x; simp only [mem_inter_iff, mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact absurd hx (hq h).2
      · intro h; exact ⟨Or.inl h, hE h⟩
    rw [← e ((subset_insert i D).trans (hDX h₁)), ← e ((subset_insert i D').trans (hDX h₃)), h]
  · rintro (h | h)
    · exact hiD h
    · exact hnot (hDX h₁ (mem_insert _ _)) h
  · rintro (h | h)
    · exact hjD h
    · exact hnot (hDX h₂ (mem_insert _ _)) h
  · rintro (h | h)
    · exact hiD' h
    · exact hnot (hDX h₃ (mem_insert _ _)) h
  · rintro (h | h)
    · exact hjD' h
    · exact hnot (hDX h₄ (mem_insert _ _)) h
  · simp only [emb, map_add, map_sub, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      splitEquiv_symm_single]
    have e1 : (basesEquiv M X hX).symm (⟨insert i D, h₁⟩, q) = ⟨insert i (D ∪ q.1), b₁⟩ :=
      Subtype.ext (by rw [basesEquiv_symm_val, insert_union])
    have e2 : (basesEquiv M X hX).symm (⟨insert j D, h₂⟩, q) = ⟨insert j (D ∪ q.1), b₂⟩ :=
      Subtype.ext (by rw [basesEquiv_symm_val, insert_union])
    have e3 : (basesEquiv M X hX).symm (⟨insert i D', h₃⟩, q) = ⟨insert i (D' ∪ q.1), b₃⟩ :=
      Subtype.ext (by rw [basesEquiv_symm_val, insert_union])
    have e4 : (basesEquiv M X hX).symm (⟨insert j D', h₄⟩, q) = ⟨insert j (D' ∪ q.1), b₄⟩ :=
      Subtype.ext (by rw [basesEquiv_symm_val, insert_union])
    rw [e1, e2, e3, e4]

/-- Squares of family (2): `e_{I₁⁰} ⊗ s = z_{i,j;I₁⁰⊔D,I₁⁰⊔D'}`. -/
theorem sq2 (hX : Sep M X) (p : Bases (M ↾ X)) {w : Bases (M ↾ (M.E \ X)) →₀ ℤ}
    (hw : IsSquare (M ↾ (M.E \ X)) w) : IsSquare M ((splitEquiv M X hX).symm (embL p w)) := by
  classical
  obtain ⟨i, j, D, D', h₁, h₂, h₃, h₄, hij, hDD', hiD, hjD, hiD', hjD', rfl⟩ := hw
  have hp : p.1 ⊆ X := p.2.subset_ground
  have hDX : ∀ {i : α} {D : Set α}, (M ↾ (M.E \ X)).IsBase (insert i D) →
      insert i D ⊆ M.E \ X := fun h => h.subset_ground
  have b₁ := isBase_union hX p.2 h₁
  have b₂ := isBase_union hX p.2 h₂
  have b₃ := isBase_union hX p.2 h₃
  have b₄ := isBase_union hX p.2 h₄
  rw [union_insert] at b₁ b₂ b₃ b₄
  have hnot : ∀ {x : α}, x ∈ M.E \ X → x ∉ p.1 := fun hx h => hx.2 (hp h)
  refine ⟨i, j, p.1 ∪ D, p.1 ∪ D', b₁, b₂, b₃, b₄, hij, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hDD'
    have e : ∀ {E : Set α}, E ⊆ M.E \ X → (p.1 ∪ E) \ X = E := by
      intro E hE
      ext x; simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact absurd (hp h) hx
        · exact h
      · intro h; exact ⟨Or.inr h, (hE h).2⟩
    rw [← e ((subset_insert i D).trans (hDX h₁)), ← e ((subset_insert i D').trans (hDX h₃)), h]
  · rintro (h | h)
    · exact hnot (hDX h₁ (mem_insert _ _)) h
    · exact hiD h
  · rintro (h | h)
    · exact hnot (hDX h₂ (mem_insert _ _)) h
    · exact hjD h
  · rintro (h | h)
    · exact hnot (hDX h₃ (mem_insert _ _)) h
    · exact hiD' h
  · rintro (h | h)
    · exact hnot (hDX h₄ (mem_insert _ _)) h
    · exact hjD' h
  · simp only [embL, map_add, map_sub, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      splitEquiv_symm_single]
    have e1 : (basesEquiv M X hX).symm (p, ⟨insert i D, h₁⟩) = ⟨insert i (p.1 ∪ D), b₁⟩ :=
      Subtype.ext (by rw [basesEquiv_symm_val, union_insert])
    have e2 : (basesEquiv M X hX).symm (p, ⟨insert j D, h₂⟩) = ⟨insert j (p.1 ∪ D), b₂⟩ :=
      Subtype.ext (by rw [basesEquiv_symm_val, union_insert])
    have e3 : (basesEquiv M X hX).symm (p, ⟨insert i D', h₃⟩) = ⟨insert i (p.1 ∪ D'), b₃⟩ :=
      Subtype.ext (by rw [basesEquiv_symm_val, union_insert])
    have e4 : (basesEquiv M X hX).symm (p, ⟨insert j D', h₄⟩) = ⟨insert j (p.1 ∪ D'), b₄⟩ :=
      Subtype.ext (by rw [basesEquiv_symm_val, union_insert])
    rw [e1, e2, e3, e4]

/-- Squares of family (3): `u_{ab} ⊗ (e_I - e_{I₂⁰}) = z_{a,b;D⊔I,D⊔I₂⁰}`. -/
theorem sq3 (hX : Sep M X) {q q₀ : Bases (M ↾ (M.E \ X))} (hq : q ≠ q₀) {a b : α} {D : Set α}
    (h₁ : (M ↾ X).IsBase (insert a D)) (h₂ : (M ↾ X).IsBase (insert b D)) (hab : a ≠ b)
    (haD : a ∉ D) (hbD : b ∉ D) :
    IsSquare M ((splitEquiv M X hX).symm
      (emb q (Finsupp.single ⟨_, h₁⟩ 1 - Finsupp.single ⟨_, h₂⟩ 1) -
        emb q₀ (Finsupp.single ⟨_, h₁⟩ 1 - Finsupp.single ⟨_, h₂⟩ 1))) := by
  classical
  have hqE : q.1 ⊆ M.E \ X := q.2.subset_ground
  have hq₀E : q₀.1 ⊆ M.E \ X := q₀.2.subset_ground
  have hDX : insert a D ⊆ X := h₁.subset_ground
  have hbX : b ∈ X := h₂.subset_ground (mem_insert _ _)
  have b₁ := isBase_union hX h₁ q.2
  have b₂ := isBase_union hX h₂ q.2
  have b₃ := isBase_union hX h₁ q₀.2
  have b₄ := isBase_union hX h₂ q₀.2
  rw [insert_union] at b₁ b₂ b₃ b₄
  refine ⟨a, b, D ∪ q.1, D ∪ q₀.1, b₁, b₂, b₃, b₄, hab, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hq
    have e : ∀ {E : Set α}, E ⊆ M.E \ X → (D ∪ E) \ X = E := by
      intro E hE
      ext x; simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact absurd (hDX (mem_insert_of_mem _ h)) hx
        · exact h
      · intro h; exact ⟨Or.inr h, (hE h).2⟩
    apply Subtype.ext
    rw [← e hqE, ← e hq₀E, h]
  · rintro (h | h)
    · exact haD h
    · exact (hqE h).2 (hDX (mem_insert _ _))
  · rintro (h | h)
    · exact hbD h
    · exact (hqE h).2 hbX
  · rintro (h | h)
    · exact haD h
    · exact (hq₀E h).2 (hDX (mem_insert _ _))
  · rintro (h | h)
    · exact hbD h
    · exact (hq₀E h).2 hbX
  · simp only [emb, map_sub, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      splitEquiv_symm_single]
    have e1 : (basesEquiv M X hX).symm (⟨insert a D, h₁⟩, q) = ⟨insert a (D ∪ q.1), b₁⟩ :=
      Subtype.ext (by rw [basesEquiv_symm_val, insert_union])
    have e2 : (basesEquiv M X hX).symm (⟨insert b D, h₂⟩, q) = ⟨insert b (D ∪ q.1), b₂⟩ :=
      Subtype.ext (by rw [basesEquiv_symm_val, insert_union])
    have e3 : (basesEquiv M X hX).symm (⟨insert a D, h₁⟩, q₀) = ⟨insert a (D ∪ q₀.1), b₃⟩ :=
      Subtype.ext (by rw [basesEquiv_symm_val, insert_union])
    have e4 : (basesEquiv M X hX).symm (⟨insert b D, h₂⟩, q₀) = ⟨insert b (D ∪ q₀.1), b₄⟩ :=
      Subtype.ext (by rw [basesEquiv_symm_val, insert_union])
    rw [e1, e2, e3, e4]
    abel

/-- **Proposition 3.1.** If `X` is a separator of `M`, both parts have rank at least one and
`M | X`, `M | (E - X)` have square bases, then `M` has a square basis: the families
(1) `w ⊗ e_I`, (2) `e_{I₁⁰} ⊗ s` and (3) `u_{ab} ⊗ (e_I - e_{I₂⁰})` of the paper. -/
theorem prop31 (hX : Sep M X) [(M ↾ X).RankPos] [(M ↾ (M.E \ X)).RankPos]
    (h1 : HasSquareBasis (M ↾ X)) (h2 : HasSquareBasis (M ↾ (M.E \ X))) : HasSquareBasis M := by
  classical
  have hXE : X ⊆ M.E := hX.1
  have : (M ↾ X).Finite := restrict_finite (M.ground_finite.subset hXE)
  have : (M ↾ (M.E \ X)).Finite := restrict_finite (M.ground_finite.subset sdiff_subset)
  obtain ⟨R₁, hR₁sq, hR₁li, hR₁span⟩ := h1
  obtain ⟨R₂, hR₂sq, hR₂li, hR₂span⟩ := h2
  obtain ⟨J₁, hJ₁⟩ := (M ↾ X).exists_isBase
  obtain ⟨J₂, hJ₂⟩ := (M ↾ (M.E \ X)).exists_isBase
  set I₁ : Bases (M ↾ X) := ⟨J₁, hJ₁⟩ with hI₁
  set I₂ : Bases (M ↾ (M.E \ X)) := ⟨J₂, hJ₂⟩ with hI₂
  set Ψ := splitEquiv M X hX with hΨ
  set A₁ := incidence (M ↾ X) with hA₁
  set K₁ := LinearMap.ker A₁ with hK₁
  set K₂ := LinearMap.ker (incidence (M ↾ (M.E \ X))) with hK₂
  set L0 : Submodule ℤ (Bases (M ↾ X) × Bases (M ↾ (M.E \ X)) →₀ ℤ) :=
    (LinearMap.ker (incidence M)).comap (Ψ.symm : _ →ₗ[ℤ] _) with hL0def
  have hL0 : ∀ f, f ∈ L0 ↔ Finsupp.mapDomain Prod.fst f ∈ K₁ ∧
      Finsupp.mapDomain Prod.snd f ∈ K₂ := fun f => by
    simp only [hL0def, Submodule.mem_comap, LinearEquiv.coe_coe]
    exact mem_ker_iff_split hX f
  set ρ := colInc (Q := Bases (M ↾ (M.E \ X))) A₁ with hρ
  -- family (1): a basis of `L0 ∩ ker ρ = K₁ ⊗ V₂`
  obtain ⟨hS₁li, hS₁span⟩ := tensor_basis (Q := Bases (M ↾ (M.E \ X))) K₁ R₁ hR₁li hR₁span
  set S₁ := ⋃ q : Bases (M ↾ (M.E \ X)), (emb q : (Bases (M ↾ X) →₀ ℤ) → _) '' R₁ with hS₁
  have hker : Submodule.span ℤ S₁ = L0 ⊓ LinearMap.ker ρ := by
    rw [hS₁span]
    apply le_antisymm
    · intro f hf
      simp only [Submodule.mem_iInf, Submodule.mem_comap, hK₁, LinearMap.mem_ker] at hf
      have hρf : ρ f = 0 := by
        ext q a
        rw [hρ, colInc_apply, hf q]
        rfl
      refine ⟨(hL0 f).2 ⟨?_, ?_⟩, hρf⟩
      · rw [hK₁, LinearMap.mem_ker, ← sum_colInc, ← hρ, hρf, map_zero]
      · have : Finsupp.mapDomain Prod.snd f = 0 := by
          ext q
          rw [mapDomain_snd_apply]
          exact total_eq_zero_of_mem_ker (M ↾ X) (LinearMap.mem_ker.2 (hf q))
        rw [this]; exact K₂.zero_mem
    · rintro f ⟨-, hf⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker] at hf
      simp only [Submodule.mem_iInf, Submodule.mem_comap, hK₁, LinearMap.mem_ker]
      intro q
      rw [← colInc_apply, ← hρ, hf]
      rfl
  -- Step 3 data for `M₁`
  obtain ⟨ι, φ, u, hφli, hφu, hushape, hΛ⟩ := step3 (M ↾ X)
  set x₁ : α → ℤ := A₁ (Finsupp.single I₁ 1) with hx₁
  -- the coordinate sum over `X`
  have hXfin : X.Finite := M.ground_finite.subset hXE
  let σE : (α → ℤ) →ₗ[ℤ] ℤ :=
    { toFun := fun x => ∑ a ∈ hXfin.toFinset, x a
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum] }
  have hσE : ∀ J : Bases (M ↾ X), σE (A₁ (Finsupp.single J 1)) = J₁.ncard := by
    intro J
    show ∑ a ∈ hXfin.toFinset, A₁ (Finsupp.single J 1) a = _
    simp only [hA₁, incidence, Finsupp.linearCombination_single, one_smul, Set.indicator_apply]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1 : ((hXfin.toFinset.filter (· ∈ J.1) : Finset α) : Set α) = J.1 := by
      ext x
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨J.2.subset_ground h, h⟩⟩
    have h2 := Set.ncard_coe_finset (hXfin.toFinset.filter (· ∈ J.1))
    rw [h1] at h2
    rw [← h2, J.2.ncard_eq_ncard_of_isBase hJ₁]
  have hk₁ : (J₁.ncard : ℤ) ≠ 0 := by
    have := (Set.ncard_pos (hXfin.subset hJ₁.subset_ground)).2 hJ₁.nonempty
    omega
  have hσφ : ∀ i, σE (φ i) = 0 := by
    intro i
    obtain ⟨a, b, D, h₁, h₂, -, -, -, hu⟩ := hushape i
    rw [← hφu i, hu, map_sub, map_sub, hσE, hσE, sub_self]
  -- the map `s ↦ ρ(e_{I₁⁰} ⊗ s)`
  let μ : (Bases (M ↾ (M.E \ X)) →₀ ℤ) →ₗ[ℤ] (Bases (M ↾ (M.E \ X)) →₀ (α → ℤ)) :=
    Finsupp.mapRange.linearMap (LinearMap.smulRight LinearMap.id x₁)
  have hμ : ∀ g q, μ g q = g q • x₁ := fun g q => rfl
  have hρL : ∀ g, ρ (embL I₁ g) = μ g := by
    intro g
    have : ρ ∘ₗ embL I₁ = μ := by
      apply Finsupp.lhom_ext
      intro q c
      simp only [LinearMap.coe_comp, Function.comp_apply, embL, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single, hρ, colInc, Finsupp.linearCombination_single]
      ext q' a
      by_cases h : q = q'
      · subst h; simp [μ, hx₁]
      · simp [μ, h]
    exact LinearMap.congr_fun this g
  have hρemb : ∀ q w, ρ (emb q w) = Finsupp.single q (A₁ w) := by
    intro q w
    have : ρ ∘ₗ emb q = (Finsupp.lsingle q) ∘ₗ A₁ := by
      apply Finsupp.lhom_ext
      intro p c
      simp only [LinearMap.coe_comp, Function.comp_apply, emb, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single, hρ, colInc, Finsupp.linearCombination_single,
        Finsupp.lsingle_apply, Finsupp.smul_single]
      rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    exact LinearMap.congr_fun this w
  -- the family `t`: (2) and (3)
  let t : R₂ ⊕ (ι × {q : Bases (M ↾ (M.E \ X)) // q ≠ I₂}) →
      (Bases (M ↾ X) × Bases (M ↾ (M.E \ X)) →₀ ℤ) :=
    Sum.elim (fun s => embL I₁ s.1) (fun iq => emb iq.2.1 (u iq.1) - emb I₂ (u iq.1))
  let vA : R₂ → (Bases (M ↾ (M.E \ X)) →₀ (α → ℤ)) := fun s => μ s.1
  let vB : ι × {q : Bases (M ↾ (M.E \ X)) // q ≠ I₂} → (Bases (M ↾ (M.E \ X)) →₀ (α → ℤ)) :=
    fun iq => Finsupp.single iq.2.1 (φ iq.1) - Finsupp.single I₂ (φ iq.1)
  have hρt : ρ ∘ t = Sum.elim vA vB := by
    funext i
    rcases i with s | ⟨i, q⟩
    · simp only [Function.comp_apply, Sum.elim_inl, t, vA, hρL]
    · simp only [Function.comp_apply, Sum.elim_inr, t, vB, map_sub, hρemb]
      rw [hA₁, hφu]
  -- squares
  have htsq : ∀ i, IsSquare M (Ψ.symm (t i)) := by
    intro i
    rcases i with s | ⟨i, q⟩
    · exact sq2 hX I₁ (hR₂sq s.1 s.2)
    · obtain ⟨a, b, D, h₁, h₂, hab, haD, hbD, hu⟩ := hushape i
      show IsSquare M (Ψ.symm (emb q.1 (u i) - emb I₂ (u i)))
      rw [hu]
      exact sq3 hX q.2 h₁ h₂ hab haD hbD
  have ht : ∀ i, t i ∈ L0 := by
    intro i
    simp only [hL0def, Submodule.mem_comap, LinearEquiv.coe_coe]
    exact (htsq i).mem_ker
  -- independence of `ρ ∘ t`
  obtain ⟨a₀, ha₀⟩ := hJ₁.nonempty
  have hx₁a₀ : x₁ a₀ = 1 := by
    show A₁ (Finsupp.single I₁ 1) a₀ = 1
    rw [hA₁, hI₁]
    simp [incidence, Finsupp.linearCombination_single, Set.indicator_of_mem ha₀]
  have hμker : LinearMap.ker μ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    ext q
    have := congrArg (fun F => F q a₀) hg
    simp only [hμ, Pi.smul_apply, hx₁a₀, smul_eq_mul, mul_one, Finsupp.coe_zero,
      Pi.zero_apply] at this
    simpa using this
  have hA : LinearIndependent ℤ vA := hR₂li.map' μ hμker
  have hB : LinearIndependent ℤ vB := by
    rw [linearIndependent_iff']
    intro T c hc j hj
    have h1 := congrArg (fun F => F j.2.1) hc
    simp only [Finset.sum_apply', Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_apply, vB,
      Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply] at h1
    have hne : I₂ ≠ j.2.1 := fun h => j.2.2 h.symm
    simp only [hne, ite_false, sub_zero] at h1
    rw [← Finset.sum_filter_add_sum_filter_not T (fun k => k.2 = j.2)] at h1
    rw [Finset.sum_eq_zero (s := T.filter (fun k => ¬ k.2 = j.2)) (fun k hk => by
      have : ¬ k.2.1 = j.2.1 := fun h => (Finset.mem_filter.1 hk).2 (Subtype.ext h)
      rw [ite_eq_right this, smul_zero]), add_zero] at h1
    rw [Finset.sum_congr rfl (fun k hk => by
      rw [ite_eq_left (congrArg Subtype.val (Finset.mem_filter.1 hk).2)])] at h1
    have hinj : Set.InjOn (fun k : ι × {q : Bases (M ↾ (M.E \ X)) // q ≠ I₂} => k.1)
        (T.filter (fun k => k.2 = j.2)) := by
      intro k hk k' hk' h
      exact Prod.ext h ((Finset.mem_filter.1 hk).2.trans (Finset.mem_filter.1 hk').2.symm)
    have h2 : ∑ i ∈ (T.filter (fun k => k.2 = j.2)).image (fun k => k.1),
        c (i, j.2) • φ i = 0 := by
      rw [Finset.sum_image hinj, ← h1]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k = (k.1, j.2) := Prod.ext rfl (Finset.mem_filter.1 hk).2
      rw [← hk']
    exact linearIndependent_iff'.1 hφli _ (fun i => c (i, j.2)) h2 j.1
      (Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨hj, rfl⟩, rfl⟩)
  let Φ0 : (Bases (M ↾ (M.E \ X)) →₀ (α → ℤ)) →ₗ[ℤ] (Bases (M ↾ (M.E \ X)) →₀ ℤ) :=
    Finsupp.mapRange.linearMap σE
  have hΦ0B : ∀ k, Φ0 (vB k) = 0 := by
    intro k
    simp only [Φ0, vB, map_sub, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      hσφ, Finsupp.single_zero, sub_zero]
  have hΦ0μ : ∀ g, Φ0 (μ g) = (J₁.ncard : ℤ) • g := by
    intro g
    ext q
    simp only [Φ0, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, hμ,
      Finsupp.smul_apply, smul_eq_mul]
    rw [map_smul, hx₁, hσE I₁, smul_eq_mul, mul_comm]
  have hdisj : Disjoint (Submodule.span ℤ (range vA)) (Submodule.span ℤ (range vB)) := by
    rw [Submodule.disjoint_def]
    intro x hxA hxB
    have hΦx : Φ0 x = 0 := by
      have : Submodule.span ℤ (range vB) ≤ LinearMap.ker Φ0 := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        exact hΦ0B k
      exact this hxB
    have hrA : range vA = μ '' R₂ := by
      ext y; simp [vA]
    rw [hrA, Submodule.span_image] at hxA
    obtain ⟨y, -, rfl⟩ := hxA
    rw [hΦ0μ] at hΦx
    have hy : y = 0 := by
      rcases smul_eq_zero.1 hΦx with h | h
      · exact absurd h hk₁
      · exact h
    rw [hy, map_zero]
  have hρtli : LinearIndependent ℤ (ρ ∘ t) := by
    rw [hρt]; exact hA.sum_type hB hdisj
  -- `ρ(L0)` is covered
  have hcover : L0.map ρ ≤ Submodule.span ℤ (range (ρ ∘ t)) := by
    rw [hρt, Set.Sum.elim_range, Submodule.span_union]
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨hrow, hcol⟩ := (hL0 f).1 hf
    set c := Finsupp.mapDomain Prod.snd f with hc
    have hμc : μ c ∈ Submodule.span ℤ (range vA) := by
      have hrA : range vA = μ '' R₂ := by ext y; simp [vA]
      rw [hrA, Submodule.span_image, hR₂span]
      exact Submodule.mem_map_of_mem hcol
    set g := ρ f - μ c with hg
    have hgq : ∀ q, g q ∈ Submodule.span ℤ (range φ) := by
      intro q
      have e : g q = A₁ (col q f - total (col q f) • Finsupp.single I₁ 1) := by
        simp only [hg, Finsupp.coe_sub, Pi.sub_apply, hρ, colInc_apply, hμ, hc,
          mapDomain_snd_apply, map_sub, map_smul, hx₁]
      rw [e]
      apply hΛ
      rw [total_eq_lc, map_sub, map_smul, ← total_eq_lc, ← total_eq_lc]
      simp [total]
    have hsumg : Finsupp.lsum ℤ (fun _ => (LinearMap.id : (α → ℤ) →ₗ[ℤ] (α → ℤ))) g = 0 := by
      have h1 : Finsupp.lsum ℤ (fun _ => (LinearMap.id : (α → ℤ) →ₗ[ℤ] (α → ℤ))) (ρ f) = 0 := by
        rw [hρ, sum_colInc]; exact hrow
      have h2 : Finsupp.lsum ℤ (fun _ => (LinearMap.id : (α → ℤ) →ₗ[ℤ] (α → ℤ))) (μ c) =
          total c • x₁ := by
        have hlin : (Finsupp.lsum ℤ (fun _ => (LinearMap.id : (α → ℤ) →ₗ[ℤ] (α → ℤ)))) ∘ₗ μ =
            LinearMap.smulRight (Finsupp.linearCombination ℤ
              (fun _ : Bases (M ↾ (M.E \ X)) => (1 : ℤ))) x₁ := by
          apply Finsupp.lhom_ext
          intro q k
          simp [μ, Finsupp.mapRange_single]
        rw [total_eq_lc]
        exact LinearMap.congr_fun hlin c
      have h3 : total c = 0 :=
        total_eq_zero_of_mem_ker (M ↾ (M.E \ X)) hcol
      rw [hg, map_sub, h1, h2, h3, zero_smul, sub_zero]
    have hgdec : g = g.sum (fun q v => Finsupp.single q v - Finsupp.single I₂ v) := by
      rw [Finsupp.sum_sub, Finsupp.sum_single]
      have : g.sum (fun _ v => Finsupp.single I₂ v) = Finsupp.single I₂
          (Finsupp.lsum ℤ (fun _ => (LinearMap.id : (α → ℤ) →ₗ[ℤ] (α → ℤ))) g) := by
        rw [Finsupp.lsum_apply, Finsupp.single_sum]
        rfl
      rw [this, hsumg, Finsupp.single_zero, sub_zero]
    have hgB : g ∈ Submodule.span ℤ (range vB) := by
      rw [hgdec]
      refine Submodule.sum_mem _ (fun q _ => ?_)
      show Finsupp.single q (g q) - Finsupp.single I₂ (g q) ∈ _
      by_cases hq : q = I₂
      · rw [hq, sub_self]; exact Submodule.zero_mem _
      · let Lq : (α → ℤ) →ₗ[ℤ] (Bases (M ↾ (M.E \ X)) →₀ (α → ℤ)) :=
          Finsupp.lsingle q - Finsupp.lsingle I₂
        have h1 : Lq (g q) ∈ Submodule.span ℤ (Lq '' range φ) := by
          rw [Submodule.span_image]; exact Submodule.mem_map_of_mem (hgq q)
        have h2 : Lq '' range φ ⊆ range vB := by
          rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨(i, ⟨q, hq⟩), rfl⟩
        have h3 : Finsupp.single q (g q) - Finsupp.single I₂ (g q) = Lq (g q) := rfl
        rw [h3]
        exact Submodule.span_mono h2 h1
    have e : ρ f = μ c + g := by rw [hg]; abel
    rw [e]
    exact Submodule.add_mem_sup hμc hgB
  -- the basis of `L0`, transported back to `ℤ^𝓑(M)`
  obtain ⟨hli, hspan⟩ := basis_of_exact L0 ρ S₁ hS₁li hker t ht hρtli hcover
  refine ⟨(Ψ.symm : _ →ₗ[ℤ] _) '' (S₁ ∪ range t), ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rcases hz with hz | ⟨i, rfl⟩
    · simp only [hS₁, mem_iUnion, mem_image] at hz
      obtain ⟨q, w, hw, rfl⟩ := hz
      exact sq1 hX q (hR₁sq w hw)
    · exact htsq i
  · exact hli.image (by
      rw [LinearMap.ker_eq_bot.2 Ψ.symm.injective]; exact disjoint_bot_right)
  · rw [Submodule.span_image, hspan, hL0def]
    exact Submodule.map_comap_eq_of_surjective Ψ.symm.surjective _

end Prop31

end SquareBasis
