module

public import SquareBasis.Rank

/-!
# Separators, circuits and Tutte's theorem

* `Sep M X` : `X ⊆ E` and `r(X) + r(E \ X) = r(E)` (a separator).
* `sep_split` : across a separator the rank is additive.
* `IsCircuit.subset_or_subset_of_sep` : a circuit lies on one side of a separator.
* `sep_dual` : separators of `M` are separators of `M✶`.
* `exists_isCircuit_of_trans` : transitivity of "lying in a common circuit".
* `ConnIn M Y` : `Y` admits no nontrivial rank split.
* `exists_isCircuit_of_connIn` : two elements of a connected set lie in a common circuit
  contained in it.
* `tutte` : Tutte's theorem, in the form needed here.
-/

@[expose] public section

namespace SquareBasis

open Matroid Set

variable {α : Type*} {M : Matroid α} [M.Finite]

/-- `X` is a separator of `M`. -/
def Sep (M : Matroid α) (X : Set α) : Prop := X ⊆ M.E ∧ rk M X + rk M (M.E \ X) = rk M M.E

/-- Rank is additive across a separator. -/
theorem sep_split {X Y Z : Set α} (hX : Sep M X) (hY : Y ⊆ X) (hZ : Z ⊆ M.E \ X) :
    rk M (Y ∪ Z) = rk M Y + rk M Z := by
  have h1 := rk_submod M Y Z
  have hYZ : Y ∩ Z = ∅ := by
    ext x; simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hy hz; exact (hZ hz).2 (hY hy)
  rw [hYZ, rk_empty] at h1
  have h2 := rk_submod M (Y ∪ Z) X
  have e2 : (Y ∪ Z) ∩ X = Y := by
    ext x; simp only [mem_inter_iff, mem_union]
    constructor
    · rintro ⟨hx | hx, hxX⟩
      · exact hx
      · exact absurd hxX (hZ hx).2
    · intro hx; exact ⟨Or.inl hx, hY hx⟩
  have e2' : Y ∪ Z ∪ X = X ∪ Z := by
    ext x; simp only [mem_union]
    constructor
    · rintro ((hx | hx) | hx)
      · exact Or.inl (hY hx)
      · exact Or.inr hx
      · exact Or.inl hx
    · rintro (hx | hx)
      · exact Or.inr hx
      · exact Or.inl (Or.inr hx)
  rw [e2, e2'] at h2
  have h3 := rk_submod M (X ∪ Z) (M.E \ X)
  have e3 : (X ∪ Z) ∩ (M.E \ X) = Z := by
    ext x; simp only [mem_inter_iff, mem_union, mem_sdiff]
    constructor
    · rintro ⟨hx | hx, -, hxX⟩
      · exact absurd hx hxX
      · exact hx
    · intro hx; exact ⟨Or.inr hx, hZ hx⟩
  have e3' : X ∪ Z ∪ (M.E \ X) = M.E := by
    ext x; simp only [mem_union, mem_sdiff]
    constructor
    · rintro ((hx | hx) | hx)
      · exact hX.1 hx
      · exact (hZ hx).1
      · exact hx.1
    · intro hx
      by_cases hxX : x ∈ X
      · exact Or.inl (Or.inl hxX)
      · exact Or.inr ⟨hx, hxX⟩
  rw [e3, e3'] at h3
  have := hX.2
  linarith

/-- A circuit lies on one side of a separator. -/
theorem subset_or_subset_of_sep {X C : Set α} (hX : Sep M X) (hC : M.IsCircuit C) :
    C ⊆ X ∨ C ⊆ M.E \ X := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hi1 : M.Indep (C ∩ X) := hC.ssubset_indep
    (ssubset_of_subset_of_ne inter_subset_left (fun he => h1 (he ▸ inter_subset_right)))
  have hi2 : M.Indep (C \ X) := hC.ssubset_indep
    (ssubset_of_subset_of_ne sdiff_subset (fun he => h2 (fun x hx => by
      rw [← he] at hx; exact ⟨hC.subset_ground hx.1, hx.2⟩)))
  have hsplit := sep_split hX (inter_subset_right : C ∩ X ⊆ X)
    (fun x hx => ⟨hC.subset_ground hx.1, hx.2⟩ : C \ X ⊆ M.E \ X)
  rw [inter_union_sdiff, rk_indep hi1, rk_indep hi2] at hsplit
  have hfin : C.Finite := M.ground_finite.subset hC.subset_ground
  have hcard : (C ∩ X).ncard + (C \ X).ncard = C.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard C X hfin
  have := rk_circuit_add_one hC
  omega

/-- Separators of `M` are separators of `M✶`. -/
theorem sep_dual {X : Set α} (hX : Sep M X) : Sep M✶ X := by
  refine ⟨by simpa using hX.1, ?_⟩
  have hXE := hX.1
  have hfinE := M.ground_finite
  rw [dual_ground, rk_dual M hXE, rk_dual M sdiff_subset, rk_dual M subset_rfl,
    sdiff_sdiff_cancel_left hXE, sdiff_self]
  have h1 : X.ncard + (M.E \ X).ncard = M.E.ncard := by
    have := Set.ncard_sdiff_add_ncard_of_subset hXE hfinE; omega
  have := hX.2
  rw [rk_empty]
  linarith

/-- A subset of a separator that splits it is a separator. -/
theorem sep_of_split {C Z : Set α} (hC : Sep M C) (hZ : Z ⊆ C)
    (h : rk M Z + rk M (C \ Z) = rk M C) : Sep M Z := by
  refine ⟨hZ.trans hC.1, ?_⟩
  have e : M.E \ Z = (C \ Z) ∪ (M.E \ C) := by
    ext x; simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hx, hxZ⟩
      by_cases hxC : x ∈ C
      · exact Or.inl ⟨hxC, hxZ⟩
      · exact Or.inr ⟨hx, hxC⟩
    · rintro (⟨hx, hxZ⟩ | ⟨hx, hxC⟩)
      · exact ⟨hC.1 hx, hxZ⟩
      · exact ⟨hx, fun hz => hxC (hZ hz)⟩
  rw [e, sep_split hC sdiff_subset subset_rfl]
  have := hC.2
  linarith

/-! ### Transitivity of "lying in a common circuit" -/

/-- If two circuits meet, then any `a` in the first and `c ≠ a` in the second lie in a
common circuit contained in their union. -/
theorem exists_isCircuit_of_trans :
    ∀ (n : ℕ) {C₁ C₂ : Set α} {a c : α}, (C₁ ∪ C₂).ncard ≤ n → M.IsCircuit C₁ →
      M.IsCircuit C₂ → a ∈ C₁ → c ∈ C₂ → a ≠ c → (C₁ ∩ C₂).Nonempty →
      ∃ K, M.IsCircuit K ∧ K ⊆ C₁ ∪ C₂ ∧ a ∈ K ∧ c ∈ K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C₁ C₂ a c hn hC₁ hC₂ ha hc hac ⟨y, hy₁, hy₂⟩
  by_cases hcC₁ : c ∈ C₁
  · exact ⟨C₁, hC₁, subset_union_left, ha, hcC₁⟩
  by_cases haC₂ : a ∈ C₂
  · exact ⟨C₂, hC₂, subset_union_right, haC₂, hc⟩
  have hfin : (C₁ ∪ C₂).Finite :=
    M.ground_finite.subset (union_subset hC₁.subset_ground hC₂.subset_ground)
  -- eliminate `y`, keeping `a`
  obtain ⟨C₃, hC₃s, hC₃, haC₃⟩ := hC₁.strong_elimination hC₂ hy₁ hy₂ ha haC₂
  by_cases hcC₃ : c ∈ C₃
  · exact ⟨C₃, hC₃, hC₃s.trans sdiff_subset, haC₃, hcC₃⟩
  -- eliminate `y`, keeping `c`
  obtain ⟨C₄, hC₄s, hC₄, hcC₄⟩ := hC₂.strong_elimination hC₁ hy₂ hy₁ hc hcC₁
  by_cases haC₄ : a ∈ C₄
  · refine ⟨C₄, hC₄, hC₄s.trans ?_, haC₄, hcC₄⟩
    rw [union_comm]; exact sdiff_subset
  have hyC₃ : y ∉ C₃ := fun h => (hC₃s h).2 rfl
  have hyC₄ : y ∉ C₄ := fun h => (hC₄s h).2 rfl
  -- `C₃` meets `C₂ \ C₁`
  have hC₃C₁ : ¬ C₃ ⊆ C₁ := by
    intro hsub
    have := hC₃.eq_of_subset_isCircuit hC₁ hsub
    exact hyC₃ (this ▸ hy₁)
  obtain ⟨w, hwC₃, hwC₁⟩ := not_subset.1 hC₃C₁
  have hwC₂ : w ∈ C₂ := by
    rcases (hC₃s hwC₃).1 with h | h
    · exact absurd h hwC₁
    · exact h
  have hC₄C₂ : ¬ C₄ ⊆ C₂ := by
    intro hsub
    have := hC₄.eq_of_subset_isCircuit hC₂ hsub
    exact hyC₄ (this ▸ hy₂)
  obtain ⟨w', hw'C₄, hw'C₂⟩ := not_subset.1 hC₄C₂
  have hw'C₁ : w' ∈ C₁ := by
    rcases (hC₄s hw'C₄).1 with h | h
    · exact absurd h hw'C₂
    · exact h
  have hC₃sub : C₃ ⊆ C₁ ∪ C₂ := hC₃s.trans sdiff_subset
  have hC₄sub : C₄ ⊆ C₁ ∪ C₂ := hC₄s.trans (by rw [union_comm]; exact sdiff_subset)
  -- Case 1: `C₃ ∪ C₂` is smaller.
  by_cases h₁ : (C₃ ∪ C₂).ncard < (C₁ ∪ C₂).ncard
  · obtain ⟨K, hK, hKs, haK, hcK⟩ := ih _ (lt_of_lt_of_le h₁ hn) le_rfl hC₃ hC₂ haC₃ hc hac
      ⟨w, hwC₃, hwC₂⟩
    exact ⟨K, hK, hKs.trans (union_subset hC₃sub subset_union_right), haK, hcK⟩
  -- Case 2: `C₁ ∪ C₄` is smaller.
  by_cases h₂ : (C₁ ∪ C₄).ncard < (C₁ ∪ C₂).ncard
  · obtain ⟨K, hK, hKs, haK, hcK⟩ := ih _ (lt_of_lt_of_le h₂ hn) le_rfl hC₁ hC₄ ha hcC₄ hac
      ⟨w', hw'C₁, hw'C₄⟩
    exact ⟨K, hK, hKs.trans (union_subset subset_union_left hC₄sub), haK, hcK⟩
  -- Otherwise `C₁ \ C₂ ⊆ C₃` and `C₂ \ C₁ ⊆ C₄`, and `C₃ ∪ C₄` misses `y`.
  push Not at h₁ h₂
  have e₁ : C₃ ∪ C₂ = C₁ ∪ C₂ := Set.eq_of_subset_of_ncard_le
    (union_subset hC₃sub subset_union_right) h₁ hfin
  have e₂ : C₁ ∪ C₄ = C₁ ∪ C₂ := Set.eq_of_subset_of_ncard_le
    (union_subset subset_union_left hC₄sub) h₂ hfin
  have hw'C₃ : w' ∈ C₃ := by
    have : w' ∈ C₃ ∪ C₂ := e₁ ▸ (Or.inl hw'C₁ : w' ∈ C₁ ∪ C₂)
    rcases this with h | h
    · exact h
    · exact absurd h hw'C₂
  have h₃ : (C₃ ∪ C₄).ncard < (C₁ ∪ C₂).ncard := by
    apply Set.ncard_lt_ncard _ hfin
    refine ssubset_of_subset_of_ne (union_subset hC₃sub hC₄sub) ?_
    intro he
    have : y ∈ C₃ ∪ C₄ := he ▸ (Or.inl hy₁ : y ∈ C₁ ∪ C₂)
    rcases this with h | h
    · exact hyC₃ h
    · exact hyC₄ h
  obtain ⟨K, hK, hKs, haK, hcK⟩ := ih _ (lt_of_lt_of_le h₃ hn) le_rfl hC₃ hC₄ haC₃ hcC₄ hac
    ⟨w', hw'C₃, hw'C₄⟩
  exact ⟨K, hK, hKs.trans (union_subset hC₃sub hC₄sub), haK, hcK⟩

/-! ### Connected sets -/

/-- `Y` is connected in `M`: it has no nontrivial rank split. -/
def ConnIn (M : Matroid α) (Y : Set α) : Prop :=
  ∀ Z ⊆ Y, rk M Z + rk M (Y \ Z) = rk M Y → Z = ∅ ∨ Z = Y

/-- The elements of `Y` that lie in a common circuit with `x` inside `Y` (and `x` itself). -/
def circuitClass (M : Matroid α) (Y : Set α) (x : α) : Set α :=
  {z | z ∈ Y ∧ (z = x ∨ ∃ K, M.IsCircuit K ∧ K ⊆ Y ∧ x ∈ K ∧ z ∈ K)}

/-- The circuit class of `x` in `Y` splits the rank of `Y`. -/
theorem circuitClass_split {Y : Set α} {x : α} (hx : x ∈ Y) :
    rk M (circuitClass M Y x) + rk M (Y \ circuitClass M Y x) = rk M Y := by
  classical
  set X := circuitClass M Y x with hXdef
  have hXY : X ⊆ Y := fun z hz => hz.1
  have hxX : x ∈ X := ⟨hx, Or.inl rfl⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ⟩ := M.exists_isBasis' (Y \ X)
  have hIJ : M.Indep (I ∪ J) := by
    by_contra hdep
    have hdep' : M.Dep (I ∪ J) := ⟨hdep, union_subset hI.indep.subset_ground
      hJ.indep.subset_ground⟩
    obtain ⟨K, hKs, hK⟩ := hdep'.exists_isCircuit_subset
    have hKI : ¬ K ⊆ I := fun h => hK.dep.not_indep (hI.indep.subset h)
    have hKJ : ¬ K ⊆ J := fun h => hK.dep.not_indep (hJ.indep.subset h)
    obtain ⟨b, hbK, hbI⟩ := not_subset.1 hKI
    obtain ⟨a, haK, haJ⟩ := not_subset.1 hKJ
    have haI : a ∈ I := by
      rcases hKs haK with h | h
      · exact h
      · exact absurd h haJ
    have hbJ : b ∈ J := by
      rcases hKs hbK with h | h
      · exact absurd h hbI
      · exact h
    have haX : a ∈ X := hI.subset haI
    have hbX : b ∈ Y \ X := hJ.subset hbJ
    have hKY : K ⊆ Y := hKs.trans (union_subset (hI.subset.trans hXY)
      (hJ.subset.trans sdiff_subset))
    apply hbX.2
    refine ⟨hbX.1, Or.inr ?_⟩
    rcases haX.2 with rfl | ⟨Ka, hKa, hKaY, hxKa, haKa⟩
    · exact ⟨K, hK, hKY, haK, hbK⟩
    · have hxb : a ≠ b ∨ True := Or.inr trivial
      have hxb' : x ≠ b := fun h => hbX.2 (h ▸ hxX)
      obtain ⟨K', hK', hK's, hxK', hbK'⟩ := exists_isCircuit_of_trans _ le_rfl hKa hK
        hxKa hbK hxb' ⟨a, haKa, haK⟩
      exact ⟨K', hK', hK's.trans (union_subset hKaY hKY), hxK', hbK'⟩
  have hdisj : Disjoint I J := by
    rw [Set.disjoint_left]
    intro z hzI hzJ
    exact (hJ.subset hzJ).2 (hI.subset hzI)
  have hle : rk M X + rk M (Y \ X) ≤ rk M Y := by
    rw [rk_isBasis' hI, rk_isBasis' hJ]
    have h1 := ncard_le_rk_of_indep hIJ (union_subset (hI.subset.trans hXY)
      (hJ.subset.trans sdiff_subset))
    have hIfin : I.Finite := M.ground_finite.subset hI.indep.subset_ground
    have hJfin : J.Finite := M.ground_finite.subset hJ.indep.subset_ground
    rw [Set.ncard_union_eq hdisj hIfin hJfin] at h1
    push_cast at h1
    exact h1
  have hge : rk M Y ≤ rk M X + rk M (Y \ X) := by
    have := rk_union_le M X (Y \ X)
    rwa [union_sdiff_cancel hXY] at this
  exact le_antisymm hle hge

/-- Two distinct elements of a connected set lie in a common circuit contained in it. -/
theorem exists_isCircuit_of_connIn {Y : Set α} (hY : ConnIn M Y) {x y : α}
    (hx : x ∈ Y) (hy : y ∈ Y) (hxy : x ≠ y) :
    ∃ K, M.IsCircuit K ∧ K ⊆ Y ∧ x ∈ K ∧ y ∈ K := by
  have hXY : circuitClass M Y x ⊆ Y := fun z hz => hz.1
  have hxX : x ∈ circuitClass M Y x := ⟨hx, Or.inl rfl⟩
  rcases hY _ hXY (circuitClass_split hx) with h | h
  · exact absurd (h ▸ hxX) (notMem_empty x)
  · have hyX : y ∈ circuitClass M Y x := by rw [h]; exact hy
    rcases hyX.2 with h' | h'
    · exact absurd h'.symm hxy
    · exact h'

/-- A minimal nonempty separator is connected. -/
theorem connIn_of_minimal {C : Set α} (hC : Sep M C)
    (hmin : ∀ Z, Sep M Z → Z.Nonempty → C.ncard ≤ Z.ncard) : ConnIn M C := by
  intro Z hZC hsplit
  have hZ := sep_of_split hC hZC hsplit
  rcases Z.eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · right
    exact Set.eq_of_subset_of_ncard_le hZC (hmin Z hZ h)
      (M.ground_finite.subset hC.1)

/-! ### Tutte's theorem -/

/-- Rank in the dual inside a separator `C`: for `Z ⊆ C`,
`r*(Z) = |Z| + r(C \ Z) - r(C)`. -/
theorem rk_dual_of_sep {C Z : Set α} (hC : Sep M C) (hZ : Z ⊆ C) :
    rk M✶ Z = Z.ncard + rk M (C \ Z) - rk M C := by
  rw [rk_dual M (hZ.trans hC.1)]
  have e : M.E \ Z = (C \ Z) ∪ (M.E \ C) := by
    ext x; simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hx, hxZ⟩
      by_cases hxC : x ∈ C
      · exact Or.inl ⟨hxC, hxZ⟩
      · exact Or.inr ⟨hx, hxC⟩
    · rintro (⟨hx, hxZ⟩ | ⟨hx, hxC⟩)
      · exact ⟨hC.1 hx, hxZ⟩
      · exact ⟨hx, fun hz => hxC (hZ hz)⟩
  rw [e, sep_split hC sdiff_subset subset_rfl]
  have := hC.2
  linarith

/-- Facts about an element of a connected separator with at least two elements. -/
theorem rk_facts_of_connIn {C : Set α} {v : α} (hconn : ConnIn M C)
    (hv : v ∈ C) (hne : (C \ {v}).Nonempty) :
    rk M {v} = 1 ∧ rk M (C \ {v}) = rk M C := by
  have hsub : rk M C ≤ rk M {v} + rk M (C \ {v}) := by
    have := rk_union_le M {v} (C \ {v})
    rwa [union_sdiff_cancel (singleton_subset_iff.2 hv)] at this
  have hmono : rk M (C \ {v}) ≤ rk M C := rk_mono M sdiff_subset
  have hle1 := rk_singleton_le M v
  have hnot : ¬ (rk M {v} + rk M (C \ {v}) = rk M C) := by
    intro h
    rcases hconn {v} (singleton_subset_iff.2 hv) h with h' | h'
    · exact (singleton_nonempty v).ne_empty h'
    · obtain ⟨w, hw⟩ := hne
      rw [← h'] at hw
      exact hw.2 hw.1
  have hmono' : rk M {v} ≤ rk M C := rk_mono M (singleton_subset_iff.2 hv)
  have h0 := rk_nonneg M {v}
  constructor
  · by_contra h1
    have : rk M {v} = 0 := by omega
    have : rk M (C \ {v}) = rk M C := by linarith
    exact hnot (by omega)
  · by_contra h1
    exact hnot (by omega)

/-- **Tutte's theorem** (in the form used here). Let `C` be a connected separator of `M`
with at least two elements and let `v ∈ C`. Then `C \ {v}` is connected in `M` or in `M✶`. -/
theorem tutte {C : Set α} {v : α} (hC : Sep M C) (hconn : ConnIn M C) (hv : v ∈ C)
    (hne : (C \ {v}).Nonempty) : ConnIn M (C \ {v}) ∨ ConnIn M✶ (C \ {v}) := by
  classical
  obtain ⟨hrv, hrC⟩ := rk_facts_of_connIn hconn hv hne
  set Y := C \ {v} with hYdef
  have hYC : Y ⊆ C := sdiff_subset
  have hvY : v ∉ Y := fun h => h.2 rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [ConnIn, not_forall, not_or] at h1 h2
  obtain ⟨Z₁, hZ₁Y, hs₁, hZ₁e, hZ₁Y'⟩ := h1
  obtain ⟨Z₂, hZ₂Y, hs₂, hZ₂e, hZ₂Y'⟩ := h2
  set W₁ := Y \ Z₁ with hW₁def
  set W₂ := Y \ Z₂ with hW₂def
  -- The dual split, expressed in `M`.
  have hs₂' : rk M (insert v Z₂) + rk M (insert v W₂) = rk M C + 1 := by
    rw [rk_dual_of_sep hC (hZ₂Y.trans hYC), rk_dual_of_sep hC (sdiff_subset.trans hYC),
      rk_dual_of_sep hC hYC] at hs₂
    have eA : C \ Z₂ = insert v W₂ := by
      ext x
      have h1 := @hZ₂Y x
      simp only [hW₂def, hYdef, mem_sdiff, mem_insert_iff, mem_singleton_iff] at h1 ⊢
      by_cases hxv : x = v
      · subst hxv; tauto
      · tauto
    have eB : C \ W₂ = insert v Z₂ := by
      ext x
      have h1 := @hZ₂Y x
      simp only [hW₂def, hYdef, mem_sdiff, mem_insert_iff, mem_singleton_iff] at h1 ⊢
      by_cases hxv : x = v
      · subst hxv; tauto
      · tauto
    have eC : C \ Y = {v} := by
      ext x
      simp only [hYdef, mem_sdiff, mem_singleton_iff]
      by_cases hxv : x = v
      · subst hxv; tauto
      · tauto
    rw [eA, eB, eC, hrv] at hs₂
    have hY_card : Z₂.ncard + W₂.ncard = Y.ncard := by
      have := Set.ncard_sdiff_add_ncard_of_subset hZ₂Y (M.ground_finite.subset (hYC.trans hC.1))
      rw [hW₂def]; omega
    have : (Z₂.ncard : ℤ) + W₂.ncard = Y.ncard := by exact_mod_cast hY_card
    linarith
  have hlam : ∀ U ⊆ Y, 0 ≤ rk M U + rk M (C \ U) - rk M C := by
    intro U hU
    have := rk_union_le M U (C \ U)
    rw [union_sdiff_cancel (hU.trans hYC)] at this
    linarith
  have hzero : ∀ U ⊆ Y, rk M U + rk M (C \ U) - rk M C = 0 → U = ∅ := by
    intro U hU h0
    rcases hconn U (hU.trans hYC) (by linarith) with h | h
    · exact h
    · exact absurd (h ▸ hU : C ⊆ Y) (fun hh => hvY (hh hv))
  -- Two applications of submodularity.
  have key : ∀ (A₁ B₁ A₂ B₂ : Set α), A₁ ⊆ Y → B₁ = Y \ A₁ → A₂ ⊆ Y → B₂ = Y \ A₂ →
      rk M A₁ + rk M B₁ = rk M C →
      rk M (insert v A₂) + rk M (insert v B₂) = rk M C + 1 →
      (rk M (A₁ ∩ A₂) + rk M (C \ (A₁ ∩ A₂)) - rk M C) +
        (rk M (B₁ ∩ B₂) + rk M (C \ (B₁ ∩ B₂)) - rk M C) ≤ 1 := by
    intro A₁ B₁ A₂ B₂ hA₁ hB₁ hA₂ hB₂ hs hs'
    have i1 := rk_submod M A₁ (insert v A₂)
    have i2 := rk_submod M B₁ (insert v B₂)
    have eA : A₁ ∩ insert v A₂ = A₁ ∩ A₂ := by
      ext x; simp only [mem_inter_iff, mem_insert_iff]
      constructor
      · rintro ⟨hx, rfl | hx'⟩
        · exact absurd (hA₁ hx) hvY
        · exact ⟨hx, hx'⟩
      · rintro ⟨hx, hx'⟩; exact ⟨hx, Or.inr hx'⟩
    have eB : B₁ ∩ insert v B₂ = B₁ ∩ B₂ := by
      ext x; simp only [mem_inter_iff, mem_insert_iff]
      constructor
      · rintro ⟨hx, rfl | hx'⟩
        · exact absurd (hB₁ ▸ hx : x ∈ Y \ A₁).1 hvY
        · exact ⟨hx, hx'⟩
      · rintro ⟨hx, hx'⟩; exact ⟨hx, Or.inr hx'⟩
    have eA' : C \ (B₁ ∩ B₂) = A₁ ∪ insert v A₂ := by
      subst hB₁ hB₂
      ext x
      have h1 := @hA₁ x
      have h2 := @hA₂ x
      simp only [hYdef, mem_sdiff, mem_inter_iff, mem_union, mem_insert_iff,
        mem_singleton_iff] at h1 h2 ⊢
      by_cases hxv : x = v
      · subst hxv; tauto
      · tauto
    have eB' : C \ (A₁ ∩ A₂) = B₁ ∪ insert v B₂ := by
      subst hB₁ hB₂
      ext x
      have h1 := @hA₁ x
      have h2 := @hA₂ x
      simp only [hYdef, mem_sdiff, mem_inter_iff, mem_union, mem_insert_iff,
        mem_singleton_iff] at h1 h2 ⊢
      by_cases hxv : x = v
      · subst hxv; tauto
      · tauto
    rw [eA] at i1
    rw [eB] at i2
    rw [eA', eB']
    have u1 : A₁ ∪ insert v A₂ = insert v (A₁ ∪ A₂) := by
      ext x; simp only [mem_union, mem_insert_iff]; tauto
    have u2 : B₁ ∪ insert v B₂ = insert v (B₁ ∪ B₂) := by
      ext x; simp only [mem_union, mem_insert_iff]; tauto
    rw [u1] at i1 ⊢
    rw [u2] at i2 ⊢
    linarith
  have hW₁ : W₁ ⊆ Y := sdiff_subset
  have hW₂ : W₂ ⊆ Y := sdiff_subset
  have hs₁' : rk M Z₁ + rk M W₁ = rk M C := by rw [hs₁, hrC]
  have k1 := key Z₁ W₁ Z₂ W₂ hZ₁Y rfl hZ₂Y rfl hs₁' hs₂'
  have hW₂' : Y \ W₂ = Z₂ := sdiff_sdiff_cancel_left hZ₂Y
  have hs₂'' : rk M (insert v W₂) + rk M (insert v (Y \ W₂)) = rk M C + 1 := by
    rw [hW₂']; linarith
  have k2 := key Z₁ W₁ W₂ (Y \ W₂) hZ₁Y rfl hW₂ rfl hs₁' hs₂''
  rw [hW₂'] at k2
  have l1 := hlam (Z₁ ∩ Z₂) (inter_subset_left.trans hZ₁Y)
  have l2 := hlam (W₁ ∩ W₂) (inter_subset_left.trans hW₁)
  have l3 := hlam (Z₁ ∩ W₂) (inter_subset_left.trans hZ₁Y)
  have l4 := hlam (W₁ ∩ Z₂) (inter_subset_left.trans hW₁)
  have c1 : Z₁ ∩ Z₂ = ∅ ∨ W₁ ∩ W₂ = ∅ := by
    by_cases h : rk M (Z₁ ∩ Z₂) + rk M (C \ (Z₁ ∩ Z₂)) - rk M C = 0
    · exact Or.inl (hzero _ (inter_subset_left.trans hZ₁Y) h)
    · exact Or.inr (hzero _ (inter_subset_left.trans hW₁) (by omega))
  have c2 : Z₁ ∩ W₂ = ∅ ∨ W₁ ∩ Z₂ = ∅ := by
    by_cases h : rk M (Z₁ ∩ W₂) + rk M (C \ (Z₁ ∩ W₂)) - rk M C = 0
    · exact Or.inl (hzero _ (inter_subset_left.trans hZ₁Y) h)
    · exact Or.inr (hzero _ (inter_subset_left.trans hW₁) (by omega))
  -- Each case empties one of the four parts.
  have hW₁ne : W₁.Nonempty := by
    rw [← ne_empty_iff_nonempty]; intro h
    exact hZ₁Y' (subset_antisymm hZ₁Y (sdiff_eq_empty.1 h))
  have hW₂ne : W₂.Nonempty := by
    rw [← ne_empty_iff_nonempty]; intro h
    exact hZ₂Y' (subset_antisymm hZ₂Y (sdiff_eq_empty.1 h))
  have part : ∀ {A B : Set α}, A ⊆ Y → (A ∩ B = ∅) → (A ∩ (Y \ B) = ∅) → A = ∅ := by
    intro A B hA h1 h2
    ext x; simp only [mem_empty_iff_false, iff_false]
    intro hx
    by_cases hxB : x ∈ B
    · exact (h1 ▸ (⟨hx, hxB⟩ : x ∈ A ∩ B) : x ∈ (∅ : Set α))
    · exact (h2 ▸ (⟨hx, hA hx, hxB⟩ : x ∈ A ∩ (Y \ B)) : x ∈ (∅ : Set α))
  rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2
  · exact hZ₁e (part hZ₁Y c1 c2)
  · -- `Z₁ ∩ Z₂ = ∅` and `W₁ ∩ Z₂ = ∅` empty `Z₂`.
    apply hZ₂e
    have := part hZ₂Y (B := Z₁) (by rw [inter_comm]; exact c1) (by rw [inter_comm]; exact c2)
    exact this
  · -- `W₁ ∩ W₂ = ∅` and `Z₁ ∩ W₂ = ∅` empty `W₂`.
    obtain ⟨x, hx⟩ := hW₂ne
    have := part hW₂ (B := Z₁) (by rw [inter_comm]; exact c2) (by rw [inter_comm]; exact c1)
    rw [this] at hx; exact hx
  · obtain ⟨x, hx⟩ := hW₁ne
    have := part hW₁ (B := Z₂) (by exact c2) (by exact c1)
    rw [this] at hx; exact hx

end SquareBasis
