module

public import SquareBasis.Section6
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi

/-!
# Figure 1 of the paper (`U_{2,4}`)

The caption of Figure 1 states: up to sign, the three equatorial squares
`z₁ = e₁₃ - e₁₄ + e₂₄ - e₂₃`, `z₂ = e₁₂ - e₁₄ + e₃₄ - e₂₃`, `z₃ = e₁₂ - e₁₃ + e₃₄ - e₂₄`
are exactly the squares of `U_{2,4}`; `rank ker_ℤ = 6 - 4 = 2`; `z₁ = z₂ - z₃`; and any two of
the three squares form a `ℤ`-basis of `ker_ℤ A_{U_{2,4}}` (`figure1`). Paper indices are shifted
down by one here.

The classification of all squares is reduced, through the injective coordinate map `ev`, to a
finite check on explicit integer vectors indexed by `Finset (Fin 4)` (`decide`).
-/

@[expose] public section

namespace SquareBasis

open Finset Module Matrix

/-- `e_X` in `ℤ^{𝓑(U_{2,4})}`. -/
noncomputable abbrev e4 (X : Finset (Fin 4)) : Bases (unif 2 4) →₀ ℤ := eF 2 X

/-- `z_{i,j;{b},{b'}}` in `U_{2,4}`. -/
noncomputable def z4 (i j b b' : Fin 4) : Bases (unif 2 4) →₀ ℤ :=
  e4 {i, b} - e4 {j, b} - e4 {i, b'} + e4 {j, b'}

/-- `z₁ = e₁₃ - e₁₄ - e₂₃ + e₂₄` (paper indices). -/
noncomputable def fz1 : Bases (unif 2 4) →₀ ℤ := z4 2 3 0 1
/-- `z₂ = e₁₂ - e₁₄ - e₂₃ + e₃₄` (paper indices). -/
noncomputable def fz2 : Bases (unif 2 4) →₀ ℤ := z4 1 3 0 2
/-- `z₃ = e₁₂ - e₁₃ - e₂₄ + e₃₄` (paper indices). -/
noncomputable def fz3 : Bases (unif 2 4) →₀ ℤ := z4 1 2 0 3

theorem base4_pair {x y : Fin 4} (h : x ≠ y) : (unif 2 4).IsBase (insert x {y} : Set (Fin 4)) := by
  have := (unif_isBase_coe_iff (by norm_num : 2 ≤ 4)).2 (card_pair h)
  simpa using this

theorem e4_pair {x y : Fin 4} (h : x ≠ y) :
    e4 {x, y} = Finsupp.single ⟨insert x {y}, base4_pair h⟩ 1 := by
  rw [e4, eF_of_card 2 (by norm_num) (card_pair h)]
  exact congrArg (fun t => Finsupp.single t (1 : ℤ)) (Subtype.ext (by simp))

theorem z4_isSquare {i j b b' : Fin 4} (hij : i ≠ j) (hbb : b ≠ b') (h1 : i ≠ b) (h2 : j ≠ b)
    (h3 : i ≠ b') (h4 : j ≠ b') : IsSquare (unif 2 4) (z4 i j b b') := by
  refine ⟨i, j, {b}, {b'}, base4_pair h1, base4_pair h2, base4_pair h3, base4_pair h4, hij,
    by simpa using hbb, by simpa using h1, by simpa using h2, by simpa using h3,
    by simpa using h4, ?_⟩
  rw [z4, e4_pair h1, e4_pair h2, e4_pair h3, e4_pair h4]

/-! ### Coordinates -/

/-- `[X = Y]`. -/
def ind4 (X Y : Finset (Fin 4)) : ℤ := if X = Y then 1 else 0

/-- The coordinate vector of `z_{i,j;{b},{b'}}`. -/
def v4 (i j b b' : Fin 4) : Finset (Fin 4) → ℤ := fun X =>
  ind4 X {i, b} - ind4 X {j, b} - ind4 X {i, b'} + ind4 X {j, b'}

/-- The coordinates of `v ∈ ℤ^𝓑`, indexed by `2`-subsets of `[4]` (and `0` elsewhere). -/
noncomputable def ev (v : Bases (unif 2 4) →₀ ℤ) : Finset (Fin 4) → ℤ :=
  fun X => if h : X.card = 2 then v (toBase 2 (by norm_num) X h) else 0

theorem ev_add (v w : Bases (unif 2 4) →₀ ℤ) : ev (v + w) = ev v + ev w := by
  funext X; simp only [ev, Pi.add_apply]; split_ifs <;> simp

theorem ev_sub (v w : Bases (unif 2 4) →₀ ℤ) : ev (v - w) = ev v - ev w := by
  funext X; simp only [ev, Pi.sub_apply]; split_ifs <;> simp

theorem ev_neg (v : Bases (unif 2 4) →₀ ℤ) : ev (-v) = -ev v := by
  funext X; simp only [ev, Pi.neg_apply]; split_ifs <;> simp

theorem ev_injective : Function.Injective ev := by
  intro v w h
  ext t
  have hcoe : ((finsetOf 2 t : Finset (Fin 4)) : Set (Fin 4)) = t.1 := by
    ext x; simp [finsetOf]
  have hc : (finsetOf 2 t).card = 2 := by
    have := (unif_isBase_iff (by norm_num : 2 ≤ 4)).1 t.2
    rwa [← hcoe, Set.ncard_coe_finset] at this
  have ht : toBase 2 (by norm_num) (finsetOf 2 t) hc = t := Subtype.ext hcoe
  have := congrFun h (finsetOf 2 t)
  simp only [ev, hc, dite_true, ht] at this
  exact this

theorem ev_e4 {Y : Finset (Fin 4)} (hY : Y.card = 2) : ev (e4 Y) = fun X => ind4 X Y := by
  funext X
  by_cases hX : X.card = 2
  · simp only [ev, hX, dite_true, e4, eF_apply 2 (by norm_num) hY, ind4]
    by_cases hXY : X = Y
    · subst hXY; simp
    · rw [ite_eq_right_iff.2 (fun h => absurd (toBase_injective 2 _ hX hY h) hXY),
        ite_eq_right_iff.2 (fun h => absurd h hXY)]
  · simp only [ev, hX, dite_false, ind4]
    rw [ite_eq_right_iff.2 (fun (h : X = Y) => absurd (by rw [h]; exact hY) hX)]

theorem ev_z4 {i j b b' : Fin 4} (h1 : i ≠ b) (h2 : j ≠ b) (h3 : i ≠ b') (h4 : j ≠ b') :
    ev (z4 i j b b') = v4 i j b b' := by
  rw [z4, ev_add, ev_sub, ev_sub, ev_e4 (card_pair h1), ev_e4 (card_pair h2),
    ev_e4 (card_pair h3), ev_e4 (card_pair h4)]
  rfl

theorem ev_fz1 : ev fz1 = v4 2 3 0 1 := ev_z4 (by decide) (by decide) (by decide) (by decide)
theorem ev_fz2 : ev fz2 = v4 1 3 0 2 := ev_z4 (by decide) (by decide) (by decide) (by decide)
theorem ev_fz3 : ev fz3 = v4 1 2 0 3 := ev_z4 (by decide) (by decide) (by decide) (by decide)

/-- The finite check behind the classification. -/
theorem v4_classify : ∀ i j b b' : Fin 4, i ≠ j → b ≠ b' → i ≠ b → j ≠ b → i ≠ b' → j ≠ b' →
    v4 i j b b' = v4 2 3 0 1 ∨ v4 i j b b' = -v4 2 3 0 1 ∨ v4 i j b b' = v4 1 3 0 2 ∨
    v4 i j b b' = -v4 1 3 0 2 ∨ v4 i j b b' = v4 1 2 0 3 ∨ v4 i j b b' = -v4 1 2 0 3 := by
  decide

/-! ### The claims of Figure 1 -/

theorem figure1_squares : IsSquare (unif 2 4) fz1 ∧ IsSquare (unif 2 4) fz2 ∧
    IsSquare (unif 2 4) fz3 :=
  ⟨z4_isSquare (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    z4_isSquare (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    z4_isSquare (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-- Up to sign, `z₁, z₂, z₃` are all the squares of `U_{2,4}`. -/
theorem figure1_classify {z : Bases (unif 2 4) →₀ ℤ} (hz : IsSquare (unif 2 4) z) :
    z = fz1 ∨ z = -fz1 ∨ z = fz2 ∨ z = -fz2 ∨ z = fz3 ∨ z = -fz3 := by
  obtain ⟨i, j, B, B', h₁, h₂, h₃, h₄, hij, hBB', hiB, hjB, hiB', hjB', rfl⟩ := hz
  have sing : ∀ {a : Fin 4} {C : Set (Fin 4)}, a ∉ C → (unif 2 4).IsBase (insert a C) →
      ∃ c, C = {c} := by
    intro a C ha h
    rw [unif_isBase_iff (by norm_num), Set.ncard_insert_of_notMem ha (Set.toFinite _)] at h
    exact Set.ncard_eq_one.1 (by omega)
  obtain ⟨b, rfl⟩ := sing hiB h₁
  obtain ⟨b', rfl⟩ := sing hiB' h₃
  simp only [Set.mem_singleton_iff] at hiB hjB hiB' hjB'
  have hbb : b ≠ b' := fun h => hBB' (by rw [h])
  have hz : Finsupp.single ⟨_, h₁⟩ 1 - Finsupp.single ⟨_, h₂⟩ 1 - Finsupp.single ⟨_, h₃⟩ 1 +
      Finsupp.single ⟨_, h₄⟩ 1 = z4 i j b b' := by
    rw [z4, e4_pair hiB, e4_pair hjB, e4_pair hiB', e4_pair hjB']
  rw [hz]
  have he := ev_z4 hiB hjB hiB' hjB'
  rcases v4_classify i j b b' hij hbb hiB hjB hiB' hjB' with h | h | h | h | h | h
  · left; exact ev_injective (by rw [he, h, ev_fz1])
  · right; left; exact ev_injective (by rw [he, h, ev_neg, ev_fz1])
  · right; right; left; exact ev_injective (by rw [he, h, ev_fz2])
  · right; right; right; left; exact ev_injective (by rw [he, h, ev_neg, ev_fz2])
  · right; right; right; right; left; exact ev_injective (by rw [he, h, ev_fz3])
  · right; right; right; right; right; exact ev_injective (by rw [he, h, ev_neg, ev_fz3])

theorem figure1_rel : fz1 = fz2 - fz3 :=
  ev_injective (by rw [ev_sub, ev_fz1, ev_fz2, ev_fz3]; decide)

theorem figure1_rank : finrank ℤ (LinearMap.ker (incidence (unif 2 4))) = 2 := by
  have h := rank_nullity (unif 2 4)
  rw [(prop62 2 (by norm_num) (by norm_num : 2 < 4)).1, card_bases_unif 2 (by norm_num)] at h
  have : (univ.powersetCard 2 : Finset (Finset (Fin 4))).card = 6 := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]; rfl
  omega

/-- The sets `s ∈ S` for `U_{2,4}`. -/
def sv4 : Fin 2 → Finset (Fin 4) := ![{1, 3}, {2, 3}]

/-- **Example 6.3**, last claim: `r_{24} = z₁` and `r_{34} = z₂` (paper indices). -/
theorem example63_z : rS 2 (by norm_num : 2 < 4) {1, 3} = fz1 ∧
    rS 2 (by norm_num : 2 < 4) {2, 3} = fz2 := by
  obtain ⟨-, -, h1, h2⟩ := example63
  have e1 : rS 2 (by norm_num : 2 < 4) {1, 3} = fz1 := by
    rw [h1]; apply ev_injective
    rw [ev_add, ev_sub, ev_sub, ev_e4 (by decide), ev_e4 (by decide), ev_e4 (by decide),
      ev_e4 (by decide), ev_fz1]; decide
  have e2 : rS 2 (by norm_num : 2 < 4) {2, 3} = fz2 := by
    rw [h2]; apply ev_injective
    rw [ev_add, ev_sub, ev_sub, ev_e4 (by decide), ev_e4 (by decide), ev_e4 (by decide),
      ev_e4 (by decide), ev_fz2]; decide
  exact ⟨e1, e2⟩

/-- `z₁, z₂` are the basis `r_s` (`s ∈ S`) of Proposition 6.2 (Example 6.3). -/
theorem figure1_basis12 : LinearIndependent ℤ ![fz1, fz2] ∧
    Submodule.span ℤ ({fz1, fz2} : Set _) = LinearMap.ker (incidence (unif 2 4)) := by
  have hk : 2 < 4 := by norm_num
  obtain ⟨-, hS, -, -⟩ := example63
  obtain ⟨e1, e2⟩ := example63_z
  obtain ⟨-, -, -, hli, hspan⟩ := prop62 2 (by norm_num) hk
  refine ⟨?_, ?_⟩
  · let f : Fin 2 → Sset 2 hk := fun a => ⟨sv4 a, by rw [hS]; fin_cases a <;> simp [sv4]⟩
    have hf : Function.Injective f := by
      intro a b h
      have h' : sv4 a = sv4 b := congrArg Subtype.val h
      clear h
      revert a b
      decide
    have := hli.comp f hf
    convert this using 1
    funext a
    fin_cases a
    · exact e1.symm
    · exact e2.symm
  · rw [← hspan, hS]
    simp [Set.image_insert_eq, e1, e2]

theorem basis_pair_sub {G : Type*} [AddCommGroup G] {x y : G} {L : Submodule ℤ G}
    (hli : LinearIndependent ℤ ![x, y]) (hspan : Submodule.span ℤ ({x, y} : Set G) = L) :
    (LinearIndependent ℤ ![x, y - x] ∧ Submodule.span ℤ ({x, y - x} : Set G) = L) ∧
    (LinearIndependent ℤ ![y, y - x] ∧ Submodule.span ℤ ({y, y - x} : Set G) = L) := by
  rw [LinearIndependent.pair_iff] at hli
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [LinearIndependent.pair_iff]
    intro s t h
    have := hli (s - t) t (by rw [← h, sub_smul, smul_sub]; abel)
    omega
  · rw [← hspan]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact Submodule.subset_span (by simp)
      · exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact Submodule.subset_span (by simp)
      · rw [SetLike.mem_coe, Submodule.mem_span_pair]; exact ⟨1, 1, by simp⟩
  · rw [LinearIndependent.pair_iff]
    intro s t h
    have := hli (-t) (s + t) (by rw [← h, add_smul, smul_sub, neg_smul]; abel)
    omega
  · rw [← hspan]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact Submodule.subset_span (by simp)
      · exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · rw [SetLike.mem_coe, Submodule.mem_span_pair]; exact ⟨1, -1, by simp⟩
      · exact Submodule.subset_span (by simp)

/-- **Figure 1.** -/
theorem figure1 :
    (IsSquare (unif 2 4) fz1 ∧ IsSquare (unif 2 4) fz2 ∧ IsSquare (unif 2 4) fz3) ∧
    (∀ z, IsSquare (unif 2 4) z →
      z = fz1 ∨ z = -fz1 ∨ z = fz2 ∨ z = -fz2 ∨ z = fz3 ∨ z = -fz3) ∧
    finrank ℤ (LinearMap.ker (incidence (unif 2 4))) = 2 ∧
    fz1 = fz2 - fz3 ∧
    (LinearIndependent ℤ ![fz1, fz2] ∧
      Submodule.span ℤ ({fz1, fz2} : Set _) = LinearMap.ker (incidence (unif 2 4))) ∧
    (LinearIndependent ℤ ![fz1, fz3] ∧
      Submodule.span ℤ ({fz1, fz3} : Set _) = LinearMap.ker (incidence (unif 2 4))) ∧
    (LinearIndependent ℤ ![fz2, fz3] ∧
      Submodule.span ℤ ({fz2, fz3} : Set _) = LinearMap.ker (incidence (unif 2 4))) := by
  have h3 : fz3 = fz2 - fz1 := by rw [figure1_rel]; abel
  obtain ⟨hli, hspan⟩ := figure1_basis12
  obtain ⟨hA, hB⟩ := basis_pair_sub hli hspan
  refine ⟨figure1_squares, fun z hz => figure1_classify hz, figure1_rank, figure1_rel,
    ⟨hli, hspan⟩, ?_, ?_⟩
  · rw [h3]; exact hA
  · rw [h3]; exact hB

end SquareBasis
