module

public import SquareBasis.PaperRoute

/-!
# Section 2 of the paper: Lemma 2.2 and Proposition 2.3(b), (c)

* `lemma22` — the squares are exactly the exponent vectors of the nonzero symmetric exchange
  binomials (Lemma 2.2). For a square `z`, the binomial `f_z` is written out
  as a symmetric exchange binomial in `binom_square` (`SquareBasis/Toric.lean`).
* `prop23b_full` — deleting a loop changes neither `ker_ℤ A_M` nor the set of squares
  (Proposition 2.3(b)).
* `prop23c` — for a coloop `c`, the map `I' ↦ I' + c` identifies `ker_ℤ A_{M ＼ c}` with
  `ker_ℤ A_M` and squares with squares when `rank (M ＼ c) ≥ 1`, and `ker_ℤ A_M = 0` when
  `rank (M ＼ c) = 0` (Proposition 2.3(c)).
-/

@[expose] public section

namespace SquareBasis

open Matroid Set

universe u

variable {α : Type u}

/-- Two basis vectors `e_X`, `e_Y` are equal when `X = Y`. -/
theorem single_congr {M : Matroid α} {X Y : Set α} (hX : M.IsBase X) (hY : M.IsBase Y)
    (h : X = Y) : Finsupp.single (⟨X, hX⟩ : Bases M) (1 : ℤ) = Finsupp.single ⟨Y, hY⟩ 1 := by
  subst h; rfl

/-- `z` is the exponent vector `e_{B₁} + e_{B₂} - e_{B₁-a+b} - e_{B₂-b+a}` of the binomial
`y_{B₁} y_{B₂} - y_{B₁-a+b} y_{B₂-b+a}` of a symmetric exchange: `B₁, B₂` are bases,
`a ∈ B₁ \ B₂`, `b ∈ B₂ \ B₁`, and `B₁ - a + b`, `B₂ - b + a` are bases. -/
def IsSymExchVec (M : Matroid α) (z : Bases M →₀ ℤ) : Prop :=
  ∃ (B₁ B₂ : Set α) (a b : α) (h₁ : M.IsBase B₁) (h₂ : M.IsBase B₂)
    (h₃ : M.IsBase (insert b (B₁ \ {a}))) (h₄ : M.IsBase (insert a (B₂ \ {b}))),
    a ∈ B₁ ∧ a ∉ B₂ ∧ b ∈ B₂ ∧ b ∉ B₁ ∧
    z = Finsupp.single ⟨B₁, h₁⟩ 1 + Finsupp.single ⟨B₂, h₂⟩ 1
        - Finsupp.single ⟨_, h₃⟩ 1 - Finsupp.single ⟨_, h₄⟩ 1

/-- A square relation is nonzero: its coordinate at `B + i` is `1`. -/
theorem IsSquare.ne_zero {M : Matroid α} {z : Bases M →₀ ℤ} (hz : IsSquare M z) : z ≠ 0 := by
  classical
  obtain ⟨i, j, B, B', h₁, h₂, h₃, h₄, hij, hBB', hiB, hjB, hiB', hjB', rfl⟩ := hz
  intro h0
  have := congrArg (fun f : Bases M →₀ ℤ => f ⟨_, h₁⟩) h0
  simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply,
    Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at this
  have e2 : (⟨insert j B, h₂⟩ : Bases M) ≠ ⟨insert i B, h₁⟩ := by
    intro h
    have : i ∈ insert j B := by
      have h' := congrArg Subtype.val h
      simp only at h'
      rw [h']; exact mem_insert i B
    rcases this with h | h
    · exact hij h
    · exact hiB h
  have e3 : (⟨insert i B', h₃⟩ : Bases M) ≠ ⟨insert i B, h₁⟩ := by
    intro h
    apply hBB'
    have h' := congrArg Subtype.val h
    simp only at h'
    rw [← insert_sdiff_self_of_notMem hiB, ← insert_sdiff_self_of_notMem hiB', h']
  have e4 : (⟨insert j B', h₄⟩ : Bases M) ≠ ⟨insert i B, h₁⟩ := by
    intro h
    have : i ∈ insert j B' := by
      have h' := congrArg Subtype.val h
      simp only at h'
      rw [h']; exact mem_insert i B
    rcases this with h | h
    · exact hij h
    · exact hiB' h
  simp [e2, e3, e4] at this

/-- **Lemma 2.2.** The squares are exactly the exponent vectors of the nonzero symmetric
exchange binomials (the binomial is zero exactly when its exponent vector is zero). -/
theorem lemma22 (M : Matroid α) (z : Bases M →₀ ℤ) :
    IsSquare M z ↔ IsSymExchVec M z ∧ z ≠ 0 := by
  constructor
  · intro hz
    refine ⟨?_, hz.ne_zero⟩
    obtain ⟨i, j, B, B', h₁, h₂, h₃, h₄, hij, hBB', hiB, hjB, hiB', hjB', rfl⟩ := hz
    have e₃ : insert j (insert i B \ {i}) = insert j B := by
      rw [insert_sdiff_self_of_notMem hiB]
    have e₄ : insert i (insert j B' \ {j}) = insert i B' := by
      rw [insert_sdiff_self_of_notMem hjB']
    have h₃' : M.IsBase (insert j (insert i B \ {i})) := e₃ ▸ h₂
    have h₄' : M.IsBase (insert i (insert j B' \ {j})) := e₄ ▸ h₃
    refine ⟨insert i B, insert j B', i, j, h₁, h₄, h₃', h₄', mem_insert i B, ?_,
      mem_insert j B', ?_, ?_⟩
    · rintro (h | h)
      · exact hij h
      · exact hiB' h
    · rintro (h | h)
      · exact hij h.symm
      · exact hjB h
    · rw [single_congr h₃' h₂ e₃, single_congr h₄' h₃ e₄]
      abel
  · rintro ⟨⟨B₁, B₂, a, b, h₁, h₂, h₃, h₄, haB₁, haB₂, hbB₂, hbB₁, rfl⟩, hne⟩
    have hab : a ≠ b := fun h => haB₂ (h ▸ hbB₂)
    have e₁ : insert a (B₁ \ {a}) = B₁ := insert_sdiff_self_of_mem haB₁
    have e₂ : insert b (B₂ \ {b}) = B₂ := insert_sdiff_self_of_mem hbB₂
    have h₁' : M.IsBase (insert a (B₁ \ {a})) := e₁.symm ▸ h₁
    have h₂' : M.IsBase (insert b (B₂ \ {b})) := e₂.symm ▸ h₂
    have hBB' : B₁ \ {a} ≠ B₂ \ {b} := by
      intro h
      apply hne
      have e3 : insert b (B₁ \ {a}) = B₂ := by rw [h, e₂]
      have e4 : insert a (B₂ \ {b}) = B₁ := by rw [← h, e₁]
      rw [single_congr h₃ h₂ e3, single_congr h₄ h₁ e4]
      abel
    refine ⟨a, b, B₁ \ {a}, B₂ \ {b}, h₁', h₃, h₄, h₂', hab, hBB', fun h => h.2 rfl,
      fun h => hbB₁ h.1, fun h => haB₂ h.1, fun h => h.2 rfl, ?_⟩
    rw [single_congr h₁' h₁ e₁, single_congr h₂' h₂ e₂]
    abel

/-! ### Proposition 2.3(b): deleting a loop -/

/-- **Proposition 2.3(b).** Deleting a loop `v` changes neither the bases, nor `ker_ℤ A_M`, nor
the set of squares: the identity on bases induces a linear isomorphism
`ℤ^𝓑(M ＼ v) ≅ ℤ^𝓑(M)` that maps `ker_ℤ A_{M ＼ v}` onto `ker_ℤ A_M` and squares onto
squares. -/
theorem prop23b_full (M : Matroid α) [M.Finite] {v : α} (hv : M.IsLoop v) :
    (∀ B, (M ＼ {v}).IsBase B ↔ M.IsBase B) ∧
    ∃ Φ : (Bases (M ＼ {v}) →₀ ℤ) ≃ₗ[ℤ] (Bases M →₀ ℤ),
      (∀ (B : Set α) (h : (M ＼ {v}).IsBase B) (h' : M.IsBase B),
        Φ (Finsupp.single ⟨B, h⟩ 1) = Finsupp.single ⟨B, h'⟩ 1) ∧
      (∀ f, f ∈ LinearMap.ker (incidence (M ＼ {v})) ↔ Φ f ∈ LinearMap.ker (incidence M)) ∧
      (∀ z, IsSquare (M ＼ {v}) z ↔ IsSquare M (Φ z)) := by
  have hrv : rk M {v} = 0 := by simp [rk, hv.eRk_eq]
  have hvB : ∀ {B}, M.IsBase B → v ∉ B := by
    intro B hB hvB
    have := rk_indep (hB.indep.subset (singleton_subset_iff.2 hvB))
    rw [hrv, ncard_singleton] at this
    norm_num at this
  have hrX : rk M (M.E \ {v}) = rk M M.E := by
    have h1 := rk_union_le M {v} (M.E \ {v})
    have h2 := rk_mono M (show M.E \ {v} ⊆ M.E from sdiff_subset)
    rw [union_sdiff_cancel (singleton_subset_iff.2 hv.mem_ground)] at h1
    linarith
  have hbase : ∀ {B}, (M ＼ {v}).IsBase B ↔ M.IsBase B := by
    intro B
    rw [delete_isBase_iff_of_rk hrX]
    exact ⟨fun h => h.1, fun h => ⟨h, hvB h⟩⟩
  refine ⟨fun B => hbase, ?_⟩
  let e : Bases (M ＼ {v}) ≃ Bases M :=
    { toFun := fun B => ⟨B.1, hbase.1 B.2⟩
      invFun := fun B => ⟨B.1, hbase.2 B.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Φ : (Bases (M ＼ {v}) →₀ ℤ) ≃ₗ[ℤ] (Bases M →₀ ℤ) := Finsupp.domLCongr e
  have hΦs : ∀ (B : Set α) (h : (M ＼ {v}).IsBase B) (h' : M.IsBase B),
      Φ (Finsupp.single ⟨B, h⟩ 1) = Finsupp.single ⟨B, h'⟩ 1 := by
    intro B h h'
    simp only [Φ, Finsupp.domLCongr_single]
    rfl
  have hinc : ∀ f, incidence M (Φ f) = incidence (M ＼ {v}) f := by
    intro f
    simp only [Φ, incidence, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_eq_mapDomain, Finsupp.linearCombination_mapDomain]
    rfl
  refine ⟨Φ, hΦs, fun f => by simp only [LinearMap.mem_ker, hinc], fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨i, j, B, B', h₁, h₂, h₃, h₄, hij, hBB', hiB, hjB, hiB', hjB', rfl⟩
    refine ⟨i, j, B, B', hbase.1 h₁, hbase.1 h₂, hbase.1 h₃, hbase.1 h₄, hij, hBB', hiB, hjB,
      hiB', hjB', ?_⟩
    simp only [map_add, map_sub]
    rw [hΦs _ h₁ (hbase.1 h₁), hΦs _ h₂ (hbase.1 h₂), hΦs _ h₃ (hbase.1 h₃),
      hΦs _ h₄ (hbase.1 h₄)]
  · rintro ⟨i, j, B, B', h₁, h₂, h₃, h₄, hij, hBB', hiB, hjB, hiB', hjB', hz⟩
    refine ⟨i, j, B, B', hbase.2 h₁, hbase.2 h₂, hbase.2 h₃, hbase.2 h₄, hij, hBB', hiB, hjB,
      hiB', hjB', Φ.injective ?_⟩
    rw [hz]
    simp only [map_add, map_sub]
    rw [hΦs _ (hbase.2 h₁) h₁, hΦs _ (hbase.2 h₂) h₂, hΦs _ (hbase.2 h₃) h₃,
      hΦs _ (hbase.2 h₄) h₄]

/-! ### Proposition 2.3(c): a coloop -/

open scoped Classical in
/-- If every basis contains `a`, then the `a`-row of `A_M` is the coordinate sum. -/
theorem incidence_apply_of_forall_mem {M : Matroid α} {a : α} (ha : ∀ B : Bases M, a ∈ B.1)
    (f : Bases M →₀ ℤ) : incidence M f a = total f := by
  rw [incidence_apply, total]
  exact Finsupp.sum_congr fun B _ => ite_eq_left (ha B)

/-- The bases of `M ＼ c` for a coloop `c` are the sets `B'` with `c ∉ B'` and `B' + c` a basis
of `M`. -/
theorem delete_coloop_isBase_iff {M : Matroid α} {c : α} (hc : M.IsColoop c) {B : Set α} :
    (M ＼ {c}).IsBase B ↔ M.IsBase (insert c B) ∧ c ∉ B := by
  have hsub : ({c} : Set α) ⊆ M.coloops := singleton_subset_iff.2 hc
  rw [← contract_eq_delete_of_subset_coloops hsub,
    (hc.isNonloop.indep : M.Indep {c}).contract_isBase_iff, union_singleton,
    disjoint_singleton_right]

/-- **Proposition 2.3(c).** Let `c` be a coloop of `M`, so that `M = (M ＼ c) ⊕ {c}`.
If `rank (M ＼ c) ≥ 1`, then `I' ↦ I' + c` induces a linear isomorphism that maps
`ker_ℤ A_{M ＼ c}` onto `ker_ℤ A_M` and squares onto squares. If `rank (M ＼ c) = 0`, then
`ker_ℤ A_M = 0`. -/
theorem prop23c (M : Matroid α) [M.Finite] {c : α} (hc : M.IsColoop c) :
    (∀ B, (M ＼ {c}).IsBase B ↔ M.IsBase (insert c B) ∧ c ∉ B) ∧
    ((M ＼ {c}).RankPos →
      ∃ Φ : (Bases (M ＼ {c}) →₀ ℤ) ≃ₗ[ℤ] (Bases M →₀ ℤ),
        (∀ (B : Set α) (h : (M ＼ {c}).IsBase B) (h' : M.IsBase (insert c B)),
          Φ (Finsupp.single ⟨B, h⟩ 1) = Finsupp.single ⟨insert c B, h'⟩ 1) ∧
        (∀ f, f ∈ LinearMap.ker (incidence (M ＼ {c})) ↔ Φ f ∈ LinearMap.ker (incidence M)) ∧
        (∀ z, IsSquare (M ＼ {c}) z ↔ IsSquare M (Φ z))) ∧
    (¬ (M ＼ {c}).RankPos → LinearMap.ker (incidence M) = ⊥) := by
  classical
  have hb : ∀ {B}, (M ＼ {c}).IsBase B ↔ M.IsBase (insert c B) ∧ c ∉ B :=
    delete_coloop_isBase_iff hc
  have hcol : ∀ {B}, M.IsBase B → c ∈ B := fun h => hc.mem_of_isBase h
  -- the bijection `B' ↦ B' + c`
  let e : Bases (M ＼ {c}) ≃ Bases M :=
    { toFun := fun B => ⟨insert c B.1, (hb.1 B.2).1⟩
      invFun := fun B => ⟨B.1 \ {c}, hb.2 ⟨by rw [insert_sdiff_self_of_mem (hcol B.2)]; exact B.2,
        fun h => h.2 rfl⟩⟩
      left_inv := fun B => Subtype.ext (insert_sdiff_self_of_notMem (hb.1 B.2).2)
      right_inv := fun B => Subtype.ext (insert_sdiff_self_of_mem (hcol B.2)) }
  refine ⟨fun B => hb, fun hpos => ?_, fun hnpos => ?_⟩
  · let Φ : (Bases (M ＼ {c}) →₀ ℤ) ≃ₗ[ℤ] (Bases M →₀ ℤ) := Finsupp.domLCongr e
    have hΦs : ∀ (B : Set α) (h : (M ＼ {c}).IsBase B) (h' : M.IsBase (insert c B)),
        Φ (Finsupp.single ⟨B, h⟩ 1) = Finsupp.single ⟨insert c B, h'⟩ 1 := by
      intro B h h'
      simp only [Φ, Finsupp.domLCongr_single]
      rfl
    -- the rows of `A_M` on `Φ f`
    have hrow : ∀ f (x : α), incidence M (Φ f) x =
        if x = c then total f else incidence (M ＼ {c}) f x := by
      intro f x
      have : incidence M (Φ f) = Finsupp.linearCombination ℤ
          (fun B : Bases (M ＼ {c}) => Set.indicator (insert c B.1) (fun _ => (1 : ℤ))) f := by
        simp only [Φ, incidence, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
          Finsupp.equivMapDomain_eq_mapDomain, Finsupp.linearCombination_mapDomain]
        rfl
      rw [this]
      simp only [incidence, total, Finsupp.linearCombination_apply, Finsupp.sum,
        Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero, Set.mem_insert_iff]
      split_ifs with hx
      · subst hx; simp
      · simp [hx]
    have hker : ∀ f, f ∈ LinearMap.ker (incidence (M ＼ {c})) ↔
        Φ f ∈ LinearMap.ker (incidence M) := by
      intro f
      simp only [LinearMap.mem_ker]
      constructor
      · intro hf
        have ht := total_eq_zero_of_mem_ker (M ＼ {c}) (LinearMap.mem_ker.2 hf)
        funext x
        rw [hrow]
        split_ifs
        · exact ht
        · rw [hf]
      · intro hf
        funext x
        by_cases hx : x = c
        · subst hx
          exact incidence_eq_zero_of_notMem _ f (by simp)
        · have := congrFun hf x
          rw [hrow, ite_eq_right hx] at this
          exact this
    refine ⟨Φ, hΦs, hker, fun z => ⟨?_, ?_⟩⟩
    · rintro ⟨i, j, B, B', h₁, h₂, h₃, h₄, hij, hBB', hiB, hjB, hiB', hjB', rfl⟩
      have hic : i ≠ c := fun h => by
        have := h₁.subset_ground (mem_insert i B); simp [h] at this
      have hjc : j ≠ c := fun h => by
        have := h₂.subset_ground (mem_insert j B); simp [h] at this
      have hcB0 : c ∉ B := fun h => by
        have := h₁.subset_ground (mem_insert_of_mem i h); simp at this
      have hcB0' : c ∉ B' := fun h => by
        have := h₃.subset_ground (mem_insert_of_mem i h); simp at this
      have comm : ∀ {x : α} {Y : Set α}, insert c (insert x Y) = insert x (insert c Y) :=
        insert_comm _ _ _
      have g₁ : M.IsBase (insert i (insert c B)) := comm ▸ (hb.1 h₁).1
      have g₂ : M.IsBase (insert j (insert c B)) := comm ▸ (hb.1 h₂).1
      have g₃ : M.IsBase (insert i (insert c B')) := comm ▸ (hb.1 h₃).1
      have g₄ : M.IsBase (insert j (insert c B')) := comm ▸ (hb.1 h₄).1
      refine ⟨i, j, insert c B, insert c B', g₁, g₂, g₃, g₄, hij, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h; apply hBB'
        rw [← insert_sdiff_self_of_notMem hcB0, ← insert_sdiff_self_of_notMem hcB0', h]
      · rintro (h | h); exacts [hic h, hiB h]
      · rintro (h | h); exacts [hjc h, hjB h]
      · rintro (h | h); exacts [hic h, hiB' h]
      · rintro (h | h); exacts [hjc h, hjB' h]
      · simp only [map_add, map_sub]
        rw [hΦs _ h₁ (hb.1 h₁).1, hΦs _ h₂ (hb.1 h₂).1, hΦs _ h₃ (hb.1 h₃).1,
          hΦs _ h₄ (hb.1 h₄).1]
        rw [single_congr _ g₁ comm, single_congr _ g₂ comm, single_congr _ g₃ comm,
          single_congr _ g₄ comm]
    · rintro ⟨i, j, B, B', h₁, h₂, h₃, h₄, hij, hBB', hiB, hjB, hiB', hjB', hz⟩
      -- every square of `M` has `c ∈ B ∩ B'`
      have hcB : c ∈ B := by
        by_contra hcB
        have hi : c ∈ insert i B := hcol h₁
        have hj : c ∈ insert j B := hcol h₂
        rcases hi with hi | hi
        · rcases hj with hj | hj
          · exact hij (hi.symm.trans hj)
          · exact hcB hj
        · exact hcB hi
      have hcB'' : c ∈ B' := by
        by_contra hcB
        have hi : c ∈ insert i B' := hcol h₃
        have hj : c ∈ insert j B' := hcol h₄
        rcases hi with hi | hi
        · rcases hj with hj | hj
          · exact hij (hi.symm.trans hj)
          · exact hcB hj
        · exact hcB hi
      have hic : i ≠ c := fun h => hiB (h ▸ hcB)
      have hjc : j ≠ c := fun h => hjB (h ▸ hcB)
      have key : ∀ {x : α} {Y : Set α}, c ∈ Y → x ≠ c →
          insert c (insert x (Y \ {c})) = insert x Y := by
        intro x Y hY hx
        rw [insert_comm, insert_sdiff_self_of_mem hY]
      have nc : ∀ {x : α} {Y : Set α}, x ≠ c → c ∉ insert x (Y \ {c}) := by
        intro x Y hx h
        rcases h with h | h
        · exact hx h.symm
        · exact h.2 rfl
      have k₁ : (M ＼ {c}).IsBase (insert i (B \ {c})) :=
        hb.2 ⟨(key hcB hic).symm ▸ h₁, nc hic⟩
      have k₂ : (M ＼ {c}).IsBase (insert j (B \ {c})) :=
        hb.2 ⟨(key hcB hjc).symm ▸ h₂, nc hjc⟩
      have k₃ : (M ＼ {c}).IsBase (insert i (B' \ {c})) :=
        hb.2 ⟨(key hcB'' hic).symm ▸ h₃, nc hic⟩
      have k₄ : (M ＼ {c}).IsBase (insert j (B' \ {c})) :=
        hb.2 ⟨(key hcB'' hjc).symm ▸ h₄, nc hjc⟩
      refine ⟨i, j, B \ {c}, B' \ {c}, k₁, k₂, k₃, k₄, hij, ?_, fun h => hiB h.1,
        fun h => hjB h.1, fun h => hiB' h.1, fun h => hjB' h.1, Φ.injective ?_⟩
      · intro h; apply hBB'
        rw [← insert_sdiff_self_of_mem hcB, ← insert_sdiff_self_of_mem hcB'', h]
      · rw [hz]
        simp only [map_add, map_sub]
        rw [hΦs _ k₁ (hb.1 k₁).1, hΦs _ k₂ (hb.1 k₂).1, hΦs _ k₃ (hb.1 k₃).1,
          hΦs _ k₄ (hb.1 k₄).1]
        rw [single_congr _ h₁ (key hcB hic), single_congr _ h₂ (key hcB hjc),
          single_congr _ h₃ (key hcB'' hic), single_congr _ h₄ (key hcB'' hjc)]
  · -- `rank (M ＼ c) = 0`: the only basis of `M` is `{c}`
    have h0 : (M ＼ {c}).IsBase ∅ := by
      by_contra h
      exact hnpos ⟨h⟩
    have hsub : Subsingleton (Bases M) := by
      constructor
      intro B₁ B₂
      have h1 : (M ＼ {c}).IsBase (B₁.1 \ {c}) := hb.2 ⟨by rw [insert_sdiff_self_of_mem (hcol B₁.2)]; exact B₁.2,
        fun h => h.2 rfl⟩
      have h2 : (M ＼ {c}).IsBase (B₂.1 \ {c}) := hb.2 ⟨by rw [insert_sdiff_self_of_mem (hcol B₂.2)]; exact B₂.2,
        fun h => h.2 rfl⟩
      have e1 := h0.eq_of_subset_isBase h1 (empty_subset _)
      have e2 := h0.eq_of_subset_isBase h2 (empty_subset _)
      apply Subtype.ext
      rw [← insert_sdiff_self_of_mem (hcol B₁.2), ← insert_sdiff_self_of_mem (hcol B₂.2),
        ← e1, ← e2]
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    rw [LinearMap.mem_ker] at hf
    have ht := incidence_apply_of_forall_mem (fun B : Bases M => hcol B.2) f
    rw [hf] at ht
    ext B
    have hf' : f = Finsupp.single B (f B) := by
      ext B'
      rw [Subsingleton.elim B' B, Finsupp.single_eq_same]
    rw [hf', total, Finsupp.sum_single_index rfl] at ht
    simpa using ht.symm

end SquareBasis
