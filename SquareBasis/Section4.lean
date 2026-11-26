module

public import SquareBasis.Lifting
public import SquareBasis.Section5

/-!
# Section 4 of the paper: the connected case along the graph `H`

* `HAdj` : the graph `H = H(M, v)` on the bases of `M ／ v` (written as the bases of `M`
  containing `v`).
* `thm43` : Theorem 4.3, lifting a square basis of `M ＼ v` along a spanning tree of `H`,
  with the squares `z_{v,j;J,J'}`.
* `prop44` : Proposition 4.4 (the direction used): if the cocircuits of `M` through `v`
  link `E - v`, then `H` is connected.
* `thm46` : Theorem 4.6, every connected matroid of rank at least one has a square basis,
  proved along the route of the paper (Tutte's theorem, Theorem 4.5 for `M✶`,
  Proposition 4.4, Theorem 4.3, Lemma 2.4).
-/

@[expose] public section

namespace SquareBasis

open Matroid Set

universe u

variable {α : Type u}

/-- The graph `H`: distinct `J + v`, `J' + v` are adjacent if `J + j` and `J' + j` are bases
of `M ＼ v` for some `j ∉ J ∪ J'`. -/
def HAdj (M : Matroid α) (v : α) (a b : basesWith M v) : Prop :=
  a ≠ b ∧ ∃ j, j ∉ a.1.1 ∧ j ∉ b.1.1 ∧ M.IsBase (insert j (a.1.1 \ {v})) ∧
    M.IsBase (insert j (b.1.1 \ {v}))

/-- An edge of `H` is realized by the square `z_{v,j;J,J'}`. -/
theorem sqAdj_of_hAdj {M : Matroid α} [M.Finite] {v : α} {a b : basesWith M v}
    (h : HAdj M v a b) : SqAdj M v a b := by
  classical
  obtain ⟨hab, j, hja, hjb, hja', hjb'⟩ := h
  have hva : v ∈ a.1.1 := a.2
  have hvb : v ∈ b.1.1 := b.2
  set J := a.1.1 \ {v} with hJ
  set J' := b.1.1 \ {v} with hJ'
  have hJa : insert v J = a.1.1 := by rw [hJ, insert_sdiff_singleton, insert_eq_of_mem hva]
  have hJb : insert v J' = b.1.1 := by rw [hJ', insert_sdiff_singleton, insert_eq_of_mem hvb]
  have hb₁ : M.IsBase (insert v J) := hJa ▸ a.1.2
  have hb₃ : M.IsBase (insert v J') := hJb ▸ b.1.2
  have hvj : v ≠ j := fun h => hja (h ▸ hva)
  have hJJ' : J' ≠ J := by
    intro h
    apply hab
    apply Subtype.ext; apply Subtype.ext
    rw [← hJa, ← hJb, h]
  -- the square `z_{v,j;J',J}` has `π`-image `e_b - e_a`... we use `z_{v,j;J',J}`
  refine ⟨_, ⟨v, j, J', J, hb₃, hjb', hb₁, hja', hvj, hJJ', fun h => h.2 rfl,
    fun h => hjb h.1, fun h => h.2 rfl, fun h => hja h.1, rfl⟩, ?_⟩
  ext w
  have hw := w.2
  simp only [map_add, map_sub, Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply,
    Pi.sub_apply, restrictV_apply, Finsupp.single_apply]
  have n2 : (⟨insert j J', hjb'⟩ : Bases M) ≠ w.1 := by
    intro h; rw [← h] at hw
    rcases hw with h' | h'
    · exact hvj h'
    · exact h'.2 rfl
  have n4 : (⟨insert j J, hja'⟩ : Bases M) ≠ w.1 := by
    intro h; rw [← h] at hw
    rcases hw with h' | h'
    · exact hvj h'
    · exact h'.2 rfl
  have e1 : ((⟨insert v J', hb₃⟩ : Bases M) = w.1) ↔ (b = w) := by
    constructor
    · intro h; apply Subtype.ext; rw [← h]; exact Subtype.ext hJb.symm
    · intro h; rw [← h]; exact Subtype.ext hJb
  have e3 : ((⟨insert v J, hb₁⟩ : Bases M) = w.1) ↔ (a = w) := by
    constructor
    · intro h; apply Subtype.ext; rw [← h]; exact Subtype.ext hJa.symm
    · intro h; rw [← h]; exact Subtype.ext hJa
  simp only [e1, e3, n2, n4, ite_false, sub_zero, add_zero]

theorem hAdj_symm {M : Matroid α} {v : α} {a b : basesWith M v} (h : HAdj M v a b) :
    HAdj M v b a := by
  obtain ⟨hab, j, h1, h2, h3, h4⟩ := h
  exact ⟨Ne.symm hab, j, h2, h1, h4, h3⟩

/-- **Theorem 4.3 (lifting along a spanning tree of `H`).** If `v` is not a coloop, `H` is
connected and `M ＼ v` has a square basis, then `M` has a square basis. -/
theorem thm43 (M : Matroid α) [M.Finite] (v : α) (hv : rk M (M.E \ {v}) = rk M M.E)
    (hH : ∀ a b : basesWith M v, Relation.ReflTransGen (HAdj M v) a b)
    (hN : HasSquareBasis (M ＼ {v})) : HasSquareBasis M := by
  have hmono : ∀ {a b : basesWith M v}, Relation.ReflTransGen (HAdj M v) a b →
      Relation.ReflTransGen (SqAdj M v) a b := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail (sqAdj_of_hAdj hbc)
  exact lift_of_sqAdj M v hv (fun a b => hmono (hH a b)) hN

/-! ### Proposition 4.4 -/

/-- `N(J)`: the elements `x ∉ J + v` with `J + x` a basis. -/
def nbr (M : Matroid α) (v : α) (a : basesWith M v) : Set α :=
  {x | x ∉ a.1.1 ∧ M.IsBase (insert x (a.1.1 \ {v}))}

/-- `N(J)` is nonempty when `v` is not a coloop. -/
theorem nbr_nonempty {M : Matroid α} [M.Finite] {v : α} (hv : rk M (M.E \ {v}) = rk M M.E)
    (a : basesWith M v) : (nbr M v a).Nonempty := by
  obtain ⟨B₀, hB₀⟩ := (M ＼ {v}).exists_isBase
  rw [delete_isBase_iff_of_rk hv] at hB₀
  obtain ⟨y, ⟨hyB₀, hya⟩, hb⟩ := a.1.2.exchange hB₀.1 ⟨a.2, hB₀.2⟩
  exact ⟨y, hya, hb⟩

/-- A cocircuit through `v` and `x, x'` gives one `J` with `x, x' ∈ N(J)`. -/
theorem exists_nbr_of_linked {M : Matroid α} [M.Finite] {v x x' : α}
    (h : Linked M✶ v x x') : ∃ a : basesWith M v, x ∈ nbr M v a ∧ x' ∈ nbr M v a := by
  obtain ⟨hxv, hx'v, K, hK, hvK, hxK, hx'K⟩ := h
  have hKv : M✶.Indep (K \ {v}) := hK.ssubset_indep
    (ssubset_of_subset_of_ne sdiff_subset (fun h => by
      have : v ∈ K \ {v} := by rw [h]; exact hvK
      exact this.2 rfl))
  obtain ⟨Bs, hBs, hKBs⟩ := hKv.exists_isBase_superset
  have hvBs : v ∉ Bs := by
    intro hvB
    apply hK.dep.not_indep (hBs.indep.subset _)
    intro y hy
    by_cases hyv : y = v
    · exact hyv ▸ hvB
    · exact hKBs ⟨hy, hyv⟩
  have hvE : v ∈ M.E := by simpa using hK.subset_ground hvK
  -- for `y ∈ K - v`, `Bs - y + v` is a base of `M✶`
  have key : ∀ y ∈ K, y ≠ v → M✶.IsBase (insert v (Bs \ {y})) := by
    intro y hyK hyv
    apply hBs.exchange_isBase_of_indep hvBs
    by_contra hdep
    have hsub : insert v (Bs \ {y}) ⊆ M✶.E :=
      insert_subset (by simpa using hvE) (sdiff_subset.trans hBs.subset_ground)
    obtain ⟨K', hK's, hK'⟩ := (show M✶.Dep (insert v (Bs \ {y})) from
      ⟨hdep, hsub⟩).exists_isCircuit_subset
    have h1 : K' ⊆ insert v Bs := hK's.trans (insert_subset_insert sdiff_subset)
    have h2 : K ⊆ insert v Bs := by
      intro z hz
      by_cases hzv : z = v
      · exact Or.inl hzv
      · exact Or.inr (hKBs ⟨hz, hzv⟩)
    have := isCircuit_insert_unique hBs.indep hK' hK h1 h2
    rw [← this] at hyK
    rcases hK's hyK with h | h
    · exact hyv h
    · exact h.2 rfl
  -- complement in `M`
  have ha : M.IsBase (M.E \ Bs) := hBs.compl_isBase_of_dual
  have hva : v ∈ M.E \ Bs := ⟨hvE, hvBs⟩
  let a : basesWith M v := ⟨⟨_, ha⟩, hva⟩
  have hn : ∀ y ∈ K, y ≠ v → y ∈ nbr M v a := by
    intro y hyK hyv
    have hyBs : y ∈ Bs := hKBs ⟨hyK, hyv⟩
    refine ⟨fun h => h.2 hyBs, ?_⟩
    have e : M.E \ insert v (Bs \ {y}) = insert y ((M.E \ Bs) \ {v}) := by
      have hyE : y ∈ M.E := by simpa using hBs.subset_ground hyBs
      ext z
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or, not_and, not_not]
      constructor
      · rintro ⟨hz, hzv, hzB⟩
        by_cases hzy : z = y
        · exact Or.inl hzy
        · exact Or.inr ⟨⟨hz, fun h => hzy (hzB h)⟩, hzv⟩
      · rintro (rfl | ⟨⟨hz, hzB⟩, hzv⟩)
        · exact ⟨hyE, hyv, fun _ => rfl⟩
        · exact ⟨hz, hzv, fun h => absurd h hzB⟩
    have := (key y hyK hyv).compl_isBase_of_dual
    rw [e] at this
    exact this
  exact ⟨a, hn x hxK hxv, hn x' hx'K hx'v⟩

/-- **Proposition 4.4** (the direction used in the proof). If the cocircuits of `M` through `v`
link all of `E - v`, then `H` is connected. -/
theorem prop44 {M : Matroid α} [M.Finite] {v : α} (hv : rk M (M.E \ {v}) = rk M M.E)
    (hΦ : ∀ x ∈ M.E \ {v}, ∀ y ∈ M.E \ {v}, Relation.ReflTransGen (Linked M✶ v) x y) :
    ∀ a b : basesWith M v, Relation.ReflTransGen (HAdj M v) a b := by
  classical
  have step : ∀ {c d : basesWith M v} {x : α}, x ∈ nbr M v c → x ∈ nbr M v d →
      Relation.ReflTransGen (HAdj M v) c d := by
    intro c d x hc hd
    by_cases hcd : c = d
    · rw [hcd]
    · exact Relation.ReflTransGen.single ⟨hcd, x, hc.1, hd.1, hc.2, hd.2⟩
  have memX : ∀ {c : basesWith M v} {x : α}, x ∈ nbr M v c → x ∈ M.E \ {v} := by
    intro c x hx
    refine ⟨hx.2.subset_ground (mem_insert _ _), fun h => hx.1 ?_⟩
    rw [mem_singleton_iff] at h
    exact h ▸ c.2
  intro a b
  obtain ⟨j, hj⟩ := nbr_nonempty hv a
  obtain ⟨j', hj'⟩ := nbr_nonempty hv b
  have walk : ∀ y, Relation.ReflTransGen (Linked M✶ v) j y →
      ∃ c, y ∈ nbr M v c ∧ Relation.ReflTransGen (HAdj M v) a c := by
    intro y hy
    induction hy with
    | refl => exact ⟨a, hj, Relation.ReflTransGen.refl⟩
    | tail _ hyz ih =>
      obtain ⟨c, hyc, hac⟩ := ih
      obtain ⟨d, hyd, hzd⟩ := exists_nbr_of_linked hyz
      exact ⟨d, hzd, hac.trans (step hyc hyd)⟩
  obtain ⟨c, hj'c, hac⟩ := walk j' (hΦ j (memX hj) j' (memX hj'))
  exact hac.trans (step hj'c hj')

/-! ### Theorem 4.6 -/

/-- The case `M ＼ v` connected in the proof of Theorem 4.6: Theorem 4.5 for `P = M✶`
(`P ／ v = (M ＼ v)✶`), Proposition 4.4 and Theorem 4.3. -/
theorem thm46_delete_case (N : Matroid α) [N.Finite] {v : α} (hN : Conn N) (hv : v ∈ N.E)
    (hne : (N.E \ {v}).Nonempty) (hNd : Conn (N ＼ {v})) (hsq : HasSquareBasis (N ＼ {v})) :
    HasSquareBasis N := by
  obtain ⟨-, hrX⟩ := conn_rk_facts hN hv hne
  have hP : Conn N✶ := (conn_dual N).2 hN
  have hPv : Conn (N✶ ／ {v}) := by rw [← dual_delete]; exact (conn_dual _).2 hNd
  have hΦ := thm45 hP (by simpa using hv) hPv
  have hΦ' : ∀ x ∈ N.E \ {v}, ∀ y ∈ N.E \ {v},
      Relation.ReflTransGen (Linked N✶ v) x y := by simpa using hΦ
  exact thm43 N v hrX (prop44 hrX hΦ') hsq

/-- **Theorem 4.6.** Every connected matroid of rank at least one has a square basis. The proof
is the induction of the paper. -/
theorem thm46 : ∀ (n : ℕ) (M : Matroid α) [M.Finite] [M.RankPos], M.E.ncard = n → Conn M →
    HasSquareBasis M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ hn hM
  obtain ⟨B₀, hB₀⟩ := M.exists_isBase
  obtain ⟨v, hvB₀⟩ := hB₀.nonempty
  have hv : v ∈ M.E := hB₀.subset_ground hvB₀
  by_cases hne : (M.E \ {v}).Nonempty
  · obtain ⟨hrv, hrX⟩ := conn_rk_facts hM hv hne
    have hlt : (M.E \ {v}).ncard < n := by
      rw [← hn]; exact Set.ncard_sdiff_singleton_lt_of_mem hv M.ground_finite
    rcases tutte_minor hM hv hne with hd | hc
    · -- `M ＼ v` connected
      have : (M ＼ {v}).RankPos := rankPos_delete hrX
      exact thm46_delete_case M hM hv hne hd (ih _ hlt (M ＼ {v}) rfl hd)
    · -- `M ／ v` connected: pass to `M✶`, where `M✶ ＼ v = (M ／ v)✶` is connected
      have hMd : Conn M✶ := (conn_dual M).2 hM
      have hMdv : Conn (M✶ ＼ {v}) := by rw [← dual_contract]; exact (conn_dual _).2 hc
      have hrX' : rk M✶ (M✶.E \ {v}) = rk M✶ M✶.E := by
        have := rk_dual_sdiff_singleton M hv
        rw [hrv] at this
        simp only [dual_ground]
        linarith
      have : M✶.RankPos := by
        refine ⟨fun h => ?_⟩
        have hE := h.compl_isBase_of_dual
        simp only [sdiff_empty] at hE
        have h1 := rk_ground_eq_of_isBase hE
        have h2 := rk_le_ncard M (M.ground_finite.subset (sdiff_subset : M.E \ {v} ⊆ M.E))
        have h3 := Set.ncard_sdiff_singleton_add_one hv M.ground_finite
        have h3' : ((M.E \ {v}).ncard : ℤ) + 1 = M.E.ncard := by exact_mod_cast h3
        linarith
      have : (M✶ ＼ {v}).RankPos := rankPos_delete hrX'
      have hv' : v ∈ M✶.E := by simpa using hv
      have hne' : (M✶.E \ {v}).Nonempty := by simpa using hne
      have hsq := ih _ (by simpa using hlt) (M✶ ＼ {v}) (by simp) hMdv
      exact (hasSquareBasis_dual_iff M).1 (thm46_delete_case M✶ hMd hv' hne' hMdv hsq)
  · -- one element: the ground set is a base
    apply hasSquareBasis_of_isBase_ground
    have hE : M.E = {v} := by
      ext x; simp only [mem_singleton_iff]
      constructor
      · intro hx; by_contra hxv; exact hne ⟨x, hx, hxv⟩
      · rintro rfl; exact hv
    have hB : B₀ = M.E := by
      rw [hE]
      ext x; simp only [mem_singleton_iff]
      constructor
      · intro hx; have := hB₀.subset_ground hx; rw [hE] at this; exact this
      · rintro rfl; exact hvB₀
    exact hB ▸ hB₀

end SquareBasis
