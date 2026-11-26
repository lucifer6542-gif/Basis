module

public import SquareBasis.Section2
public import Mathlib.Combinatorics.Colex

/-!
# Uniform matroids and the combinatorics of Section 6

The paper's ground set is `[n] = {1, …, n}`; here it is `Fin n = {0, …, n-1}`, so the paper's
element `m` is `m - 1` here. Under this shift the paper's `[m] = {1, …, m}` is
`ini n m = {x : x < m}`.

* `unif k n` — the uniform matroid `U_{k,n}` on `Fin n`.
* `colexLt X Y` — the colex order of the paper: `X ≺ Y` iff `max (X △ Y) ∈ Y`
  (Mathlib's `Finset.Colex`, see `Finset.Colex.toColex_lt_toColex_iff_max'_mem`).
* `Tset`, `Sset`, `iOf`, `jOf`, `BOf`, `BpOf` — the sets `T`, `S` and the data `i, j, B, B'`
  of Proposition 6.2.
-/

@[expose] public section

namespace SquareBasis

open Finset Matroid

/-! ### The uniform matroid -/

/-- The independence system of `U_{k,n}`: the sets of size at most `k`. -/
def unifIndepMatroid (k n : ℕ) : IndepMatroid (Fin n) :=
  IndepMatroid.ofFinite (E := Set.univ) Set.finite_univ (fun I => I.ncard ≤ k) (by simp)
    (fun _ _ hJ hIJ => (Set.ncard_le_ncard hIJ).trans hJ)
    (by
      intro I J _ hJ hIJ
      obtain ⟨e, heJ, heI⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hIJ
      refine ⟨e, heJ, heI, ?_⟩
      rw [Set.ncard_insert_of_notMem heI]
      omega)
    (fun _ _ => Set.subset_univ _)

/-- The uniform matroid `U_{k,n}` on `Fin n`: the bases are the `k`-subsets. -/
def unif (k n : ℕ) : Matroid (Fin n) := (unifIndepMatroid k n).matroid

theorem unif_indep_iff {k n : ℕ} {I : Set (Fin n)} : (unif k n).Indep I ↔ I.ncard ≤ k := by
  simp [unif, unifIndepMatroid]

theorem unif_isBase_iff {k n : ℕ} (hk : k ≤ n) {B : Set (Fin n)} :
    (unif k n).IsBase B ↔ B.ncard = k := by
  rw [isBase_iff_maximal_indep]
  constructor
  · intro h
    have hle : B.ncard ≤ k := unif_indep_iff.1 h.prop
    by_contra hne
    have hlt : B.ncard < k := lt_of_le_of_ne hle hne
    have hB : B ≠ Set.univ := by
      intro hB
      rw [hB, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hlt
      omega
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem B).1 hB
    have hind : (unif k n).Indep (insert x B) := by
      rw [unif_indep_iff, Set.ncard_insert_of_notMem hx]; omega
    exact hx (h.eq_of_subset hind (Set.subset_insert x B) ▸ Set.mem_insert x B)
  · intro h
    refine ⟨unif_indep_iff.2 h.le, fun J hJ hBJ => ?_⟩
    have hJ' : J.ncard ≤ B.ncard := h ▸ unif_indep_iff.1 hJ
    exact (Set.eq_of_subset_of_ncard_le hBJ hJ').symm.le

/-- The bases of `U_{k,n}` as finsets. -/
theorem unif_isBase_coe_iff {k n : ℕ} (hk : k ≤ n) {B : Finset (Fin n)} :
    (unif k n).IsBase (B : Set (Fin n)) ↔ B.card = k := by
  rw [unif_isBase_iff hk, Set.ncard_coe_finset]

/-! ### The colex order -/

/-- The colex order of the paper on subsets of `Fin n`: `X ≺ Y` if `max (X △ Y) ∈ Y`. -/
def colexLt {n : ℕ} (X Y : Set (Fin n)) : Prop :=
  open scoped Classical in toColex (univ.filter (· ∈ X)) < toColex (univ.filter (· ∈ Y))

theorem colexLt_coe {n : ℕ} (X Y : Finset (Fin n)) :
    colexLt (X : Set (Fin n)) Y ↔ toColex X < toColex Y := by
  classical
  simp only [colexLt, Finset.mem_coe, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- The colex order is `max (X △ Y) ∈ Y`, as in the paper. -/
theorem colexLt_coe_iff_max {n : ℕ} (X Y : Finset (Fin n)) :
    colexLt (X : Set (Fin n)) Y ↔
      ∃ h : X ≠ Y, (symmDiff X Y).max' (symmDiff_nonempty.2 h) ∈ Y := by
  rw [colexLt_coe, Finset.Colex.toColex_lt_toColex_iff_max'_mem]

variable {n : ℕ}

/-- If every element of `X` is below `a ∈ Y`, then `X ≺ Y`. -/
theorem colex_lt_of_forall_lt {X Y : Finset (Fin n)} {a : Fin n} (ha : a ∈ Y)
    (hX : ∀ x ∈ X, x < a) : toColex X < toColex Y := by
  rw [Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt]
  exact ⟨a, ha, fun h => lt_irrefl a (hX a h), fun b hb _ => hX b hb⟩

/-- `B' ≺ B` and `i ∉ B ∪ B'` give `B' + i ≺ B + i`. -/
theorem colex_insert_lt_insert {B B' : Finset (Fin n)} {i : Fin n} (hiB : i ∉ B)
    (h : toColex B' < toColex B) : toColex (insert i B') < toColex (insert i B) := by
  rw [Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt] at h ⊢
  obtain ⟨a, haB, haB', hall⟩ := h
  have hai : a ≠ i := fun h => hiB (h ▸ haB)
  refine ⟨a, mem_insert_of_mem haB, ?_, ?_⟩
  · rw [mem_insert]; rintro (h | h); exacts [hai h, haB' h]
  · intro b hb hb'
    rw [mem_insert] at hb hb'
    push Not at hb'
    rcases hb with rfl | hb
    · exact absurd rfl hb'.1
    · exact hall b hb hb'.2

/-- `[m] = {x : x < m}` (the paper's `{1, …, m}` after the shift). -/
def ini (n m : ℕ) : Finset (Fin n) := univ.filter (fun x : Fin n => x.val < m)

@[simp] theorem mem_ini {m : ℕ} {x : Fin n} : x ∈ ini n m ↔ x.val < m := by simp [ini]

theorem card_ini {m : ℕ} (h : m ≤ n) : (ini n m).card = m := by
  rw [ini, Fin.card_filter_val_lt, min_eq_right h]

/-- A set of size `m` other than `[m]` is colex-larger than `[m]`. -/
theorem colex_ini_lt {m : ℕ} (hm : m ≤ n) {X : Finset (Fin n)} (hX : X.card = m)
    (hne : X ≠ ini n m) : toColex (ini n m) < toColex X := by
  have : ¬ X ⊆ ini n m := fun h =>
    hne (Finset.eq_of_subset_of_card_le h (by rw [card_ini hm, hX]))
  obtain ⟨a, haX, ha⟩ := Finset.not_subset.1 this
  rw [mem_ini, not_lt] at ha
  rw [Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt]
  refine ⟨a, haX, by simp [ha], fun b hb _ => ?_⟩
  rw [mem_ini] at hb
  exact Fin.lt_def.2 (lt_of_lt_of_le hb ha)

/-- For `j < m`, the smallest `(m-1)`-set avoiding `j` is `[m] - j`. -/
theorem colex_ini_erase_lt {m : ℕ} (hm : m ≤ n) {j : Fin n} (hj : j.val < m)
    {X : Finset (Fin n)} (hX : X.card = m - 1) (hjX : j ∉ X) (hne : X ≠ (ini n m).erase j) :
    toColex ((ini n m).erase j) < toColex X := by
  have hj' : j ∈ ini n m := mem_ini.2 hj
  have : ¬ X ⊆ ini n m := by
    intro h
    apply hne
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · exact mem_erase.2 ⟨fun h => hjX (h ▸ hx), h hx⟩
    · rw [card_erase_of_mem hj', card_ini hm, hX]
  obtain ⟨a, haX, ha⟩ := Finset.not_subset.1 this
  rw [mem_ini, not_lt] at ha
  rw [Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt]
  refine ⟨a, haX, fun h => by simp at h; omega, fun b hb _ => ?_⟩
  rw [mem_erase, mem_ini] at hb
  exact Fin.lt_def.2 (lt_of_lt_of_le hb.2 ha)

/-! ### The data of Proposition 6.2 -/

variable (k : ℕ)

/-- The set `T` of Proposition 6.2:
`T = {[k]} ∪ {[k-1] + i : k < i ≤ n} ∪ {([k] - j) + (k+1) : 1 ≤ j ≤ k-1}`
(paper indices; here shifted by one). -/
def Tset (hk : k < n) : Finset (Finset (Fin n)) :=
  {ini n k} ∪ (univ.filter (fun i : Fin n => k ≤ i.val)).image (fun i => insert i (ini n (k - 1)))
    ∪ (univ.filter (fun j : Fin n => j.val < k - 1)).image
        (fun j => insert ⟨k, hk⟩ ((ini n k).erase j))

/-- The set `S` of Proposition 6.2: the `k`-subsets not in `T`. -/
def Sset (hk : k < n) : Finset (Finset (Fin n)) :=
  (univ.powersetCard k).filter (· ∉ Tset k hk)

/-- `i = max s` (with a junk value for `s = ∅`). -/
def iOf (hk : k < n) (s : Finset (Fin n)) : Fin n :=
  if h : s.Nonempty then s.max' h else ⟨0, by omega⟩

/-- `B = s - i`. -/
def BOf (hk : k < n) (s : Finset (Fin n)) : Finset (Fin n) := s.erase (iOf k hk s)

/-- `W_s = [i-1] \ B`. -/
def Wof (hk : k < n) (s : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun x : Fin n => x < iOf k hk s) \ BOf k hk s

/-- The elements of `W_s` that are `≥ k` (paper indices). -/
def Whi (hk : k < n) (s : Finset (Fin n)) : Finset (Fin n) :=
  (Wof k hk s).filter (fun x : Fin n => k - 1 ≤ x.val)

/-- `j`: the least element of `W_s` that is `≥ k` if there is one, else `min W_s`. -/
def jOf (hk : k < n) (s : Finset (Fin n)) : Fin n :=
  if h : (Whi k hk s).Nonempty then (Whi k hk s).min' h
  else if h' : (Wof k hk s).Nonempty then (Wof k hk s).min' h' else iOf k hk s

/-- `B' = [k-1]` in the first case and `B' = [k] - j` in the second. -/
def BpOf (hk : k < n) (s : Finset (Fin n)) : Finset (Fin n) :=
  if (Whi k hk s).Nonempty then ini n (k - 1) else (ini n k).erase (jOf k hk s)

/-! ### Properties of `T` -/

theorem mem_Tset (hk : k < n) {X : Finset (Fin n)} :
    X ∈ Tset k hk ↔ X = ini n k ∨ (∃ i : Fin n, k ≤ i.val ∧ X = insert i (ini n (k - 1))) ∨
      ∃ j : Fin n, j.val < k - 1 ∧ X = insert ⟨k, hk⟩ ((ini n k).erase j) := by
  simp only [Tset, mem_union, mem_singleton, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ((h | ⟨i, hi, rfl⟩) | ⟨j, hj, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨i, hi, rfl⟩)
    · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
  · rintro (h | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨i, hi, rfl⟩)
    · exact Or.inr ⟨j, hj, rfl⟩

theorem card_filter_ge (hk : k ≤ n) : (univ.filter (fun i : Fin n => k ≤ i.val)).card = n - k := by
  have : univ.filter (fun i : Fin n => k ≤ i.val) = univ \ ini n k := by
    ext x; simp [ini]
  rw [this, card_univ_sdiff, card_ini hk, Fintype.card_fin]

theorem card_filter_lt' {m : ℕ} (hm : m ≤ n) : (univ.filter (fun i : Fin n => i.val < m)).card = m :=
  card_ini hm

/-- `T` consists of `n` subsets of size `k`. -/
theorem Tset_card (hk1 : 1 ≤ k) (hk : k < n) :
    (Tset k hk).card = n ∧ ∀ X ∈ Tset k hk, X.card = k := by
  set A : Finset (Finset (Fin n)) := {ini n k}
  set P := (univ.filter (fun i : Fin n => k ≤ i.val)).image (fun i => insert i (ini n (k - 1)))
  set Q := (univ.filter (fun j : Fin n => j.val < k - 1)).image
    (fun j => insert (⟨k, hk⟩ : Fin n) ((ini n k).erase j))
  have hT : Tset k hk = A ∪ P ∪ Q := rfl
  have hiP : ∀ i : Fin n, k ≤ i.val → i ∉ ini n (k - 1) := fun i hi h => by
    rw [mem_ini] at h; omega
  have hkQ : ∀ j : Fin n, (⟨k, hk⟩ : Fin n) ∉ (ini n k).erase j := fun j h => by
    rw [mem_erase, mem_ini] at h; exact lt_irrefl _ h.2
  have hcardP : P.card = n - k := by
    rw [card_image_of_injOn, card_filter_ge k hk.le]
    intro a ha b hb hab
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
    have : a ∈ insert b (ini n (k - 1)) := by
      simp only at hab; rw [← hab]; exact mem_insert_self a _
    rcases mem_insert.1 this with h | h
    · exact h
    · exact absurd h (hiP a ha)
  have hcardQ : Q.card = k - 1 := by
    rw [card_image_of_injOn, card_filter_lt' (by omega)]
    intro a ha b hb hab
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
    simp only at hab
    by_contra hne
    have hb' : b ∈ insert (⟨k, hk⟩ : Fin n) ((ini n k).erase a) :=
      mem_insert_of_mem (mem_erase.2 ⟨fun h => hne h.symm, mem_ini.2 (by omega)⟩)
    rw [hab] at hb'
    rcases mem_insert.1 hb' with h | h
    · rw [Fin.ext_iff] at h; simp at h; omega
    · simp at h
  have hAP : Disjoint A P := by
    rw [disjoint_singleton_left]
    simp only [P, mem_image, mem_filter, mem_univ, true_and, not_exists, not_and]
    intro i hi h
    have : i ∈ ini n k := h ▸ mem_insert_self i _
    rw [mem_ini] at this; omega
  have hAQ : Disjoint (A ∪ P) Q := by
    rw [disjoint_union_left]
    constructor
    · rw [disjoint_singleton_left]
      simp only [Q, mem_image, mem_filter, mem_univ, true_and, not_exists, not_and]
      intro j _ h
      have : (⟨k, hk⟩ : Fin n) ∈ ini n k := h ▸ mem_insert_self _ _
      rw [mem_ini] at this; exact lt_irrefl _ this
    · rw [Finset.disjoint_left]
      simp only [P, Q, mem_image, mem_filter, mem_univ, true_and, not_exists, not_and]
      rintro X ⟨i, hi, rfl⟩ j hj h
      -- `k - 1` lies in the `Q`-set but not in the `P`-set
      have hk1mem : (⟨k - 1, by omega⟩ : Fin n) ∈ insert (⟨k, hk⟩ : Fin n) ((ini n k).erase j) :=
        mem_insert_of_mem (mem_erase.2 ⟨fun h' => by rw [Fin.ext_iff] at h'; simp at h'; omega,
          mem_ini.2 (by simp; omega)⟩)
      rw [h] at hk1mem
      rcases mem_insert.1 hk1mem with h' | h'
      · -- then `i = k - 1 < k`, impossible
        rw [Fin.ext_iff] at h'; simp at h'; omega
      · rw [mem_ini] at h'; simp at h'
  refine ⟨?_, ?_⟩
  · rw [hT, card_union_of_disjoint hAQ, card_union_of_disjoint hAP, card_singleton, hcardP,
      hcardQ]
    omega
  · intro X hX
    rcases (mem_Tset k hk).1 hX with rfl | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · exact card_ini hk.le
    · rw [card_insert_of_notMem (hiP i hi), card_ini (by omega)]; omega
    · rw [card_insert_of_notMem (hkQ j), card_erase_of_mem (mem_ini.2 (by omega)),
        card_ini hk.le]
      omega

/-- **The data `i, j, B, B'` of Proposition 6.2.** For `s ∈ S`: `i = max s`, `B = s - i`,
`j ∉ B ∪ B'`, `j < i`, `i ∉ B'`, `|B| = |B'| = k - 1`, all elements of `B` and `B'` are `< i`,
and `B' ≺ B` (in particular `B ≠ B'`). -/
theorem S_data (hk1 : 1 ≤ k) (hk : k < n) {s : Finset (Fin n)} (hs : s ∈ Sset k hk) :
    let i := iOf k hk s
    let B := BOf k hk s
    let j := jOf k hk s
    let B' := BpOf k hk s
    s = insert i B ∧ i ∉ B ∧ B.card = k - 1 ∧ B'.card = k - 1 ∧ j < i ∧ j ∉ B ∧ j ∉ B' ∧
      i ∉ B' ∧ (∀ x ∈ B, x < i) ∧ (∀ x ∈ B', x < i) ∧ toColex B' < toColex B := by
  intro i B j B'
  simp only [Sset, mem_filter, mem_powersetCard, subset_univ, true_and] at hs
  obtain ⟨hcard, hT⟩ := hs
  have hne : s.Nonempty := by rw [← card_pos]; omega
  have hi : i = s.max' hne := dite_eq_left hne
  have hiS : i ∈ s := hi ▸ s.max'_mem hne
  have hsB : s = insert i B := (insert_erase hiS).symm
  have hiB : i ∉ B := notMem_erase i s
  have hBcard : B.card = k - 1 := by
    rw [show B = s.erase i from rfl, card_erase_of_mem hiS, hcard]
  have hBlt : ∀ x ∈ B, x < i := by
    intro x hx
    have hx : x ∈ s.erase i := hx
    rw [mem_erase] at hx
    exact lt_of_le_of_ne (hi ▸ s.le_max' x hx.2) hx.1
  have hik : k ≤ i.val := by
    by_contra h
    push Not at h
    apply hT
    rw [mem_Tset]
    left
    refine eq_of_subset_of_card_le (fun x hx => ?_) (by rw [card_ini hk.le, hcard])
    rw [mem_ini]
    have := hi ▸ s.le_max' x hx
    exact lt_of_le_of_lt (Fin.le_def.1 this) h
  -- `W_s`
  have hW : Wof k hk s = univ.filter (fun x : Fin n => x < i) \ B := rfl
  have hBsub : B ⊆ univ.filter (fun x : Fin n => x < i) := fun x hx => by
    simp [hBlt x hx]
  have hWcard : (Wof k hk s).card = i.val - (k - 1) := by
    rw [hW, card_sdiff_of_subset hBsub, hBcard]
    congr 1
    have : univ.filter (fun x : Fin n => x < i) = ini n i.val := by
      ext x; simp only [ini, mem_filter, mem_univ, true_and, Fin.lt_def]
    rw [this, card_ini i.isLt.le]
  have hWne : (Wof k hk s).Nonempty := by rw [← card_pos, hWcard]; omega
  have hWmem : ∀ {x}, x ∈ Wof k hk s → x < i ∧ x ∉ B := by
    intro x hx; rw [hW, mem_sdiff, mem_filter] at hx; exact ⟨hx.1.2, hx.2⟩
  -- the two cases
  have hcase : (j < i ∧ j ∉ B ∧ j ∉ B' ∧ B'.card = k - 1 ∧ toColex B' < toColex B) := by
    by_cases h : (Whi k hk s).Nonempty
    · have hj : j = (Whi k hk s).min' h := dite_eq_left h
      have hB' : B' = ini n (k - 1) := ite_eq_left h
      have hjW : j ∈ Whi k hk s := hj ▸ (Whi k hk s).min'_mem h
      rw [Whi, mem_filter] at hjW
      obtain ⟨hjlt, hjB⟩ := hWmem hjW.1
      refine ⟨hjlt, hjB, ?_, ?_, ?_⟩
      · rw [hB', mem_ini]; omega
      · rw [hB', card_ini (by omega)]
      · rw [hB']
        refine colex_ini_lt (by omega) hBcard fun hBe => hT ?_
        rw [mem_Tset]
        exact Or.inr (Or.inl ⟨i, hik, by rw [hsB, hBe]⟩)
    · have hj : j = (Wof k hk s).min' hWne := by
        simp only [j, jOf, dite_eq_right h, dite_eq_left hWne]
      have hB' : B' = (ini n k).erase j := ite_eq_right h
      have hjW : j ∈ Wof k hk s := hj ▸ (Wof k hk s).min'_mem hWne
      have hsmall : ∀ x ∈ Wof k hk s, x.val < k - 1 := by
        intro x hx
        by_contra hx'
        exact h ⟨x, by rw [Whi, mem_filter]; exact ⟨hx, by omega⟩⟩
      obtain ⟨hjlt, hjB⟩ := hWmem hjW
      have hjk := hsmall j hjW
      have hjini : j ∈ ini n k := mem_ini.2 (by omega)
      refine ⟨hjlt, hjB, by rw [hB']; exact notMem_erase j _, ?_, ?_⟩
      · rw [hB', card_erase_of_mem hjini, card_ini hk.le]
      · rw [hB']
        refine colex_ini_erase_lt hk.le (by omega) hBcard hjB fun hBe => hT ?_
        -- then `i = k`
        have hik' : i.val = k := by
          by_contra hne'
          have hx : (⟨k, hk⟩ : Fin n) ∈ Wof k hk s := by
            rw [hW, mem_sdiff, mem_filter, hBe]
            refine ⟨⟨mem_univ _, Fin.lt_def.2 (by simp; omega)⟩, ?_⟩
            rw [mem_erase, mem_ini]; simp
          have := hsmall _ hx
          simp at this; omega
        have hieq : i = ⟨k, hk⟩ := Fin.ext hik'
        rw [mem_Tset]
        exact Or.inr (Or.inr ⟨j, hjk, by rw [hsB, hBe, hieq]⟩)
  obtain ⟨hji, hjB, hjB', hB'card, hlex⟩ := hcase
  have hB'lt : ∀ x ∈ B', x < i := Finset.Colex.forall_lt_mono hlex.le hBlt
  exact ⟨hsB, hiB, hBcard, hB'card, hji, hjB, hjB', fun h => lt_irrefl i (hB'lt i h),
    hBlt, hB'lt, hlex⟩

end SquareBasis
