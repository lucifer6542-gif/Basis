module

public import SquareBasis.Minor

/-!
# Section 5 of the paper: circuits through a fixed element

Throughout, `P` is a connected matroid with at least two elements and `v ∈ E(P)`.

* `SetupS P v A B` : Setup (S) of the paper.
* `lemma51` : Lemma 5.1, `v ∈ cl(A) ∩ cl(B)`.
* `lemma52` : Lemma 5.2, every `g ∈ A ∩ cl(B)` is parallel to `v`.
* `prop53` : Proposition 5.3, `λ = 1`, by the minimal-counterexample argument of the paper.
* `thm45` : Theorem 4.5, the circuits through `v` link `E(P) - v` when `P / v` is connected.
-/

@[expose] public section

namespace SquareBasis

open Matroid Set

universe u

variable {α : Type u}

/-! ### Helpers -/

/-- If `C` is a circuit through `e` with `C - e ⊆ S`, then `e ∈ cl(S)`. -/
theorem rk_insert_eq_of_isCircuit {M : Matroid α} [M.Finite] {C S : Set α} {e : α}
    (hC : M.IsCircuit C) (he : e ∈ C) (hsub : C \ {e} ⊆ S) : rk M (insert e S) = rk M S := by
  have hfin : C.Finite := M.ground_finite.subset hC.subset_ground
  have hind : M.Indep (C \ {e}) := hC.ssubset_indep
    (ssubset_of_subset_of_ne sdiff_subset (fun h => by
      have : e ∈ C \ {e} := by rw [h]; exact he
      exact this.2 rfl))
  have h1 := rk_indep hind
  have h2 := rk_circuit_add_one hC
  have hc := Set.ncard_sdiff_singleton_add_one he hfin
  have hc' : ((C \ {e}).ncard : ℤ) + 1 = C.ncard := by exact_mod_cast hc
  have h3 := rk_submod M S C
  have e1 : S ∩ C = C \ {e} ∨ S ∩ C = C := by
    by_cases heS : e ∈ S
    · right; ext x; simp only [mem_inter_iff]
      constructor
      · exact fun h => h.2
      · intro hx
        by_cases hxe : x = e
        · exact ⟨hxe ▸ heS, hx⟩
        · exact ⟨hsub ⟨hx, hxe⟩, hx⟩
    · left; ext x; simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨hxS, hxC⟩; exact ⟨hxC, fun h => heS (h ▸ hxS)⟩
      · rintro ⟨hxC, hxe⟩; exact ⟨hsub ⟨hxC, hxe⟩, hxC⟩
  have e2 : S ∪ C = insert e S := by
    ext x; simp only [mem_union, mem_insert_iff]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · by_cases hxe : x = e
        · exact Or.inl hxe
        · exact Or.inr (hsub ⟨h, hxe⟩)
    · rintro (rfl | h)
      · exact Or.inr he
      · exact Or.inl h
  rw [e2] at h3
  have hmono := rk_mono M (subset_insert e S)
  have hmono2 := rk_mono M (show C \ {e} ⊆ C from sdiff_subset)
  rcases e1 with e1 | e1 <;> rw [e1] at h3 <;> linarith

/-- If `e ∉ I`, `I` is independent and `e ∈ cl(I)`, there is a circuit in `I + e` through `e`. -/
theorem exists_isCircuit_insert {M : Matroid α} [M.Finite] {I : Set α} {e : α}
    (hI : M.Indep I) (heI : e ∉ I) (he : e ∈ M.E) (hr : rk M (insert e I) = rk M I) :
    ∃ K, M.IsCircuit K ∧ K ⊆ insert e I ∧ e ∈ K := by
  have hsub : insert e I ⊆ M.E := insert_subset he hI.subset_ground
  have hdep : M.Dep (insert e I) := by
    refine ⟨fun hind => ?_, hsub⟩
    rw [indep_iff_rk hsub, hr, rk_indep hI,
      Set.ncard_insert_of_notMem heI (M.ground_finite.subset hI.subset_ground)] at hind
    push_cast at hind
    omega
  obtain ⟨K, hKs, hK⟩ := hdep.exists_isCircuit_subset
  refine ⟨K, hK, hKs, ?_⟩
  by_contra heK
  apply hK.dep.not_indep (hI.subset _)
  intro x hx
  rcases hKs hx with rfl | h
  · exact absurd hx heK
  · exact h

/-- Uniqueness of the circuit in `I + e`. -/
theorem isCircuit_insert_unique {M : Matroid α} {I K₁ K₂ : Set α} {e : α} (hI : M.Indep I)
    (hK₁ : M.IsCircuit K₁) (hK₂ : M.IsCircuit K₂) (h₁ : K₁ ⊆ insert e I)
    (h₂ : K₂ ⊆ insert e I) : K₁ = K₂ := by
  by_contra hne
  obtain ⟨K, hKs, hK⟩ := hK₁.elimination hK₂ hne e
  apply hK.dep.not_indep (hI.subset _)
  intro x hx
  obtain ⟨hx1, hx2⟩ := hKs hx
  rw [mem_singleton_iff] at hx2
  rcases hx1 with hx1 | hx1
  · rcases h₁ hx1 with h | h
    · exact absurd h hx2
    · exact h
  · rcases h₂ hx1 with h | h
    · exact absurd h hx2
    · exact h

theorem rk_insert_le (M : Matroid α) [M.Finite] (e : α) (S : Set α) :
    rk M (insert e S) ≤ rk M S + 1 := by
  have := rk_union_le M {e} S
  rw [singleton_union] at this
  have := rk_singleton_le M e
  linarith

/-- A set all of whose elements are coloops of it is independent. -/
theorem indep_of_forall_rk_sdiff_lt {M : Matroid α} [M.Finite] {A : Set α} (hA : A ⊆ M.E)
    (h : ∀ e ∈ A, rk M (A \ {e}) < rk M A) : M.Indep A := by
  by_contra hind
  obtain ⟨K, hKs, hK⟩ := (show M.Dep A from ⟨hind, hA⟩).exists_isCircuit_subset
  obtain ⟨e, he⟩ := hK.nonempty
  have := rk_insert_eq_of_isCircuit hK he (sdiff_subset_sdiff hKs subset_rfl)
  rw [insert_sdiff_singleton, insert_eq_of_mem (hKs he)] at this
  have := h e (hKs he)
  omega

/-! ### Setup (S) -/

/-- Setup (S) of the paper. -/
def SetupS (P : Matroid α) (v : α) (A B : Set α) : Prop :=
  A ∪ B = P.E \ {v} ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
    ∀ C, P.IsCircuit C → v ∈ C → C \ {v} ⊆ A ∨ C \ {v} ⊆ B

/-- `λ = r(A) + r(B) - r(X)`. -/
noncomputable def lam (P : Matroid α) (v : α) (A B : Set α) : ℤ :=
  rk P A + rk P B - rk P (P.E \ {v})

theorem SetupS.symm {P : Matroid α} {v : α} {A B : Set α} (h : SetupS P v A B) :
    SetupS P v B A := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by rw [union_comm]; exact h1, h2.symm, h4, h3, fun C hC hvC => (h5 C hC hvC).symm⟩

theorem SetupS.subset_left {P : Matroid α} {v : α} {A B : Set α} (h : SetupS P v A B) :
    A ⊆ P.E \ {v} := h.1 ▸ subset_union_left

theorem SetupS.subset_right {P : Matroid α} {v : α} {A B : Set α} (h : SetupS P v A B) :
    B ⊆ P.E \ {v} := h.1 ▸ subset_union_right

/-- A circuit through `v` meeting `A` has `C - v ⊆ A`. -/
theorem SetupS.sub_left {P : Matroid α} {v : α} {A B : Set α} (h : SetupS P v A B)
    {C : Set α} (hC : P.IsCircuit C) (hvC : v ∈ C) {a : α} (haC : a ∈ C) (haA : a ∈ A) :
    C \ {v} ⊆ A := by
  rcases h.2.2.2.2 C hC hvC with h' | h'
  · exact h'
  · have hav : a ≠ v := fun hav => (h.subset_left haA).2 (by rw [hav]; rfl)
    exact absurd (h' ⟨haC, hav⟩) (Set.disjoint_left.1 h.2.1 haA)

variable {P : Matroid α} [P.Finite] {v : α} {A B : Set α}

/-- **Lemma 5.1.** In Setup (S), `v ∈ cl(A) ∩ cl(B)`. -/
theorem lemma51 (hP : Conn P) (hv : v ∈ P.E) (hS : SetupS P v A B) :
    rk P (insert v A) = rk P A ∧ rk P (insert v B) = rk P B := by
  have side : ∀ {A' B' : Set α}, SetupS P v A' B' → rk P (insert v A') = rk P A' := by
    intro A' B' hS'
    obtain ⟨x, hx⟩ := hS'.2.2.1
    have hxX := hS'.subset_left hx
    obtain ⟨C, hC, hvC, hxC⟩ := conn_exists_isCircuit hP hv hxX.1
      (fun h => hxX.2 (by rw [← h]; rfl))
    exact rk_insert_eq_of_isCircuit hC hvC (hS'.sub_left hC hvC hxC hx)
  exact ⟨side hS, side hS.symm⟩

/-- **Lemma 5.2.** In Setup (S), every `g ∈ A ∩ cl(B)` is parallel to `v`, i.e. `{v, g}` is
a circuit. -/
theorem lemma52 (hP : Conn P) (hv : v ∈ P.E) (hS : SetupS P v A B) {g : α} (hgA : g ∈ A)
    (hgB : rk P (insert g B) = rk P B) : P.IsCircuit {v, g} := by
  have hgX := hS.subset_left hgA
  have hgv : g ≠ v := fun h => hgX.2 (by rw [h]; rfl)
  have hne : (P.E \ {v}).Nonempty := ⟨g, hgX⟩
  have hrv : rk P {v} = 1 := (conn_rk_facts hP hv hne).1
  have hBX := hS.subset_right
  have hdisj := hS.2.1
  -- a basis `I` of `B`
  obtain ⟨I, hI⟩ := P.exists_isBasis' B
  have hIB : I ⊆ B := hI.subset
  have hIind := hI.indep
  have hrI : rk P B = rk P I := by rw [rk_isBasis' hI, rk_indep hIind]
  have hvI : v ∉ I := fun h => (hBX (hIB h)).2 rfl
  have hgI : g ∉ I := fun h => Set.disjoint_left.1 hdisj hgA (hIB h)
  have hrvI : rk P (insert v I) = rk P I := by
    have h1 := (lemma51 hP hv hS).2
    have h2 := rk_mono P (insert_subset_insert hIB : insert v I ⊆ insert v B)
    have h3 := rk_mono P (subset_insert v I)
    linarith
  have hrgI : rk P (insert g I) = rk P I := by
    have h2 := rk_mono P (insert_subset_insert hIB : insert g I ⊆ insert g B)
    have h3 := rk_mono P (subset_insert g I)
    linarith
  -- fundamental circuits `C_I(v)` and `C_I(g)`
  obtain ⟨Cv, hCv, hCvs, hvCv⟩ := exists_isCircuit_insert hIind hvI hv hrvI
  obtain ⟨Cg, hCg, hCgs, hgCg⟩ := exists_isCircuit_insert hIind hgI hgX.1 hrgI
  -- a circuit `C` through `v` and `g`; `C - v ⊆ A`
  obtain ⟨C, hC, hvC, hgC⟩ := conn_exists_isCircuit hP hv hgX.1 hgv.symm
  have hCA : C \ {v} ⊆ A := hS.sub_left hC hvC hgC hgA
  have hvCg : v ∉ Cg := by
    intro h
    rcases hCgs h with h' | h'
    · exact hgv h'.symm
    · exact hvI h'
  -- strong circuit elimination of `g` from `C` and `C_I(g)`, keeping `v`
  obtain ⟨C', hC's, hC', hvC'⟩ := hC.strong_elimination hCg hgC hgCg hvC hvCg
  have hgC' : g ∉ C' := fun h => (hC's h).2 rfl
  have hC'B : C' \ {v} ⊆ B := by
    rcases hS.2.2.2.2 C' hC' hvC' with h | h
    · exfalso
      have hsub : C' ⊆ C := by
        intro y hy
        rcases (hC's hy).1 with h1 | h1
        · exact h1
        · by_cases hyv : y = v
          · exact hyv ▸ hvC
          · have hyA : y ∈ A := h ⟨hy, hyv⟩
            have hyI : y ∈ I := by
              rcases hCgs h1 with h2 | h2
              · exact absurd h2 (hC's hy).2
              · exact h2
            exact absurd (hIB hyI) (Set.disjoint_left.1 hdisj hyA)
      have := hC'.eq_of_subset_isCircuit hC hsub
      exact hgC' (this ▸ hgC)
    · exact h
  -- hence `C' ⊆ I + v`, so `C' = C_I(v)` and `D_v ⊆ D_g`
  have hC'sub : C' ⊆ insert v I := by
    intro y hy
    by_cases hyv : y = v
    · exact Or.inl hyv
    · right
      have hyB : y ∈ B := hC'B ⟨hy, hyv⟩
      rcases (hC's hy).1 with h1 | h1
      · exact absurd (hCA ⟨h1, hyv⟩) (Set.disjoint_right.1 hdisj hyB)
      · rcases hCgs h1 with h2 | h2
        · exact absurd h2 (hC's hy).2
        · exact h2
  have hCvC' : Cv = C' := isCircuit_insert_unique hIind hCv hC' hCvs hC'sub
  have hDv : ∀ y ∈ Cv, y ≠ v → y ∈ Cg ∧ y ≠ g := by
    intro y hy hyv
    rw [hCvC'] at hy
    have hyB : y ∈ B := hC'B ⟨hy, hyv⟩
    rcases (hC's hy).1 with h1 | h1
    · exact absurd (hCA ⟨h1, hyv⟩) (Set.disjoint_right.1 hdisj hyB)
    · exact ⟨h1, (hC's hy).2⟩
  -- choose `x ∈ D_v`
  obtain ⟨x, hxCv, hxv⟩ : ∃ x ∈ Cv, x ≠ v := by
    by_contra hcon
    push Not at hcon
    have hCv1 : Cv = {v} := by
      ext y; simp only [mem_singleton_iff]
      exact ⟨fun hy => hcon y hy, fun hy => hy ▸ hvCv⟩
    have := rk_circuit_add_one hCv
    rw [hCv1, hrv, ncard_singleton] at this
    norm_num at this
  have hxI : x ∈ I := by
    rcases hCvs hxCv with h | h
    · exact absurd h hxv
    · exact h
  obtain ⟨hxCg, hxg⟩ := hDv x hxCv hxv
  -- `I' = I - x + g` is independent
  set I' := insert g (I \ {x}) with hI'
  have hI'ind : P.Indep I' := by
    by_contra hdep
    have hsub : I' ⊆ P.E := insert_subset hgX.1 (sdiff_subset.trans hIind.subset_ground)
    obtain ⟨K, hKs, hK⟩ := (show P.Dep I' from ⟨hdep, hsub⟩).exists_isCircuit_subset
    have hKsub : K ⊆ insert g I := hKs.trans (insert_subset_insert sdiff_subset)
    have := isCircuit_insert_unique hIind hK hCg hKsub hCgs
    rw [← this] at hxCg
    rcases hKs hxCg with h | h
    · exact hxg h
    · exact h.2 rfl
  have hfinI : I.Finite := P.ground_finite.subset hIind.subset_ground
  have hcardI' : I'.ncard = I.ncard := by
    have hgIx : g ∉ I \ {x} := fun h => hgI (mem_of_mem_sdiff h)
    rw [hI', Set.ncard_insert_of_notMem hgIx (hfinI.subset sdiff_subset)]
    exact Set.ncard_sdiff_singleton_add_one hxI hfinI
  have hvI' : v ∉ I' := by
    rintro (h | h)
    · exact hgv h.symm
    · exact hvI h.1
  -- `cl(I') = cl(I) ∋ v`
  have hrvI' : rk P (insert v I') = rk P I' := by
    have h1 : rk P (insert v (insert g I)) = rk P (insert g I) :=
      rk_insert_eq_of_isCircuit hCv hvCv (fun y hy => by
        rcases hCvs hy.1 with h | h
        · exact absurd h hy.2
        · exact Or.inr h)
    have h2 := rk_mono P (insert_subset_insert (insert_subset_insert sdiff_subset) :
      insert v I' ⊆ insert v (insert g I))
    have h3 := rk_mono P (subset_insert v I')
    have h4 := rk_indep hI'ind
    have h5 := rk_indep hIind
    rw [hcardI'] at h4
    linarith
  obtain ⟨C'', hC'', hC''s, hvC''⟩ := exists_isCircuit_insert hI'ind hvI' hv hrvI'
  -- `g ∈ C''`
  have hgC'' : g ∈ C'' := by
    by_contra hg
    have hsub : C'' ⊆ insert v I := by
      intro y hy
      rcases hC''s hy with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hy) hg
      · exact Or.inr h.1
    have := isCircuit_insert_unique hIind hC'' hCv hsub hCvs
    rw [← this] at hxCv
    rcases hC''s hxCv with h | h | h
    · exact hxv h
    · exact hxg h
    · exact h.2 rfl
  have hC''A : C'' \ {v} ⊆ A := hS.sub_left hC'' hvC'' hgC'' hgA
  have hC''eq : C'' = {v, g} := by
    ext y; simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · intro hy
      by_cases hyv : y = v
      · exact Or.inl hyv
      · right
        rcases hC''s hy with h | h | h
        · exact absurd h hyv
        · exact h
        · exact absurd (hIB h.1) (Set.disjoint_left.1 hdisj (hC''A ⟨hy, hyv⟩))
    · rintro (rfl | rfl)
      · exact hvC''
      · exact hgC''
  exact hC''eq ▸ hC''

/-! ### Proposition 5.3 -/

theorem lam_symm (P : Matroid α) (v : α) (A B : Set α) : lam P v A B = lam P v B A := by
  unfold lam; omega

/-- Observation (1) of the paper for contraction: Setup (S) passes to `P ／ e`. -/
theorem SetupS.contract {P : Matroid α} {v e : α} {A B : Set α} (hS : SetupS P v A B)
    (heA : e ∈ A) (hA : (A \ {e}).Nonempty) : SetupS (P ／ {e}) v (A \ {e}) B := by
  obtain ⟨h1, h2, -, h4, h5⟩ := hS
  have heB : e ∉ B := fun h => Set.disjoint_left.1 h2 heA h
  refine ⟨?_, h2.mono_left sdiff_subset, hA, h4, ?_⟩
  · rw [contract_ground]
    ext x
    have hx := congrArg (fun S => x ∈ S) h1
    simp only [mem_union, mem_sdiff, mem_singleton_iff, eq_iff_iff] at hx ⊢
    by_cases hxe : x = e
    · subst hxe; simp only [heB, false_or, not_true_eq_false, and_false, false_and]
    · tauto
  · intro D hD hvD
    obtain ⟨C', hC', hDC', hC'D⟩ := hD.exists_subset_isCircuit_of_contract
    have heD : e ∉ D := fun h => (hD.subset_ground h).2 rfl
    rcases h5 C' hC' (hDC' hvD) with h | h
    · left
      intro x hx
      exact ⟨h ⟨hDC' hx.1, hx.2⟩, fun hxe => heD (by rw [mem_singleton_iff] at hxe; exact hxe ▸ hx.1)⟩
    · right
      intro x hx
      exact h ⟨hDC' hx.1, hx.2⟩

/-- Observation (1) of the paper for deletion: Setup (S) passes to `P ＼ e`. -/
theorem SetupS.delete {P : Matroid α} {v e : α} {A B : Set α} (hS : SetupS P v A B)
    (heA : e ∈ A) (hA : (A \ {e}).Nonempty) : SetupS (P ＼ {e}) v (A \ {e}) B := by
  obtain ⟨h1, h2, -, h4, h5⟩ := hS
  have heB : e ∉ B := fun h => Set.disjoint_left.1 h2 heA h
  refine ⟨?_, h2.mono_left sdiff_subset, hA, h4, ?_⟩
  · rw [delete_ground]
    ext x
    have hx := congrArg (fun S => x ∈ S) h1
    simp only [mem_union, mem_sdiff, mem_singleton_iff, eq_iff_iff] at hx ⊢
    by_cases hxe : x = e
    · subst hxe; simp only [heB, false_or, not_true_eq_false, and_false, false_and]
    · tauto
  · intro D hD hvD
    rw [delete_isCircuit_iff] at hD
    obtain ⟨hD, hDe⟩ := hD
    rcases h5 D hD hvD with h | h
    · left
      intro x hx
      exact ⟨h hx, fun hxe => Set.disjoint_left.1 hDe hx.1 hxe⟩
    · right; exact h

/-- **Proposition 5.3.** In Setup (S), `λ = 1`. The proof is the minimal-counterexample
argument of the paper (induction on `|E(P)|`). -/
theorem prop53 : ∀ (n : ℕ) (P : Matroid α) [P.Finite] (v : α) (A B : Set α),
    P.E.ncard = n → Conn P → v ∈ P.E → SetupS P v A B → lam P v A B = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P _ v A B hn hP hv hS
  have hAX := hS.subset_left
  have hBX := hS.subset_right
  have hne : (P.E \ {v}).Nonempty := hS.2.2.1.mono hAX
  obtain ⟨hrv, hrX⟩ := conn_rk_facts hP hv hne
  obtain ⟨h51A, h51B⟩ := lemma51 hP hv hS
  -- `λ ≥ 1`
  have hge : 1 ≤ lam P v A B := by
    have h := rk_submod P (insert v A) (insert v B)
    have e1 : insert v A ∩ insert v B = {v} := by
      ext x; simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        rcases h1 with h1 | h1
        · exact h1
        rcases h2 with h2 | h2
        · exact h2
        exact absurd h2 (Set.disjoint_left.1 hS.2.1 h1)
      · intro h; exact ⟨Or.inl h, Or.inl h⟩
    have e2 : insert v A ∪ insert v B = P.E := by
      rw [← insert_union_distrib, hS.1, insert_sdiff_singleton, insert_eq_of_mem hv]
    rw [e1, e2] at h
    unfold lam
    linarith
  -- `λ ≤ 1` by a minimal counterexample
  by_contra hne1
  have hlam2 : 2 ≤ lam P v A B := by omega
  -- Step 1 (for either orientation of the setup)
  have step1 : ∀ {A' B' : Set α}, SetupS P v A' B' → lam P v A' B' = lam P v A B →
      ∀ e ∈ A', (A' \ {e}).Nonempty ∧ ¬ Conn (P ／ {e}) ∧ rk P (A' \ {e}) < rk P A' := by
    intro A' B' hS' hlam e heA
    have heX := hS'.subset_left heA
    have he : e ∈ P.E := heX.1
    have hev : e ≠ v := fun h => heX.2 (by rw [h]; rfl)
    have heB : e ∉ B' := fun h => Set.disjoint_left.1 hS'.2.1 heA h
    have hre : rk P {e} = 1 := (conn_rk_facts hP he ⟨v, hv, fun h => hev (by
      rw [mem_singleton_iff] at h; exact h.symm)⟩).1
    -- `|A'| ≥ 2`
    have hA'e : (A' \ {e}).Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty] at hemp
      have hsub : A' ⊆ {e} := sdiff_eq_empty.1 hemp
      have h1 := rk_mono P hsub
      have h2 := rk_singleton_le P e
      have h3 := rk_mono P hS'.subset_right
      have : lam P v A' B' ≤ 1 := by unfold lam; linarith
      omega
    have hSc := hS'.contract heA hA'e
    have hSd := hS'.delete heA hA'e
    have hvc : v ∈ (P ／ {e}).E := ⟨hv, fun h => hev (by rw [mem_singleton_iff] at h; exact h.symm)⟩
    have hvd : v ∈ (P ＼ {e}).E := hvc
    have hnc : (P ／ {e}).E.ncard < n := by
      rw [contract_ground, ← hn]; exact Set.ncard_sdiff_singleton_lt_of_mem he P.ground_finite
    have hnd : (P ＼ {e}).E.ncard < n := by
      rw [delete_ground, ← hn]; exact Set.ncard_sdiff_singleton_lt_of_mem he P.ground_finite
    -- rank formulas in `P ／ e` (observation (2))
    have hEe : (P.E \ {e}) \ {v} ⊆ P.E \ {e} := sdiff_subset
    have hA'sub : A' \ {e} ⊆ P.E \ {e} := fun x hx => ⟨(hS'.subset_left hx.1).1, hx.2⟩
    have hB'sub : B' ⊆ P.E \ {e} := fun x hx => ⟨(hS'.subset_right hx).1,
      fun h => heB (by rw [mem_singleton_iff] at h; exact h ▸ hx)⟩
    have hlamc : lam (P ／ {e}) v (A' \ {e}) B' =
        rk P A' + rk P (insert e B') - rk P (P.E \ {v}) - 1 := by
      unfold lam
      rw [contract_ground, rk_contract_elem P he hA'sub, rk_contract_elem P he hB'sub,
        rk_contract_elem P he hEe, hre, insert_sdiff_singleton, insert_eq_of_mem heA]
      have : insert e ((P.E \ {e}) \ {v}) = P.E \ {v} := by
        ext x; simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff]
        constructor
        · rintro (rfl | ⟨⟨hx, -⟩, hxv⟩)
          · exact ⟨he, hev⟩
          · exact ⟨hx, hxv⟩
        · rintro ⟨hx, hxv⟩
          by_cases hxe : x = e
          · exact Or.inl hxe
          · exact Or.inr ⟨⟨hx, hxe⟩, hxv⟩
      rw [this]
      omega
    -- (i) `P ／ e` is not connected
    have hnotc : ¬ Conn (P ／ {e}) := by
      by_cases hpar : P.IsCircuit {v, e}
      · intro hN
        have hrv' : rk (P ／ {e}) {v} = 0 := by
          rw [rk_contract_elem P he (singleton_subset_iff.2 hvc), hre]
          have := rk_circuit_add_one hpar
          rw [Set.pair_comm] at this
          rw [Set.ncard_pair hev] at this
          have e1 : insert e ({v} : Set α) = {e, v} := rfl
          rw [e1]
          push_cast at this
          linarith
        have hsplit : rk (P ／ {e}) {v} + rk (P ／ {e}) ((P ／ {e}).E \ {v}) =
            rk (P ／ {e}) (P ／ {e}).E := by
          have h1 := rk_union_le (P ／ {e}) {v} ((P ／ {e}).E \ {v})
          rw [union_sdiff_cancel (singleton_subset_iff.2 hvc)] at h1
          have h2 := rk_mono (P ／ {e}) (show (P ／ {e}).E \ {v} ⊆ (P ／ {e}).E from sdiff_subset)
          linarith
        rcases hN {v} (singleton_subset_iff.2 hvc) hsplit with h | h
        · exact (singleton_nonempty v).ne_empty h
        · obtain ⟨b, hb⟩ := hS'.2.2.2.1
          have hbE : b ∈ (P ／ {e}).E :=
            ⟨(hS'.subset_right hb).1, fun h => heB (by rw [mem_singleton_iff] at h; exact h ▸ hb)⟩
          rw [← h] at hbE
          exact (hS'.subset_right hb).2 hbE
      · have hnot : rk P (insert e B') ≠ rk P B' := fun h => hpar (lemma52 hP hv hS' heA h)
        have h1 := rk_insert_le P e B'
        have h2 := rk_mono P (subset_insert e B')
        intro hN
        have := ih _ hnc (P ／ {e}) v (A' \ {e}) B' rfl hN hvc hSc
        rw [hlamc] at this
        have : lam P v A' B' = 1 := by unfold lam; omega
        omega
    refine ⟨hA'e, hnotc, ?_⟩
    -- (ii) `e` is a coloop of `P | A'`
    have hd : Conn (P ＼ {e}) := by
      rcases tutte_minor hP he ⟨v, hv, fun h => hev (by
        rw [mem_singleton_iff] at h; exact h.symm)⟩ with h | h
      · exact h
      · exact absurd h hnotc
    have hlamd := ih _ hnd (P ＼ {e}) v (A' \ {e}) B' rfl hd hvd hSd
    unfold lam at hlamd
    rw [delete_ground, rk_delete P {e} hA'sub, rk_delete P {e} hB'sub,
      rk_delete P {e} hEe] at hlamd
    by_contra hlt
    have hle := rk_mono P (show A' \ {e} ⊆ A' from sdiff_subset)
    have heq : rk P (A' \ {e}) = rk P A' := by omega
    have h3 := rk_submod P ((P.E \ {e}) \ {v}) A'
    have e1 : ((P.E \ {e}) \ {v}) ∩ A' = A' \ {e} := by
      ext x; simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨⟨⟨-, hxe⟩, -⟩, hx⟩; exact ⟨hx, hxe⟩
      · rintro ⟨hx, hxe⟩
        exact ⟨⟨⟨(hS'.subset_left hx).1, hxe⟩, (hS'.subset_left hx).2⟩, hx⟩
    have e2 : ((P.E \ {e}) \ {v}) ∪ A' = P.E \ {v} := by
      ext x; simp only [mem_union, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro (⟨⟨hx, -⟩, hxv⟩ | hx)
        · exact ⟨hx, hxv⟩
        · exact hS'.subset_left hx
      · rintro ⟨hx, hxv⟩
        by_cases hxe : x = e
        · exact Or.inr (hxe ▸ heA)
        · exact Or.inl ⟨⟨hx, hxe⟩, hxv⟩
    rw [e1, e2] at h3
    have h4 := rk_mono P (show (P.E \ {e}) \ {v} ⊆ P.E \ {v} from fun x hx => ⟨hx.1.1, hx.2⟩)
    have : lam P v A' B' = 1 := by unfold lam; linarith
    omega
  -- `A` is independent
  have hAind : P.Indep A :=
    indep_of_forall_rk_sdiff_lt (hAX.trans sdiff_subset) (fun e he => (step1 hS rfl e he).2.2)
  -- Step 2: choose `e ∈ A` not parallel to `v`
  obtain ⟨a, ha⟩ := hS.2.2.1
  obtain ⟨a', ha'A, ha'a⟩ := (step1 hS rfl a ha).1
  have ha'a' : a' ≠ a := fun h => ha'a (by rw [mem_singleton_iff]; exact h)
  obtain ⟨e, heA, hpar⟩ : ∃ e ∈ A, ¬ P.IsCircuit {v, e} := by
    by_contra hcon
    push Not at hcon
    have h1 := hcon a ha
    have h2 := hcon a' ha'A
    have hne' : ({v, a} : Set α) ≠ {v, a'} := by
      intro h
      have : a ∈ ({v, a'} : Set α) := h ▸ (Or.inr rfl : a ∈ ({v, a} : Set α))
      rcases this with h' | h'
      · exact (hAX ha).2 (by rw [h']; rfl)
      · exact ha'a' (by rw [mem_singleton_iff] at h'; exact h'.symm)
    obtain ⟨K, hKs, hK⟩ := h1.elimination h2 hne' v
    apply hK.dep.not_indep (hAind.subset _)
    intro x hx
    obtain ⟨hx1, hx2⟩ := hKs hx
    rw [mem_singleton_iff] at hx2
    rcases hx1 with (h | h) | (h | h)
    · exact absurd h hx2
    · rw [mem_singleton_iff] at h; exact h ▸ ha
    · exact absurd h hx2
    · rw [mem_singleton_iff] at h; exact h ▸ ha'A
  obtain ⟨-, hNe, -⟩ := step1 hS rfl e heA
  have heX := hAX heA
  have he : e ∈ P.E := heX.1
  have hev : e ≠ v := fun h => heX.2 (by rw [h]; rfl)
  have heB : e ∉ B := fun h => Set.disjoint_left.1 hS.2.1 heA h
  have hre : rk P {e} = 1 := (conn_rk_facts hP he ⟨v, hv, fun h => hev (by
      rw [mem_singleton_iff] at h; exact h.symm)⟩).1
  set N := P ／ {e} with hNdef
  have hNE : N.E = P.E \ {e} := contract_ground P {e}
  have hvN : v ∈ N.E := by
    rw [hNE]; exact ⟨hv, fun h => hev (by rw [mem_singleton_iff] at h; exact h.symm)⟩
  set W := circuitClass N N.E v with hW
  set R := N.E \ W with hR
  have hsplit := circuitClass_split (M := N) hvN
  have hvW : v ∈ W := ⟨hvN, Or.inl rfl⟩
  -- `R` is nonempty, because `P ／ e` is not connected
  have hRne : R.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    apply hNe
    apply conn_of_forall_isCircuit hvN
    intro y hy
    have hyW : y ∈ W := by
      by_contra hyW
      have : y ∈ R := ⟨hy, hyW⟩
      rw [hemp] at this
      exact this
    rcases hyW.2 with h | ⟨K, hK, -, hvK, hyK⟩
    · exact Or.inl h
    · exact Or.inr ⟨K, hK, hvK, hyK⟩
  -- `R ⊆ A - e`
  have hRA : R ⊆ A \ {e} := by
    intro y hy
    have hyE' : y ∈ N.E := hy.1
    have hyE : y ∈ P.E := (hNE ▸ hyE').1
    have hye : y ≠ e := fun h => (hNE ▸ hyE').2 (by rw [h]; rfl)
    have hyv : y ≠ v := fun h => hy.2 (h ▸ hvW)
    obtain ⟨C, hC, hvC, hyC⟩ := conn_exists_isCircuit hP hv hyE hyv.symm
    have notW : ∀ K, N.IsCircuit K → v ∈ K → y ∈ K → False := by
      intro K hK hvK hyK
      exact hy.2 ⟨hyE', Or.inr ⟨K, hK, hK.subset_ground, hvK, hyK⟩⟩
    by_cases heC : e ∈ C
    · have hnt : C.Nontrivial := ⟨v, hvC, y, hyC, hyv.symm⟩
      exact (notW _ (hC.contractElem_isCircuit hnt heC) ⟨hvC, fun h => hev (by
        rw [mem_singleton_iff] at h; exact h.symm)⟩ ⟨hyC, fun h => hye (by
        rw [mem_singleton_iff] at h; exact h)⟩).elim
    have hcl : rk P (insert e C) = rk P C := by
      by_contra hne'
      have h1 := rk_insert_le P e C
      have h2 := rk_mono P (subset_insert e C)
      exact notW C (contract_isCircuit_of_rk hC he heC (by omega) hre) hvC hyC
    rcases hS.2.2.2.2 C hC hvC with hCA | hCB
    · exact ⟨hCA ⟨hyC, hyv⟩, fun h => hye (by rw [mem_singleton_iff] at h; exact h)⟩
    · exfalso
      apply hpar
      apply lemma52 hP hv hS heA
      set S := insert v B with hSdef
      have hCS : C ⊆ S := by
        intro x hx
        by_cases hxv : x = v
        · exact Or.inl hxv
        · exact Or.inr (hCB ⟨hx, hxv⟩)
      have heS : e ∉ S := by
        rintro (h | h)
        · exact hev h
        · exact heB h
      have h1 := rk_submod P (insert e C) S
      have e1 : insert e C ∩ S = C := by
        ext x; simp only [mem_inter_iff, mem_insert_iff]
        constructor
        · rintro ⟨rfl | hx, hxS⟩
          · exact absurd hxS heS
          · exact hx
        · intro hx; exact ⟨Or.inr hx, hCS hx⟩
      have e2 : insert e C ∪ S = insert e S := by
        ext x; simp only [mem_union, mem_insert_iff]
        constructor
        · rintro ((rfl | hx) | hx)
          · exact Or.inl rfl
          · exact Or.inr (hCS hx)
          · exact Or.inr hx
        · rintro (rfl | hx)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr hx
      rw [e1, e2] at h1
      have h2 := rk_mono P (show insert e B ⊆ insert e S from
        insert_subset_insert (subset_insert v B))
      have h3 := rk_mono P (subset_insert e B)
      linarith
  -- ranks in `P ／ e`
  have hRE : R ⊆ P.E \ {e} := hNE ▸ (sdiff_subset : R ⊆ N.E)
  have hWE : W ⊆ P.E \ {e} := hNE ▸ (fun x hx => hx.1 : W ⊆ N.E)
  have heR : e ∉ R := fun h => (hRE h).2 rfl
  have hfinR : R.Finite := P.ground_finite.subset (hRE.trans sdiff_subset)
  have hrR : rk N R = R.ncard := by
    rw [rk_contract_elem P he hRE, hre]
    have hind : P.Indep (insert e R) := hAind.subset (insert_subset heA (hRA.trans sdiff_subset))
    rw [rk_indep hind, Set.ncard_insert_of_notMem heR hfinR]
    push_cast; omega
  have hrW : rk N W = rk P (insert e W) - 1 := by rw [rk_contract_elem P he hWE, hre]
  have hrNE : rk N N.E = rk P P.E - 1 := by
    rw [hNE, rk_contract_elem P he subset_rfl, hre, insert_sdiff_singleton,
      insert_eq_of_mem he]
  rw [hrR, hrW, hrNE] at hsplit
  have heW : insert e W = P.E \ R := by
    ext x; simp only [mem_insert_iff, mem_sdiff]
    constructor
    · rintro (rfl | hx)
      · exact ⟨he, heR⟩
      · exact ⟨(hWE hx).1, fun h => h.2 hx⟩
    · rintro ⟨hx, hxR⟩
      by_cases hxe : x = e
      · exact Or.inl hxe
      · right
        by_contra hxW
        exact hxR ⟨by rw [hNE]; exact ⟨hx, hxe⟩, hxW⟩
  rw [heW] at hsplit
  -- every element of `R` is a coloop of `P`, a contradiction
  obtain ⟨x, hxR⟩ := hRne
  have hxE : x ∈ P.E := (hRE hxR).1
  have hxv : x ≠ v := fun h => hxR.2 (h ▸ hvW)
  have hcol := (conn_rk_facts hP hxE ⟨v, hv, fun h => hxv (by
    rw [mem_singleton_iff] at h; exact h.symm)⟩).2
  have hu := rk_union_le P (P.E \ R) (R \ {x})
  have e1 : (P.E \ R) ∪ (R \ {x}) = P.E \ {x} := by
    ext y; simp only [mem_union, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro (⟨hy, hyR⟩ | ⟨hyR, hyx⟩)
      · exact ⟨hy, fun h => hyR (h ▸ hxR)⟩
      · exact ⟨(hRE hyR).1, hyx⟩
    · rintro ⟨hy, hyx⟩
      by_cases hyR : y ∈ R
      · exact Or.inr ⟨hyR, hyx⟩
      · exact Or.inl ⟨hy, hyR⟩
  rw [e1] at hu
  have hrk := rk_le_ncard P (hfinR.subset (sdiff_subset : R \ {x} ⊆ R))
  have hc := Set.ncard_sdiff_singleton_add_one hxR hfinR
  have hc' : ((R \ {x}).ncard : ℤ) + 1 = R.ncard := by exact_mod_cast hc
  linarith

/-! ### Theorem 4.5 -/

/-- The edge relation of the graph on `E(P) - v`: `x ~ y` if `x, y ≠ v` and some circuit of `P`
contains `v`, `x` and `y`. -/
def Linked (P : Matroid α) (v x y : α) : Prop :=
  x ≠ v ∧ y ≠ v ∧ ∃ C, P.IsCircuit C ∧ v ∈ C ∧ x ∈ C ∧ y ∈ C

/-- **Theorem 4.5.** Let `P` be connected with at least two elements and `v ∈ E(P)`. If
`P ／ v` is connected, the graph on `E(P) - v` in which `x ~ y` whenever some circuit of `P`
contains `v`, `x` and `y` is connected. -/
theorem thm45 (hP : Conn P) (hv : v ∈ P.E) (hPv : Conn (P ／ {v})) :
    ∀ x ∈ P.E \ {v}, ∀ y ∈ P.E \ {v}, Relation.ReflTransGen (Linked P v) x y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, y, hy, hxy⟩ := hcon
  set A := {z | z ∈ P.E \ {v} ∧ Relation.ReflTransGen (Linked P v) x z} with hA
  set B := (P.E \ {v}) \ A with hB
  have hxA : x ∈ A := ⟨hx, Relation.ReflTransGen.refl⟩
  have hyB : y ∈ B := ⟨hy, fun h => hxy h.2⟩
  have hS : SetupS P v A B := by
    refine ⟨?_, ?_, ⟨x, hxA⟩, ⟨y, hyB⟩, ?_⟩
    · have hAsub : A ⊆ P.E \ {v} := fun z hz => by rw [hA] at hz; exact hz.1
      rw [hB, union_sdiff_cancel hAsub]
    · rw [Set.disjoint_left]; intro z hzA hzB; exact hzB.2 hzA
    · intro C hC hvC
      by_cases hmeet : ∃ a ∈ C \ {v}, a ∈ A
      · obtain ⟨a, haC, haA⟩ := hmeet
        left
        intro c hc
        have hcX : c ∈ P.E \ {v} := ⟨hC.subset_ground hc.1, hc.2⟩
        have hav : a ≠ v := fun h => haC.2 (by rw [h]; rfl)
        have hcv : c ≠ v := fun h => hc.2 (by rw [h]; rfl)
        exact ⟨hcX, haA.2.tail ⟨hav, hcv, C, hC, hvC, haC.1, hc.1⟩⟩
      · right
        push Not at hmeet
        intro c hc
        exact ⟨⟨hC.subset_ground hc.1, hc.2⟩, hmeet c hc⟩
  have hlam := prop53 _ P v A B rfl hP hv hS
  obtain ⟨h51A, h51B⟩ := lemma51 hP hv hS
  have hne : (P.E \ {v}).Nonempty := ⟨x, hx⟩
  obtain ⟨hrv, hrX⟩ := conn_rk_facts hP hv hne
  have hAX := hS.subset_left
  have hBX := hS.subset_right
  have hNE : (P ／ {v}).E = P.E \ {v} := contract_ground P {v}
  have hsplit : rk (P ／ {v}) A + rk (P ／ {v}) ((P ／ {v}).E \ A) = rk (P ／ {v}) (P ／ {v}).E := by
    rw [hNE, show (P.E \ {v}) \ A = B from rfl, rk_contract_elem P hv hAX,
      rk_contract_elem P hv hBX, rk_contract_elem P hv subset_rfl, h51A, h51B, hrv,
      insert_sdiff_singleton, insert_eq_of_mem hv]
    unfold lam at hlam
    linarith
  rcases hPv A (hNE ▸ hAX) hsplit with h | h
  · rw [h] at hxA; exact hxA
  · have : y ∈ A := by rw [h, hNE]; exact hy
    exact hyB.2 this

end SquareBasis
