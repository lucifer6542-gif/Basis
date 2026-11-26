module

public import SquareBasis.LinAlg

/-!
# Potentials on a spanning forest

The proof of Theorem 7.4(a) chooses `σ` with prescribed differences `σ_a - σ_b` along the edges
of a spanning forest ("fix `σ` at one vertex of each tree and propagate along the tree").
-/

@[expose] public section

namespace SquareBasis

open Set

/-- Values on the parent edges of a forest (parents have smaller depth) can be realized as
differences of a potential. -/
theorem exists_potential {V G : Type*} [AddCommGroup G] (d : V → ℕ) (N : Set V) (p : N → V)
    (hpd : ∀ a : N, d (p a) < d a.1) (g : N → G) :
    ∃ σ : V → G, ∀ a : N, σ a.1 - σ (p a) = g a := by
  classical
  let F : ∀ a : V, (∀ b : V, d b < d a → G) → G := fun a rec =>
    if h : a ∈ N then rec (p ⟨a, h⟩) (hpd ⟨a, h⟩) + g ⟨a, h⟩ else 0
  let σ : V → G := (InvImage.wf d Nat.lt_wfRel.wf).fix F
  refine ⟨σ, fun a => ?_⟩
  have h := (InvImage.wf d Nat.lt_wfRel.wf).fix_eq F a.1
  have : σ a.1 = σ (p a) + g a := by
    have h' : σ a.1 = F a.1 (fun b _ => σ b) := h
    rw [h']
    simp only [F, a.2, ↓reduceDIte]
  rw [this]; abel

/-- **Spanning forest, with potentials** (the forest of `forest_basis`; in addition, values on
the edges can be prescribed as differences `σ_a - σ_{p(a)}`, by propagating along the trees). For a symmetric relation on a finite set there are non-root vertices
`N` and parents `p` such that the vectors `e_a - e_{p(a)}` (`a ∈ N`) are linearly independent
and span every edge vector `e_a - e_b`. -/
theorem forest_basis_pot {V : Type*} [Finite V] (Adj : V → V → Prop) (hsymm : ∀ a b, Adj a b → Adj b a) :
    ∃ (N : Set V) (p : N → V), (∀ a, Adj (p a) a.1) ∧
      LinearIndependent ℤ (fun a : N => Finsupp.single a.1 (1 : ℤ) - Finsupp.single (p a) 1) ∧
      (∀ a b, Adj a b → Finsupp.single a (1 : ℤ) - Finsupp.single b 1 ∈
        Submodule.span ℤ (range (fun a : N => Finsupp.single a.1 (1 : ℤ) - Finsupp.single (p a) 1))) ∧
      ∀ (G : Type) [AddCommGroup G] (g : N → G), ∃ σ : V → G, ∀ a : N, σ a.1 - σ (p a) = g a := by
  classical
  have := Fintype.ofFinite V
  let st : Setoid V := Relation.EqvGen.setoid Adj
  let rep : V → V := fun a => (@Quotient.mk'' V st a).out
  have hrep_rel : ∀ a, Relation.EqvGen Adj (rep a) a := fun a => Quotient.mk_out' (s₁ := st) a
  have hrep_eq : ∀ a b, Relation.EqvGen Adj a b → rep a = rep b := by
    intro a b h
    show (@Quotient.mk'' V st a).out = (@Quotient.mk'' V st b).out
    rw [Quotient.sound' (s₁ := st) h]
  have hrep_rep : ∀ a, rep (rep a) = rep a := fun a => hrep_eq _ _ (hrep_rel a)
  have hex : ∀ a, ∃ n, reach Adj (rep a) n a := fun a => exists_reach (rtg_of_eqvGen hsymm (hrep_rel a))
  let d : V → ℕ := fun a => Nat.find (hex a)
  let N : Set V := {a | a ≠ rep a}
  have key : ∀ a : N, ∃ b, Adj b a.1 ∧ d b < d a.1 ∧ rep b = rep a.1 := by
    intro a
    have hm := Nat.find_spec (hex a.1)
    obtain ⟨k, hk⟩ : ∃ k, Nat.find (hex a.1) = k + 1 := by
      rcases h : Nat.find (hex a.1) with _ | k
      · rw [h] at hm; exact absurd hm a.2
      · exact ⟨k, rfl⟩
    rw [hk] at hm
    rcases hm with hm | ⟨b, hb, hba⟩
    · exact absurd hm (Nat.find_min (hex a.1) (by omega : k < Nat.find (hex a.1)))
    · have hrb : rep b = rep a.1 := by
        have h1 : Relation.EqvGen Adj (rep a.1) b := eqvGen_of_rtg (rtg_of_reach hb)
        rw [← hrep_eq _ _ h1, hrep_rep]
      refine ⟨b, hba, ?_, hrb⟩
      have : d b ≤ k := Nat.find_min' (hex b) (by rw [hrb]; exact hb)
      show d b < Nat.find (hex a.1)
      omega
  choose p hpAdj hpd hprep using key
  set u : N → (V →₀ ℤ) := fun a => Finsupp.single a.1 1 - Finsupp.single (p a) 1 with hu
  refine ⟨N, p, hpAdj, ?_, ?_, fun G _ g => exists_potential d N p hpd g⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀⟩ := hne
    set s := Finset.univ.filter (fun i => g i ≠ 0)
    have hs : s.Nonempty := ⟨i₀, by simp [s, hi₀]⟩
    obtain ⟨i, his, hmax⟩ := s.exists_max_image (fun i => d i.1) hs
    have hgi : g i ≠ 0 := (Finset.mem_filter.1 his).2
    have heval := congrArg (fun f : V →₀ ℤ => f i.1) hg
    simp only [Finset.sum_apply', Finsupp.coe_zero, Pi.zero_apply] at heval
    rw [Finset.sum_eq_single i] at heval
    · have hpi : p i ≠ i.1 := fun h => by
        have := hpd i
        rw [h] at this
        exact lt_irrefl _ this
      simp [hpi] at heval
      exact hgi heval
    · intro j _ hji
      have hj1 : j.1 ≠ i.1 := fun h => hji (Subtype.ext h)
      by_cases hpj : p j = i.1
      · have hdj : d i.1 < d j.1 := hpj ▸ hpd j
        have hgj : g j = 0 := by
          by_contra hgj
          have := hmax j (by simp [s, hgj])
          omega
        simp [hgj]
      · simp [hj1, hpj]
    · intro h; exact absurd (Finset.mem_univ i) h
  · have hroot : ∀ n, ∀ a, d a = n →
        Finsupp.single a (1 : ℤ) - Finsupp.single (rep a) 1 ∈ Submodule.span ℤ (range u) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro a ha
      by_cases har : a = rep a
      · rw [← har]; simp
      · have e : Finsupp.single a (1 : ℤ) - Finsupp.single (rep a) 1 =
            u ⟨a, har⟩ + (Finsupp.single (p ⟨a, har⟩) 1 - Finsupp.single (rep (p ⟨a, har⟩)) 1) := by
          rw [hprep ⟨a, har⟩]; simp [u]
        rw [e]
        refine Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩) ?_
        exact ih _ (ha ▸ hpd ⟨a, har⟩) _ rfl
    intro a b hab
    have hrab : rep a = rep b := hrep_eq _ _ (Relation.EqvGen.rel _ _ hab)
    have e : Finsupp.single a (1 : ℤ) - Finsupp.single b 1 =
        (Finsupp.single a 1 - Finsupp.single (rep a) 1) -
          (Finsupp.single b 1 - Finsupp.single (rep b) 1) := by
      rw [hrab]; abel
    rw [e]
    exact Submodule.sub_mem _ (hroot _ a rfl) (hroot _ b rfl)

end SquareBasis
