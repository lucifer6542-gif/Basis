module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

/-!
# Two lemmas on lattices

* `basis_of_exact` : if `S` is a basis of `L ∩ ker ρ` and the images `ρ(t_i)` are linearly
  independent and span `ρ(L)`, then `S ∪ {t_i}` is a basis of `L`.
* `graph_basis` : for a connected relation on a finite set `V` with root `r`, there is a
  parent function `p` such that the vectors `e_a - e_{p(a)}` (`a ≠ r`) form a basis of the
  lattice of integer vectors on `V` with coordinate sum zero.
-/

@[expose] public section

namespace SquareBasis

open Set

theorem basis_of_exact {V W ι : Type*} [AddCommGroup V] [Module ℤ V] [AddCommGroup W]
    [Module ℤ W] (L : Submodule ℤ V) (ρ : V →ₗ[ℤ] W) (S : Set V) (hS : LinearIndepOn ℤ id S)
    (hSspan : Submodule.span ℤ S = L ⊓ LinearMap.ker ρ) (t : ι → V) (ht : ∀ i, t i ∈ L)
    (hρt : LinearIndependent ℤ (ρ ∘ t))
    (hcover : L.map ρ ≤ Submodule.span ℤ (range (ρ ∘ t))) :
    LinearIndepOn ℤ id (S ∪ range t) ∧ Submodule.span ℤ (S ∪ range t) = L := by
  have htinj : Function.Injective t := Function.Injective.of_comp hρt.injective
  have htli : LinearIndependent ℤ t := LinearIndependent.of_comp ρ hρt
  have hT : LinearIndepOn ℤ id (range t) := (linearIndepOn_id_range_iff htinj).2 htli
  have hSL : Submodule.span ℤ S ≤ L := hSspan ▸ inf_le_left
  have hSker : Submodule.span ℤ S ≤ LinearMap.ker ρ := hSspan ▸ inf_le_right
  have hTL : Submodule.span ℤ (range t) ≤ L := Submodule.span_le.2 (range_subset_iff.2 ht)
  have hρinj : ∀ x ∈ Submodule.span ℤ (range t), ρ x = 0 → x = 0 := by
    intro x hx hρx
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
    have h1 : Finsupp.linearCombination ℤ (ρ ∘ t) c = 0 := by
      rw [← Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
      exact hρx
    have hc := linearIndependent_iff.1 hρt c h1
    simp [hc]
  refine ⟨hS.id_union hT ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxS hxT
    exact hρinj x hxT (hSker hxS)
  · rw [Submodule.span_union]
    refine le_antisymm (sup_le hSL hTL) ?_
    intro f hf
    have h1 : ρ f ∈ Submodule.span ℤ (range (ρ ∘ t)) := hcover ⟨f, hf, rfl⟩
    rw [range_comp, Submodule.span_image] at h1
    obtain ⟨y, hy, hyf⟩ := h1
    have hfy : f - y ∈ Submodule.span ℤ S := by
      rw [hSspan]
      refine ⟨L.sub_mem hf (hTL hy), ?_⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hyf, sub_self]
    have : f = (f - y) + y := by abel
    rw [this]
    exact Submodule.add_mem_sup hfy hy

/-! ### Spanning trees -/

/-- `reach Adj r n a` : `a` is reached from `r` in at most `n` steps. -/
def reach {V : Type*} (Adj : V → V → Prop) (r : V) : ℕ → V → Prop
  | 0 => fun a => a = r
  | n + 1 => fun a => reach Adj r n a ∨ ∃ b, reach Adj r n b ∧ Adj b a

theorem exists_reach {V : Type*} {Adj : V → V → Prop} {r a : V}
    (h : Relation.ReflTransGen Adj r a) : ∃ n, reach Adj r n a := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, Or.inr ⟨_, hn, hbc⟩⟩

/-- The sum-zero lattice on `V` is spanned, with a basis, by `e_a - e_{p(a)}`. -/
theorem graph_basis {V : Type*} [Finite V] (r : V) (Adj : V → V → Prop)
    (hconn : ∀ a, Relation.ReflTransGen Adj r a) :
    ∃ p : {a // a ≠ r} → V, (∀ a, Adj (p a) a.1) ∧
      LinearIndependent ℤ
        (fun a : {a // a ≠ r} => Finsupp.single a.1 (1 : ℤ) - Finsupp.single (p a) 1) ∧
      Submodule.span ℤ
        (range (fun a : {a // a ≠ r} => Finsupp.single a.1 (1 : ℤ) - Finsupp.single (p a) 1)) =
        LinearMap.ker (Finsupp.linearCombination ℤ (fun _ : V => (1 : ℤ))) := by
  classical
  have := Fintype.ofFinite V
  have hex : ∀ a, ∃ n, reach Adj r n a := fun a => exists_reach (hconn a)
  let d : V → ℕ := fun a => Nat.find (hex a)
  have key : ∀ a : {a // a ≠ r}, ∃ b, Adj b a.1 ∧ d b < d a.1 := by
    intro a
    have hm := Nat.find_spec (hex a.1)
    obtain ⟨k, hk⟩ : ∃ k, Nat.find (hex a.1) = k + 1 := by
      rcases h : Nat.find (hex a.1) with _ | k
      · rw [h] at hm; exact absurd hm a.2
      · exact ⟨k, rfl⟩
    rw [hk] at hm
    rcases hm with hm | ⟨b, hb, hba⟩
    · exact absurd hm (Nat.find_min (hex a.1) (by omega : k < Nat.find (hex a.1)))
    · refine ⟨b, hba, ?_⟩
      have : d b ≤ k := Nat.find_min' (hex b) hb
      show d b < Nat.find (hex a.1)
      omega
  choose p hpAdj hpd using key
  set u : {a // a ≠ r} → (V →₀ ℤ) := fun a => Finsupp.single a.1 1 - Finsupp.single (p a) 1
    with hu
  refine ⟨p, hpAdj, ?_, ?_⟩
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
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      simp [LinearMap.mem_ker]
    · have hroot : ∀ n, ∀ a, d a = n →
          Finsupp.single a (1 : ℤ) - Finsupp.single r 1 ∈ Submodule.span ℤ (range u) := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
        intro a ha
        by_cases har : a = r
        · subst har; simp
        · have e : Finsupp.single a (1 : ℤ) - Finsupp.single r 1 =
              u ⟨a, har⟩ + (Finsupp.single (p ⟨a, har⟩) 1 - Finsupp.single r 1) := by
            simp [u]
          rw [e]
          refine Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩) ?_
          exact ih _ (ha ▸ hpd ⟨a, har⟩) _ rfl
      have hall : ∀ g : V →₀ ℤ, g - Finsupp.single r
          (Finsupp.linearCombination ℤ (fun _ : V => (1 : ℤ)) g) ∈
            Submodule.span ℤ (range u) := by
        intro g
        induction g using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg =>
          have e : f + g - Finsupp.single r
              (Finsupp.linearCombination ℤ (fun _ : V => (1 : ℤ)) (f + g)) =
              (f - Finsupp.single r (Finsupp.linearCombination ℤ (fun _ : V => (1 : ℤ)) f)) +
              (g - Finsupp.single r (Finsupp.linearCombination ℤ (fun _ : V => (1 : ℤ)) g)) := by
            rw [map_add, Finsupp.single_add]; abel
          rw [e]; exact Submodule.add_mem _ hf hg
        | single a c =>
          have e : Finsupp.single a c - Finsupp.single r
              (Finsupp.linearCombination ℤ (fun _ : V => (1 : ℤ)) (Finsupp.single a c)) =
              c • (Finsupp.single a (1 : ℤ) - Finsupp.single r 1) := by
            simp [smul_sub, Finsupp.smul_single]
          rw [e]
          exact Submodule.smul_mem _ c (hroot _ a rfl)
      intro g hg
      have := hall g
      rw [LinearMap.mem_ker] at hg
      rwa [hg, Finsupp.single_zero, sub_zero] at this

/-! ### Tensor bases -/

section Tensor

variable {P Q : Type*}

/-- `w ⊗ e_q`. -/
noncomputable def emb (q : Q) : (P →₀ ℤ) →ₗ[ℤ] (P × Q →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (p, q))

theorem emb_injective (q : Q) : Function.Injective (fun p : P => (p, q)) :=
  fun _ _ h => (Prod.ext_iff.1 h).1

/-- The column of `f` at `q`. -/
noncomputable def col (q : Q) : (P × Q →₀ ℤ) →ₗ[ℤ] (P →₀ ℤ) :=
  Finsupp.lcomapDomain (fun p => (p, q)) (emb_injective q)

theorem col_apply (q : Q) (f : P × Q →₀ ℤ) (p : P) : col q f p = f (p, q) := rfl

theorem emb_apply (q : Q) (w : P →₀ ℤ) (p : P) (q' : Q) [DecidableEq Q] :
    emb q w (p, q') = if q = q' then w p else 0 := by
  unfold emb
  rw [Finsupp.lmapDomain_apply]
  by_cases h : q = q'
  · subst h
    rw [ite_eq_left rfl]
    exact Finsupp.mapDomain_apply_of_injective (emb_injective q) w p
  · rw [ite_eq_right h]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨p', hp'⟩
    exact h (Prod.ext_iff.1 hp').2

theorem col_emb [DecidableEq Q] (q q' : Q) (w : P →₀ ℤ) :
    col q' (emb q w) = if q = q' then w else 0 := by
  ext p
  rw [col_apply, emb_apply]
  split_ifs <;> simp

theorem sum_emb_col [DecidableEq Q] (f : P × Q →₀ ℤ) :
    f = ∑ q ∈ f.support.image Prod.snd, emb q (col q f) := by
  ext ⟨p, q'⟩
  rw [Finset.sum_apply']
  simp only [emb_apply, col_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · symm
    by_contra hne
    exact h (Finset.mem_image.2 ⟨(p, q'), Finsupp.mem_support_iff.2 (Ne.symm hne), rfl⟩)

/-- The tensor basis: if `S` is a basis of `K`, then `{w ⊗ e_q}` is a basis of the lattice of
`f` all of whose columns lie in `K`. -/
theorem tensor_basis (K : Submodule ℤ (P →₀ ℤ)) (S : Set (P →₀ ℤ)) (hS : LinearIndepOn ℤ id S)
    (hspan : Submodule.span ℤ S = K) :
    LinearIndepOn ℤ id (⋃ q : Q, (emb q : (P →₀ ℤ) → (P × Q →₀ ℤ)) '' S) ∧
      Submodule.span ℤ (⋃ q : Q, (emb q : (P →₀ ℤ) → (P × Q →₀ ℤ)) '' S) =
        ⨅ q : Q, K.comap (col q) := by
  classical
  -- the family indexed by `Q × S`
  let g : Q × S → (P × Q →₀ ℤ) := fun i => emb i.1 i.2.1
  have hSli : LinearIndependent ℤ (fun w : S => (w : P →₀ ℤ)) := hS
  have hg : LinearIndependent ℤ g := by
    rw [linearIndependent_iff']
    intro t c hc i hi
    have h1 := congrArg (col i.1) hc
    rw [map_sum, map_zero] at h1
    simp only [map_zsmul, g, col_emb] at h1
    rw [← Finset.sum_filter_add_sum_filter_not t (fun j => j.1 = i.1)] at h1
    rw [Finset.sum_eq_zero (s := t.filter (fun j => ¬ j.1 = i.1)) (fun j hj => by
      rw [ite_eq_right (Finset.mem_filter.1 hj).2, smul_zero]), add_zero] at h1
    rw [Finset.sum_congr rfl (fun j hj => by rw [ite_eq_left (Finset.mem_filter.1 hj).2])] at h1
    -- reindex by `S`
    have hinj : Set.InjOn (fun j : Q × S => j.2) (t.filter (fun j => j.1 = i.1)) := by
      intro j hj j' hj' h
      have e1 := (Finset.mem_filter.1 hj).2
      have e2 := (Finset.mem_filter.1 hj').2
      exact Prod.ext (e1.trans e2.symm) h
    have h2 : ∑ w ∈ (t.filter (fun j => j.1 = i.1)).image (fun j => j.2),
        c (i.1, w) • (w : P →₀ ℤ) = 0 := by
      rw [Finset.sum_image hinj]
      rw [← h1]
      apply Finset.sum_congr rfl
      intro j hj
      have := (Finset.mem_filter.1 hj).2
      have hj' : j = (i.1, j.2) := Prod.ext this rfl
      rw [← hj']
    have := linearIndependent_iff'.1 hSli _ (fun w => c (i.1, w)) h2 i.2
      (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hi, rfl⟩, rfl⟩)
    exact this
  have hrange : range g = ⋃ q : Q, (emb q : (P →₀ ℤ) → (P × Q →₀ ℤ)) '' S := by
    ext f
    simp only [mem_range, mem_iUnion, mem_image, g]
    constructor
    · rintro ⟨⟨q, w⟩, rfl⟩; exact ⟨q, w.1, w.2, rfl⟩
    · rintro ⟨q, w, hw, rfl⟩; exact ⟨⟨q, ⟨w, hw⟩⟩, rfl⟩
  refine ⟨hrange ▸ (linearIndepOn_id_range_iff hg.injective).2 hg, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro f hf
    simp only [mem_iUnion, mem_image] at hf
    obtain ⟨q, w, hw, rfl⟩ := hf
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
    intro q'
    rw [col_emb]
    split_ifs
    · rw [← hspan]; exact Submodule.subset_span hw
    · exact K.zero_mem
  · intro f hf
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hf
    rw [sum_emb_col f]
    refine Submodule.sum_mem _ (fun q _ => ?_)
    have h1 : col q f ∈ Submodule.span ℤ S := hspan ▸ hf q
    have h2 : emb q (col q f) ∈ Submodule.span ℤ ((emb q : (P →₀ ℤ) → (P × Q →₀ ℤ)) '' S) := by
      rw [Submodule.span_image]
      exact Submodule.mem_map_of_mem h1
    exact Submodule.span_mono (subset_iUnion_of_subset q subset_rfl) h2

end Tensor

/-! ### Spanning forests -/

theorem rtg_symm {V : Type*} {r : V → V → Prop} (hr : ∀ a b, r a b → r b a) {a b : V}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (hr _ _ hbc)).trans ih

theorem rtg_of_eqvGen {V : Type*} {r : V → V → Prop} (hr : ∀ a b, r a b → r b a) {a b : V}
    (h : Relation.EqvGen r a b) : Relation.ReflTransGen r a b := by
  induction h with
  | rel x y h => exact Relation.ReflTransGen.single h
  | refl => exact Relation.ReflTransGen.refl
  | symm x y _ ih => exact rtg_symm hr ih
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem eqvGen_of_rtg {V : Type*} {r : V → V → Prop} {a b : V}
    (h : Relation.ReflTransGen r a b) : Relation.EqvGen r a b := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hcd ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hcd)

theorem rtg_of_reach {V : Type*} {Adj : V → V → Prop} {r : V} :
    ∀ {n : ℕ} {a : V}, reach Adj r n a → Relation.ReflTransGen Adj r a
  | 0, a, h => by rw [show a = r from h]
  | n + 1, a, h => by
    rcases h with h | ⟨b, hb, hba⟩
    · exact rtg_of_reach h
    · exact (rtg_of_reach hb).tail hba

/-- **Spanning forest.** For a symmetric relation on a finite set there are non-root vertices
`N` and parents `p` such that the vectors `e_a - e_{p(a)}` (`a ∈ N`) are linearly independent
and span every edge vector `e_a - e_b`. -/
theorem forest_basis {V : Type*} [Finite V] (Adj : V → V → Prop) (hsymm : ∀ a b, Adj a b → Adj b a) :
    ∃ (N : Set V) (p : N → V), (∀ a, Adj (p a) a.1) ∧
      LinearIndependent ℤ (fun a : N => Finsupp.single a.1 (1 : ℤ) - Finsupp.single (p a) 1) ∧
      ∀ a b, Adj a b → Finsupp.single a (1 : ℤ) - Finsupp.single b 1 ∈
        Submodule.span ℤ (range (fun a : N => Finsupp.single a.1 (1 : ℤ) - Finsupp.single (p a) 1)) := by
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
  refine ⟨N, p, hpAdj, ?_, ?_⟩
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
