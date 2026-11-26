module

public import SquareBasis.Section6
public import SquareBasis.Potential

/-!
# Section 7.2 of the paper (part 1): vectors orthogonal to `ker_ℤ A_M`

`orth_ker` is the combinatorial core of the proof of Theorem 7.4: if `ψ : 𝓑 → G` (for any
abelian group `G`) annihilates `ker_ℤ A_M`, then `ψ_I = τ + ∑_{i ∈ I} σ_i` for some `σ`, `τ`.
The proof is the argument of the paper for the signs in Theorem 7.4(a): the map
`φ(A_M u) = ∑_I u_I ψ_I` is well defined on `Λ = A_M(ℤ^𝓑)`, the lattice `Λ⁰ = A_M(V⁰)` is
spanned by the edge vectors `e_a - e_b` of a spanning forest of the exchange graph, `σ` is
chosen along the forest, and `τ = φ(𝟙_{J₀}) - ∑_{i ∈ J₀} σ_i`.
-/

@[expose] public section

namespace SquareBasis

open Matroid Set

universe u

variable {α : Type u}

open scoped Classical in
/-- `⟪t, σ⟫ = ∑_{x ∈ E} t_x σ_x`. -/
noncomputable def pairE (N : Matroid α) [N.Finite] {G : Type} [AddCommGroup G] (t : α → ℤ)
    (σ : α → G) : G :=
  ∑ x ∈ N.ground_finite.toFinset, t x • σ x

theorem pairE_add (N : Matroid α) [N.Finite] {G : Type} [AddCommGroup G] (s t : α → ℤ)
    (σ : α → G) : pairE N (s + t) σ = pairE N s σ + pairE N t σ := by
  simp [pairE, add_smul, Finset.sum_add_distrib]

theorem pairE_smul (N : Matroid α) [N.Finite] {G : Type} [AddCommGroup G] (c : ℤ) (t : α → ℤ)
    (σ : α → G) : pairE N (c • t) σ = c • pairE N t σ := by
  simp [pairE, mul_smul, Finset.smul_sum]

theorem pairE_sub (N : Matroid α) [N.Finite] {G : Type} [AddCommGroup G] (s t : α → ℤ)
    (σ : α → G) : pairE N (s - t) σ = pairE N s σ - pairE N t σ := by
  simp [pairE, sub_smul, Finset.sum_sub_distrib]

open scoped Classical in
theorem pairE_single (N : Matroid α) [N.Finite] {G : Type} [AddCommGroup G] {a : α}
    (ha : a ∈ N.E) (σ : α → G) : pairE N (Pi.single a 1) σ = σ a := by
  simp only [pairE, Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Set.Finite.mem_toFinset, ha, ite_true]

open scoped Classical in
theorem pairE_indicator (N : Matroid α) [N.Finite] {G : Type} [AddCommGroup G] (I : Bases N)
    (σ : α → G) : pairE N (Set.indicator I.1 (fun _ => (1 : ℤ))) σ =
      ∑ x ∈ N.ground_finite.toFinset.filter (· ∈ I.1), σ x := by
  simp only [pairE, Set.indicator_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite,
    Finset.sum_const_zero, add_zero]

/-- `⟪·, σ⟫` as an additive map. -/
noncomputable def pairEHom (N : Matroid α) [N.Finite] {G : Type} [AddCommGroup G] (σ : α → G) :
    (α → ℤ) →+ G where
  toFun t := pairE N t σ
  map_zero' := by simp [pairE]
  map_add' s t := pairE_add N s t σ

open scoped Classical in
/-- **The core of Theorem 7.4.** If `ψ : 𝓑 → G` vanishes on `ker_ℤ A_M`, i.e.
`∑_I u_I ψ_I = 0` for every `u ∈ ker_ℤ A_M`, then there are `σ : E → G` and `τ ∈ G` with
`ψ_I = τ + ∑_{i ∈ I} σ_i` for every basis `I`. -/
theorem orth_ker (N : Matroid α) [N.Finite] {G : Type} [AddCommGroup G] (ψ : Bases N → G)
    (hψ : ∀ u ∈ LinearMap.ker (incidence N), Finsupp.linearCombination ℤ ψ u = 0) :
    ∃ (σ : α → G) (τ : G), ∀ I : Bases N,
      ψ I = τ + ∑ x ∈ N.ground_finite.toFinset.filter (· ∈ I.1), σ x := by
  classical
  let V : Set α := N.E
  have : Finite V := N.ground_finite.to_subtype
  let Adj : V → V → Prop := fun x y => x ≠ y ∧ ∃ D, x.1 ∉ D ∧ y.1 ∉ D ∧
    N.IsBase (insert x.1 D) ∧ N.IsBase (insert y.1 D)
  have hsymm : ∀ x y, Adj x y → Adj y x := by
    rintro x y ⟨hxy, D, h1, h2, h3, h4⟩; exact ⟨Ne.symm hxy, D, h2, h1, h4, h3⟩
  obtain ⟨Nf, p, hpAdj, -, hspanE, hpot⟩ := forest_basis_pot Adj hsymm
  choose hne D hD1 hD2 hb1 hb2 using hpAdj
  -- the edge vectors and their preimages
  let φ : Nf → (α → ℤ) := fun a => Pi.single a.1.1 1 - Pi.single (p a).1 1
  let w : Nf → (Bases N →₀ ℤ) := fun a =>
    Finsupp.single ⟨_, hb2 a⟩ 1 - Finsupp.single ⟨_, hb1 a⟩ 1
  have hw : ∀ a, incidence N (w a) = φ a := by
    intro a
    simp only [w, φ, map_sub, incidence, Finsupp.linearCombination_single, one_smul]
    convert indicator_insert_sub (hD2 a) (hD1 a) using 2
  -- the potential along the forest
  obtain ⟨σV, hσV⟩ := hpot G (fun a => Finsupp.linearCombination ℤ ψ (w a))
  let σ : α → G := fun x => if h : x ∈ N.E then σV ⟨x, h⟩ else 0
  have hφσ : ∀ a, pairE N (φ a) σ = Finsupp.linearCombination ℤ ψ (w a) := by
    intro a
    simp only [φ, pairE_sub, pairE_single N a.1.2, pairE_single N (p a).2]
    have h1 : a.1.1 ∈ N.E := a.1.2
    have h2 : (p a).1 ∈ N.E := (p a).2
    simp only [σ, h1, h2, ↓reduceDIte]
    exact hσV a
  -- `A_N w ∈ span φ` when `∑ w = 0` (Step 3 of Proposition 3.1)
  have hedge : ∀ x y : V, Adj x y → Pi.single x.1 (1 : ℤ) - Pi.single y.1 1 ∈
      Submodule.span ℤ (range φ) := by
    intro x y hxy
    have h1 := hspanE x y hxy
    have hφ : φ = vecOf V ∘ (fun a : Nf => Finsupp.single a.1 (1 : ℤ) - Finsupp.single (p a) 1) := by
      funext a; simp only [Function.comp_apply, vecOf_single_sub, φ]
    have h2 := Submodule.mem_map_of_mem (f := vecOf V) h1
    rw [← Submodule.span_image, ← range_comp, ← hφ] at h2
    rwa [vecOf_single_sub] at h2
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
    have hfin : (J.1 \ J'.1).Finite :=
      N.ground_finite.subset (sdiff_subset.trans J.2.subset_ground)
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
  -- the key identity on `V⁰`: `∑_I u_I ψ_I = ⟪A_N u, σ⟫` for `u = e_J - e_{J'}`
  have hkey : ∀ J J' : Bases N, ψ J - ψ J' =
      pairE N (Set.indicator J.1 (fun _ => (1 : ℤ)) - Set.indicator J'.1 (fun _ => 1)) σ := by
    intro J J'
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 (hpair _ J J' rfl)
    -- `u - ∑ c_a w_a ∈ ker`
    set u : Bases N →₀ ℤ := Finsupp.single J 1 - Finsupp.single J' 1
    set u' : Bases N →₀ ℤ := c.sum (fun a t => t • w a)
    have hAu : incidence N u = Set.indicator J.1 (fun _ => (1 : ℤ)) -
        Set.indicator J'.1 (fun _ => 1) := by
      simp [u, incidence]
    have hAu' : incidence N u' = Set.indicator J.1 (fun _ => (1 : ℤ)) -
        Set.indicator J'.1 (fun _ => 1) := by
      rw [← hc]
      simp only [u', map_finsuppSum, map_zsmul, hw]
    have hker : u - u' ∈ LinearMap.ker (incidence N) := by
      rw [LinearMap.mem_ker, map_sub, hAu, hAu', sub_self]
    have h1 := hψ _ hker
    rw [map_sub, sub_eq_zero] at h1
    have h2 : Finsupp.linearCombination ℤ ψ u = ψ J - ψ J' := by
      simp [u]
    have h3 : Finsupp.linearCombination ℤ ψ u' = c.sum (fun a t => t • pairE N (φ a) σ) := by
      simp only [u', map_finsuppSum, map_zsmul, hφσ]
    rw [← h2, h1, h3, ← hc]
    have := map_finsuppSum (pairEHom N σ) c (fun a t => t • φ a)
    simp only [map_zsmul] at this
    exact this.symm
  obtain ⟨J₀, hJ₀⟩ := N.exists_isBase
  refine ⟨σ, ψ ⟨J₀, hJ₀⟩ - ∑ x ∈ N.ground_finite.toFinset.filter (· ∈ J₀), σ x,
    fun I => ?_⟩
  have h := hkey I ⟨J₀, hJ₀⟩
  rw [pairE_sub, pairE_indicator, pairE_indicator, sub_eq_iff_eq_add] at h
  rw [h]
  abel

open scoped Classical in
/-- The converse direction: a function of the form `ψ_I = τ + ∑_{i ∈ I} σ_i` annihilates
`ker_ℤ A_M` when `rank M ≥ 1`. -/
theorem lc_eq_zero_of_potential (N : Matroid α) [N.Finite] [N.RankPos] {G : Type}
    [AddCommGroup G] (ψ : Bases N → G) (σ : α → G) (τ : G)
    (h : ∀ I : Bases N, ψ I = τ + ∑ x ∈ N.ground_finite.toFinset.filter (· ∈ I.1), σ x)
    {u : Bases N →₀ ℤ} (hu : u ∈ LinearMap.ker (incidence N)) :
    Finsupp.linearCombination ℤ ψ u = 0 := by
  classical
  have key : ∀ v : Bases N →₀ ℤ, Finsupp.linearCombination ℤ ψ v =
      total v • τ + pairE N (incidence N v) σ := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero => simp [total, pairE]
    | add f g hf hg =>
      have ht : total (f + g) = total f + total g := by
        simp only [total]; rw [Finsupp.sum_add_index'] <;> simp
      rw [map_add, map_add, hf, hg, ht, add_smul, pairE_add]; abel
    | single B c =>
      rw [Finsupp.linearCombination_single, h B]
      have : incidence N (Finsupp.single B c) = c • Set.indicator B.1 (fun _ => (1 : ℤ)) := by
        simp [incidence]
      rw [this, pairE_smul, pairE_indicator]
      simp [total, smul_add]
  rw [key, total_eq_zero_of_mem_ker N hu, LinearMap.mem_ker.1 hu]
  simp [pairE]

end SquareBasis
