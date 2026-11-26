module

public import SquareBasis.Duality
public import SquareBasis.Exchange
public import SquareBasis.LinAlg

/-!
# Lifting a square basis along the deletion of one element

Let `v` be a non-coloop of `M`. If `M ＼ {v}` has a square basis and the exchange
condition `StarD M v` holds, then `M` has a square basis.

The proof follows the exact sequence of the paper (Theorem 4.2). Restricting to the bases
containing `v` gives a map `ρ` whose kernel on `ker_ℤ A_M` is `ker_ℤ A_{M ＼ v}`; its
image lies in the sum-zero lattice on the bases containing `v`. The condition `StarD M v`
gives, for every basis exchange between two bases containing `v`, a square whose image
under `ρ` is the corresponding edge vector, and a spanning tree of these exchanges gives a
basis of the sum-zero lattice (`graph_basis`).
-/

@[expose] public section

namespace SquareBasis

open Matroid Set

universe u

variable {α : Type u}

instance finite_bases (M : Matroid α) [M.Finite] : Finite (Bases M) := by
  have : {B | M.IsBase B}.Finite :=
    M.ground_finite.finite_subsets.subset (fun B hB => hB.subset_ground)
  exact this.to_subtype

theorem delete_isBase_iff_of_rk {M : Matroid α} [M.Finite] {v : α}
    (hv : rk M (M.E \ {v}) = rk M M.E) {B : Set α} :
    (M ＼ {v}).IsBase B ↔ M.IsBase B ∧ v ∉ B := by
  rw [delete_isBase_iff]
  constructor
  · intro h
    refine ⟨isBase_of_indep_ncard h.indep ?_, fun hvB => (h.subset hvB).2 rfl⟩
    rw [← hv, rk_isBasis' h.isBasis', ← rk_indep h.indep, rk_indep h.indep]
  · rintro ⟨hB, hvB⟩
    exact hB.isBasis_of_subset sdiff_subset
      (fun x hx => ⟨hB.subset_ground hx, fun h => hvB (by rw [mem_singleton_iff] at h; exact h ▸ hx)⟩)

/-- The bases of `M` containing `v`. -/
def basesWith (M : Matroid α) (v : α) : Set (Bases M) := {B | v ∈ B.1}

/-- Restriction to the bases containing `v` (the map `π` of Theorem 4.2). -/
noncomputable def restrictV (M : Matroid α) (v : α) :
    (Bases M →₀ ℤ) →ₗ[ℤ] (basesWith M v →₀ ℤ) :=
  Finsupp.lsubtypeDomain (basesWith M v)

theorem restrictV_apply (M : Matroid α) (v : α) (f : Bases M →₀ ℤ) (w : basesWith M v) :
    restrictV M v f w = f w.1 := rfl

/-- `a — b` is realized by a square: some square `z` has `π(z) = e_b - e_a`. -/
def SqAdj (M : Matroid α) (v : α) (a b : basesWith M v) : Prop :=
  ∃ z, IsSquare M z ∧ restrictV M v z = Finsupp.single b 1 - Finsupp.single a 1

/-- **Lifting along a deletion** (Theorems 4.2 and 4.3 of the paper). If `v` is not a coloop,
`M ＼ v` has a square basis, and the bases containing `v` are connected by edges realized by
squares, then `M` has a square basis. -/
theorem lift_of_sqAdj (M : Matroid α) [M.Finite] (v : α)
    (hv : rk M (M.E \ {v}) = rk M M.E)
    (hconnA : ∀ a b : basesWith M v, Relation.ReflTransGen (SqAdj M v) a b)
    (hN : HasSquareBasis (M ＼ {v})) : HasSquareBasis M := by
  classical
  set N := M ＼ {v} with hNdef
  have hbase : ∀ {B}, N.IsBase B ↔ M.IsBase B ∧ v ∉ B := delete_isBase_iff_of_rk hv
  -- the inclusion of bases
  let ι : Bases N → Bases M := fun B => ⟨B.1, (hbase.1 B.2).1⟩
  have hιinj : Function.Injective ι := by
    intro B B' h
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  let φ : (Bases N →₀ ℤ) →ₗ[ℤ] (Bases M →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ ι
  have hφ : ∀ f, incidence M (φ f) = incidence N f := by
    intro f
    simp only [φ, incidence, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
    rfl
  have hφker : ∀ f, φ f ∈ LinearMap.ker (incidence M) ↔ f ∈ LinearMap.ker (incidence N) := by
    intro f; simp only [LinearMap.mem_ker, hφ]
  have hφinj : Function.Injective φ := Finsupp.mapDomain_injective hιinj
  have hφsq : ∀ z, IsSquare N z → IsSquare M (φ z) := by
    rintro z ⟨i, j, B, B', h₁, h₂, h₃, h₄, hij, hBB', hiB, hjB, hiB', hjB', rfl⟩
    refine ⟨i, j, B, B', (hbase.1 h₁).1, (hbase.1 h₂).1, (hbase.1 h₃).1, (hbase.1 h₄).1,
      hij, hBB', hiB, hjB, hiB', hjB', ?_⟩
    simp only [φ, map_add, map_sub, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rfl
  -- restriction to the bases containing `v`
  set s : Set (Bases M) := basesWith M v with hs
  let ρ : (Bases M →₀ ℤ) →ₗ[ℤ] (s →₀ ℤ) := restrictV M v
  have hρapply : ∀ f (w : s), ρ f w = f w.1 := fun f w => rfl
  set L := LinearMap.ker (incidence M) with hL
  -- the kernel part
  obtain ⟨SN, hSNsq, hSNli, hSNspan⟩ := hN
  set S := (φ : (Bases N →₀ ℤ) → (Bases M →₀ ℤ)) '' SN with hSdef
  have hSli : LinearIndepOn ℤ id S := by
    have h : LinearIndepOn ℤ id SN := hSNli
    exact h.image (by
      rw [LinearMap.ker_eq_bot.2 hφinj]; exact disjoint_bot_right)
  have hSspan : Submodule.span ℤ S = L ⊓ LinearMap.ker ρ := by
    rw [hSdef, Submodule.span_image, hSNspan]
    apply le_antisymm
    · rintro _ ⟨f, hf, rfl⟩
      refine ⟨(hφker f).2 hf, ?_⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      ext w
      rw [hρapply]
      simp only [φ, Finsupp.lmapDomain_apply, Finsupp.coe_zero, Pi.zero_apply]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨B, hB⟩
      have := (hbase.1 B.2).2
      have hw := w.2
      rw [← hB] at hw
      exact this hw
    · rintro g ⟨hgL, hgρ⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker] at hgρ
      have hsupp : ↑g.support ⊆ range ι := by
        intro B hB
        have hvB : v ∉ B.1 := by
          intro hvB
          have := congrArg (fun f => f ⟨B, hvB⟩) hgρ
          simp only [hρapply, Finsupp.coe_zero, Pi.zero_apply] at this
          exact (Finsupp.mem_support_iff.1 hB) this
        exact ⟨⟨B.1, hbase.2 ⟨B.2, hvB⟩⟩, rfl⟩
      have hg : φ (Finsupp.comapDomain ι g hιinj.injOn) = g :=
        Finsupp.mapDomain_comapDomain ι hιinj g hsupp
      refine ⟨Finsupp.comapDomain ι g hιinj.injOn, ?_, hg⟩
      rw [SetLike.mem_coe, ← hφker, hg]
      exact hgL
  -- the total of `ρ f` is row `v` of `A_M f`
  let tot : (s →₀ ℤ) →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ (fun _ : s => (1 : ℤ))
  have htot : ∀ f, tot (ρ f) = incidence M f v := by
    have : tot ∘ₗ ρ = (LinearMap.proj v) ∘ₗ incidence M := by
      apply Finsupp.lhom_ext
      intro B c
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
        Function.eval, incidence, Finsupp.linearCombination_single, Pi.smul_apply,
        Set.indicator_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hvB : v ∈ B.1
      · have : ρ (Finsupp.single B c) = Finsupp.single ⟨B, hvB⟩ c := by
          ext w
          rw [hρapply]
          simp only [Finsupp.single_apply]
          by_cases hw : B = w.1
          · simp [hw]
          · have : (⟨B, hvB⟩ : s) ≠ w := fun h => hw (congrArg Subtype.val h)
            simp [hw, this]
        rw [this]
        simp [tot, hvB]
      · have : ρ (Finsupp.single B c) = 0 := by
          ext w
          rw [hρapply]
          simp only [Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply]
          have : B ≠ w.1 := fun h => hvB (h ▸ w.2)
          simp [this]
        rw [this]
        simp [hvB]
    intro f
    exact LinearMap.congr_fun this f
  have hcover0 : L.map ρ ≤ LinearMap.ker tot := by
    rintro _ ⟨f, hf, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hf ⊢
    rw [htot, hf]; rfl
  -- the edge part
  have hfinal : ∀ {ι' : Type u} (t : ι' → Bases M →₀ ℤ), (∀ i, IsSquare M (t i)) →
      LinearIndependent ℤ (ρ ∘ t) → L.map ρ ≤ Submodule.span ℤ (range (ρ ∘ t)) →
      HasSquareBasis M := by
    intro ι' t htsq hρt hcov
    obtain ⟨hli, hspan⟩ := basis_of_exact L ρ S hSli hSspan t (fun i => (htsq i).mem_ker)
      hρt hcov
    refine ⟨S ∪ range t, ?_, hli, hspan⟩
    rintro z (⟨f, hf, rfl⟩ | ⟨i, rfl⟩)
    · exact hφsq f (hSNsq f hf)
    · exact htsq i
  by_cases hsne : Nonempty s
  · obtain ⟨r⟩ := hsne
    let Adj : s → s → Prop := SqAdj M v
    have hconn : ∀ B : s, Relation.ReflTransGen Adj r B := fun B => hconnA r B
    obtain ⟨p, hpAdj, hli, hspan⟩ := graph_basis r Adj hconn
    choose t htsq hρt using hpAdj
    refine hfinal t htsq ?_ ?_
    · have : ρ ∘ t = fun a : {a // a ≠ r} => Finsupp.single a.1 (1 : ℤ) - Finsupp.single (p a) 1 :=
        funext hρt
      rw [this]; exact hli
    · have : ρ ∘ t = fun a : {a // a ≠ r} => Finsupp.single a.1 (1 : ℤ) - Finsupp.single (p a) 1 :=
        funext hρt
      rw [this, hspan]; exact hcover0
  · have hempty : IsEmpty s := not_nonempty_iff.1 hsne
    refine hfinal (ι' := PEmpty) (fun x => x.elim) (fun x => x.elim)
      (linearIndependent_empty_type) ?_
    rintro _ ⟨f, -, rfl⟩
    have : ρ f = 0 := by ext w; exact isEmptyElim w
    rw [this]
    exact Submodule.zero_mem _


/-- Under the exchange condition `StarD M v`, the bases containing `v` are connected by
square-realized exchanges. -/
theorem sqAdj_conn_of_starD (M : Matroid α) [M.Finite] (v : α) (hstar : StarD M v) :
    ∀ r B : basesWith M v, Relation.ReflTransGen (SqAdj M v) r B := by
  classical
  set s : Set (Bases M) := basesWith M v with hs
  let ρ : (Bases M →₀ ℤ) →ₗ[ℤ] (s →₀ ℤ) := restrictV M v
  have hρapply : ∀ f (w : s), ρ f w = f w.1 := fun f w => rfl
  let Adj : s → s → Prop := SqAdj M v
  intro r
  have main : ∀ n, ∀ B : s, (B.1.1 \ r.1.1).ncard = n → Relation.ReflTransGen Adj r B := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro B hn
    by_cases hBr : B = r
    · rw [hBr]
    have hBr' : ¬ B.1.1 ⊆ r.1.1 := by
      intro hsub
      exact hBr (Subtype.ext (Subtype.ext (B.1.2.eq_of_subset_isBase r.1.2 hsub)))
    obtain ⟨e, heB, her⟩ := not_subset.1 hBr'
    obtain ⟨y, ⟨hyr, hyB⟩, hB'⟩ := B.1.2.exchange r.1.2 ⟨heB, her⟩
    have hve : v ≠ e := fun h => her (h ▸ r.2)
    have hvB' : v ∈ insert y (B.1.1 \ {e}) :=
      mem_insert_of_mem _ ⟨B.2, fun h => hve (by rwa [mem_singleton_iff] at h)⟩
    let B' : s := ⟨⟨_, hB'⟩, hvB'⟩
    have hfin : (B.1.1 \ r.1.1).Finite :=
      M.ground_finite.subset (sdiff_subset.trans B.1.2.subset_ground)
    have hlt : (B'.1.1 \ r.1.1).ncard < n := by
      rw [← hn]
      apply Set.ncard_lt_ncard _ hfin
      refine ⟨?_, fun h => ?_⟩
      · rintro x ⟨hx, hxr⟩
        rcases hx with rfl | ⟨hxB, -⟩
        · exact absurd hyr hxr
        · exact ⟨hxB, hxr⟩
      · have := h ⟨heB, her⟩
        rcases this.1 with h' | h'
        · rw [h'] at her; exact her hyr
        · exact h'.2 rfl
    have hrB' := ih _ hlt B' rfl
    refine hrB'.tail ?_
    -- the square realizing the exchange `B' — B`
    set D := B.1.1 \ {e} with hD
    have hey : e ≠ y := fun h => her (h ▸ hyr)
    have hvD : v ∈ D := ⟨B.2, fun h => hve (by rwa [mem_singleton_iff] at h)⟩
    have heD : e ∉ D := fun h => h.2 rfl
    have hyD : y ∉ D := fun h => hyB h.1
    have hBeq : insert e D = B.1.1 := by
      rw [hD, insert_sdiff_singleton, insert_eq_of_mem heB]
    have hb₁ : M.IsBase (insert e D) := hBeq ▸ B.1.2
    obtain ⟨D', hvD', heD', hyD', hb₃, hb₄⟩ := hstar D e y hey hvD heD hyD hb₁ hB'
    have hDD' : D ≠ D' := fun h => hvD' (h ▸ hvD)
    refine ⟨_, ⟨e, y, D, D', hb₁, hB', hb₃, hb₄, hey, hDD', heD, hyD, heD', hyD', rfl⟩, ?_⟩
    ext w
    simp only [map_add, map_sub, Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply,
      Pi.sub_apply, restrictV_apply, Finsupp.single_apply]
    have h3 : (⟨insert e D', hb₃⟩ : Bases M) ≠ w.1 := fun h => hvD' (by
      have := w.2; rw [← h] at this
      rcases this with h' | h'
      · exact absurd (h' ▸ r.2) her
      · exact h')
    have h4 : (⟨insert y D', hb₄⟩ : Bases M) ≠ w.1 := fun h => hvD' (by
      have := w.2; rw [← h] at this
      rcases this with h' | h'
      · exact absurd hve (fun _ => by
          have hvy : v = y := h'
          exact hyB (hvy ▸ B.2))
      · exact h')
    have e1 : ((⟨insert e D, hb₁⟩ : Bases M) = w.1) ↔ (B = w) := by
      constructor
      · intro h; exact Subtype.ext (by rw [← h]; exact Subtype.ext hBeq.symm)
      · intro h; rw [← h]; exact Subtype.ext hBeq
    have e2 : ((⟨insert y D, hB'⟩ : Bases M) = w.1) ↔ (B' = w) := by
      constructor
      · intro h; exact Subtype.ext h
      · intro h; rw [← h]
    simp only [e1, e2, h3, h4, ite_false, sub_zero, add_zero]
  intro B
  exact main _ B rfl

/-- **Lifting along a deletion, exchange-graph version.** -/
theorem hasSquareBasis_of_delete (M : Matroid α) [M.Finite] (v : α)
    (hv : rk M (M.E \ {v}) = rk M M.E) (hstar : StarD M v)
    (hN : HasSquareBasis (M ＼ {v})) : HasSquareBasis M :=
  lift_of_sqAdj M v hv (sqAdj_conn_of_starD M v hstar) hN

/-- If the whole ground set is a base, then `ker_ℤ A_M = 0`. -/
theorem hasSquareBasis_of_isBase_ground (M : Matroid α) [M.Finite] [M.RankPos]
    (hE : M.IsBase M.E) : HasSquareBasis M := by
  classical
  have hsub : ∀ B : Bases M, B = ⟨M.E, hE⟩ := by
    intro B
    apply Subtype.ext
    exact Set.eq_of_subset_of_ncard_le B.2.subset_ground
      (le_of_eq (hE.ncard_eq_ncard_of_isBase B.2)) M.ground_finite
  obtain ⟨x, hx⟩ : M.E.Nonempty := by
    rcases M.E.eq_empty_or_nonempty with h | h
    · exact absurd (h ▸ hE) M.empty_not_isBase
    · exact h
  refine ⟨∅, by simp, linearIndependent_empty_type, ?_⟩
  rw [Submodule.span_empty]
  symm
  rw [eq_bot_iff]
  intro f hf
  have hf1 : f = Finsupp.single ⟨M.E, hE⟩ (f ⟨M.E, hE⟩) := by
    ext B; rw [hsub B]; simp
  rw [LinearMap.mem_ker, hf1] at hf
  have := congrFun hf x
  simp only [incidence, Finsupp.linearCombination_single, Pi.smul_apply,
    Set.indicator_of_mem hx, smul_eq_mul, mul_one, Pi.zero_apply] at this
  rw [Submodule.mem_bot, hf1, this, Finsupp.single_zero]

theorem rankPos_delete {M : Matroid α} [M.Finite] [M.RankPos] {v : α}
    (hv : rk M (M.E \ {v}) = rk M M.E) : (M ＼ {v}).RankPos :=
  ⟨fun h => M.empty_not_isBase ((delete_isBase_iff_of_rk hv).1 h).1⟩

theorem rk_dual_sdiff_singleton (M : Matroid α) [M.Finite] {v : α} (hv : v ∈ M.E) :
    rk M✶ (M.E \ {v}) - rk M✶ M.E = rk M {v} - 1 := by
  rw [rk_dual M sdiff_subset, rk_dual M subset_rfl, sdiff_sdiff_cancel_left
    (singleton_subset_iff.2 hv), sdiff_self, rk_empty]
  have := Set.ncard_sdiff_singleton_add_one hv M.ground_finite
  have : ((M.E \ {v}).ncard : ℤ) + 1 = M.E.ncard := by exact_mod_cast this
  linarith

theorem rk_dual_singleton (M : Matroid α) [M.Finite] {v : α} (hv : v ∈ M.E) :
    rk M✶ {v} = 1 + rk M (M.E \ {v}) - rk M M.E := by
  rw [rk_dual M (singleton_subset_iff.2 hv), ncard_singleton]
  simp

end SquareBasis
