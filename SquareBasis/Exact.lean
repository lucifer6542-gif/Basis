module

public import SquareBasis.Section4
public import SquareBasis.Section3

/-!
# Lemma 4.1 and Theorem 4.2 of the paper

* `lemma41` : for a connected matroid `N` of rank `k ≥ 1`, the lattice `Λ(N)` spanned by the
  indicator vectors of the bases is `{x ∈ ℤ^E : k ∣ ∑ x}`.
* `thm42` : the exact sequence `0 → ker_ℤ A_{M＼v} → ker_ℤ A_M → Γ → 0` for `M` and `M ＼ v`
  connected (all three parts: injectivity, exactness in the middle, surjectivity onto `Γ`).
-/

@[expose] public section

namespace SquareBasis

open Matroid Set

universe u

variable {α : Type u}

/-- A circuit through `i ≠ j` gives bases `D + i` and `D + j`. -/
theorem exists_pair_of_isCircuit' {M : Matroid α} [M.Finite] {K : Set α} {i j : α}
    (hK : M.IsCircuit K) (hiK : i ∈ K) (hjK : j ∈ K) (hij : i ≠ j) :
    ∃ D, i ∉ D ∧ j ∉ D ∧ M.IsBase (insert i D) ∧ M.IsBase (insert j D) := by
  have hKj : M.Indep (K \ {j}) := hK.ssubset_indep
    (ssubset_of_subset_of_ne sdiff_subset (fun h => by
      have : j ∈ K \ {j} := by rw [h]; exact hjK
      exact this.2 rfl))
  obtain ⟨I, hI, hKI⟩ := hKj.exists_isBase_superset
  have hiI : i ∈ I := hKI ⟨hiK, fun h => hij (by rwa [mem_singleton_iff] at h)⟩
  have hjI : j ∉ I := by
    intro hjI
    apply hK.dep.not_indep (hI.indep.subset _)
    intro x hx
    by_cases hxj : x = j
    · exact hxj ▸ hjI
    · exact hKI ⟨hx, hxj⟩
  have hind : M.Indep (insert j (I \ {i})) := by
    by_contra hdep
    have hsub : insert j (I \ {i}) ⊆ M.E :=
      insert_subset (hK.subset_ground hjK) (sdiff_subset.trans hI.subset_ground)
    obtain ⟨K', hK's, hK'⟩ :=
      (show M.Dep (insert j (I \ {i})) from ⟨hdep, hsub⟩).exists_isCircuit_subset
    have h1 : K' ⊆ insert j I := hK's.trans (insert_subset_insert sdiff_subset)
    have h2 : K ⊆ insert j I := by
      intro x hx
      by_cases hxj : x = j
      · exact Or.inl hxj
      · exact Or.inr (hKI ⟨hx, hxj⟩)
    have := isCircuit_insert_unique hI.indep hK' hK h1 h2
    rw [← this] at hiK
    rcases hK's hiK with h | h
    · exact hij h
    · exact h.2 rfl
  refine ⟨I \ {i}, fun h => h.2 rfl, fun h => hjI h.1, ?_, ?_⟩
  · rwa [insert_sdiff_singleton, insert_eq_of_mem hiI]
  · exact insert_isBase_of_insert_indep (e := i) (fun h => h.2 rfl) (fun h => hjI h.1)
      (by rwa [insert_sdiff_singleton, insert_eq_of_mem hiI]) hind

open scoped Classical in
/-- The coordinate sum of a vector over a finite set. -/
noncomputable def sumOn (S : Set α) (hS : S.Finite) (x : α → ℤ) : ℤ := ∑ a ∈ hS.toFinset, x a

open scoped Classical in
theorem sumOn_incidence_single (N : Matroid α) [N.Finite] (B : Bases N) :
    sumOn N.E N.ground_finite (incidence N (Finsupp.single B 1)) = rk N N.E := by
  simp only [sumOn, incidence, Finsupp.linearCombination_single, one_smul, Set.indicator_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    rk_ground_eq_of_isBase B.2]
  have h1 : ((N.ground_finite.toFinset.filter (· ∈ B.1) : Finset α) : Set α) = B.1 := by
    ext x
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨B.2.subset_ground h, h⟩⟩
  have h2 := Set.ncard_coe_finset (N.ground_finite.toFinset.filter (· ∈ B.1))
  rw [h1] at h2
  rw [← h2]

/-- **Lemma 4.1.** For a connected matroid `N` of rank `k ≥ 1` on `Y`,
`Λ(N) = {x ∈ ℤ^Y : ∑ x ∈ kℤ}`. -/
theorem lemma41 (N : Matroid α) [N.Finite] [N.RankPos] (hN : Conn N) (x : α → ℤ) :
    x ∈ LinearMap.range (incidence N) ↔
      (∀ a, a ∉ N.E → x a = 0) ∧ rk N N.E ∣ sumOn N.E N.ground_finite x := by
  classical
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨fun a ha => incidence_eq_zero_of_notMem N f ha, ?_⟩
    -- `∑ A_N f = k ∑ f`
    have hlin : ∀ f : Bases N →₀ ℤ, sumOn N.E N.ground_finite (incidence N f) =
        rk N N.E * total f := by
      intro f
      induction f using Finsupp.induction_linear with
      | zero => simp [sumOn, total]
      | add f g hf hg =>
        have h1 : sumOn N.E N.ground_finite (incidence N (f + g)) =
            sumOn N.E N.ground_finite (incidence N f) + sumOn N.E N.ground_finite (incidence N g) := by
          simp [sumOn, Finset.sum_add_distrib]
        have h2 : total (f + g) = total f + total g := by
          simp only [total]; rw [Finsupp.sum_add_index'] <;> simp
        rw [h1, hf, hg, h2]; ring
      | single B c =>
        have h1 : incidence N (Finsupp.single B c) = c • incidence N (Finsupp.single B 1) := by
          rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
        have h2 : sumOn N.E N.ground_finite (c • incidence N (Finsupp.single B 1)) =
            c * sumOn N.E N.ground_finite (incidence N (Finsupp.single B 1)) := by
          simp [sumOn, Finset.mul_sum]
        rw [h1, h2, sumOn_incidence_single]
        simp [total]; ring
    rw [hlin]
    exact Dvd.intro _ rfl
  · rintro ⟨hsupp, q, hq⟩
    -- `e_j - e_i ∈ Λ` for distinct `i, j`
    have hedge : ∀ i ∈ N.E, ∀ j ∈ N.E, Pi.single j (1 : ℤ) - Pi.single i 1 ∈
        LinearMap.range (incidence N) := by
      intro i hi j hj
      by_cases hij : i = j
      · rw [hij, sub_self]; exact Submodule.zero_mem _
      obtain ⟨K, hK, hiK, hjK⟩ := conn_exists_isCircuit hN hi hj hij
      obtain ⟨D, hiD, hjD, h1, h2⟩ := exists_pair_of_isCircuit' hK hjK hiK (Ne.symm hij)
      refine ⟨Finsupp.single ⟨_, h1⟩ 1 - Finsupp.single ⟨_, h2⟩ 1, ?_⟩
      simp only [map_sub, incidence, Finsupp.linearCombination_single, one_smul]
      convert indicator_insert_sub hiD hjD using 2
    obtain ⟨J₀, hJ₀⟩ := N.exists_isBase
    obtain ⟨a₀, ha₀⟩ := hJ₀.nonempty
    have ha₀E : a₀ ∈ N.E := hJ₀.subset_ground ha₀
    set y : α → ℤ := x - q • incidence N (Finsupp.single ⟨J₀, hJ₀⟩ 1) with hy
    have hysupp : ∀ a, a ∉ N.E → y a = 0 := by
      intro a ha
      simp [hy, hsupp a ha, incidence_eq_zero_of_notMem N _ ha]
    have hysum : sumOn N.E N.ground_finite y = 0 := by
      have h1 : sumOn N.E N.ground_finite y = sumOn N.E N.ground_finite x -
          q * sumOn N.E N.ground_finite (incidence N (Finsupp.single ⟨J₀, hJ₀⟩ 1)) := by
        simp [hy, sumOn, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [h1, sumOn_incidence_single, hq]; ring
    have hdec : y = ∑ a ∈ N.ground_finite.toFinset, y a • (Pi.single a (1 : ℤ) - Pi.single a₀ 1) +
        sumOn N.E N.ground_finite y • Pi.single a₀ 1 := by
      funext b
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        mul_sub, Finset.sum_sub_distrib, sumOn, Finset.sum_mul]
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
      by_cases hb : b ∈ N.E
      · simp [hb]
      · simp [hb, hysupp b hb]
    have hy_mem : y ∈ LinearMap.range (incidence N) := by
      rw [hdec, hysum, zero_smul, add_zero]
      exact Submodule.sum_mem _ (fun a ha => Submodule.smul_mem _ _
        (hedge a₀ ha₀E a ((Set.Finite.mem_toFinset _).1 ha)))
    have : x = y + q • incidence N (Finsupp.single ⟨J₀, hJ₀⟩ 1) := by rw [hy]; abel
    rw [this]
    exact Submodule.add_mem _ hy_mem (Submodule.smul_mem _ _ ⟨_, rfl⟩)

open scoped Classical in
/-- The last claim of Lemma 4.1: `Λ(N)` contains `k ℤ^Y` (so `A_N` has full rank `|Y|`). -/
theorem lemma41_full (N : Matroid α) [N.Finite] [N.RankPos] (hN : Conn N) {a : α}
    (ha : a ∈ N.E) : rk N N.E • Pi.single a (1 : ℤ) ∈ LinearMap.range (incidence N) := by
  rw [lemma41 N hN]
  refine ⟨fun b hb => ?_, ?_⟩
  · have : b ≠ a := fun h => hb (h ▸ ha)
    simp [this]
  · refine ⟨1, ?_⟩
    simp only [sumOn, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Set.Finite.mem_toFinset, ha, ite_true]

/-! ### Theorem 4.2 -/

/-- Row `v` of `A_M` is the coordinate sum of the restriction to the bases containing `v`. -/
theorem total_restrictV (M : Matroid α) (v : α) (f : Bases M →₀ ℤ) :
    total (restrictV M v f) = incidence M f v := by
  classical
  rw [total_eq_lc]
  have : (Finsupp.linearCombination ℤ (fun _ : basesWith M v => (1 : ℤ))) ∘ₗ restrictV M v =
      (LinearMap.proj v) ∘ₗ incidence M := by
    apply Finsupp.lhom_ext
    intro B c
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
      incidence, Finsupp.linearCombination_single, Pi.smul_apply, Set.indicator_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hvB : v ∈ B.1
    · have : restrictV M v (Finsupp.single B c) = Finsupp.single ⟨B, hvB⟩ c := by
        ext w
        rw [restrictV_apply]
        simp only [Finsupp.single_apply]
        by_cases hw : B = w.1
        · simp [hw]
        · have : (⟨B, hvB⟩ : basesWith M v) ≠ w := fun h => hw (congrArg Subtype.val h)
          simp [hw, this]
      rw [this]
      simp [hvB]
    · have : restrictV M v (Finsupp.single B c) = 0 := by
        ext w
        rw [restrictV_apply]
        have : B ≠ w.1 := fun h => hvB (h ▸ w.2)
        simp [this]
      rw [this]
      simp [hvB]
  exact LinearMap.congr_fun this f

/-- The inclusion `𝓑(M ＼ v) → 𝓑(M)`. -/
def delInc (M : Matroid α) [M.Finite] {v : α} (hv : rk M (M.E \ {v}) = rk M M.E) :
    Bases (M ＼ {v}) → Bases M :=
  fun B => ⟨B.1, ((delete_isBase_iff_of_rk hv).1 B.2).1⟩

theorem delInc_injective (M : Matroid α) [M.Finite] {v : α} (hv : rk M (M.E \ {v}) = rk M M.E) :
    Function.Injective (delInc M hv) := by
  intro B B' h
  apply Subtype.ext
  have := congrArg Subtype.val h
  exact this

theorem incidence_delInc (M : Matroid α) [M.Finite] {v : α} (hv : rk M (M.E \ {v}) = rk M M.E)
    (h : Bases (M ＼ {v}) →₀ ℤ) :
    incidence M (Finsupp.mapDomain (delInc M hv) h) = incidence (M ＼ {v}) h := by
  simp only [incidence, Finsupp.linearCombination_mapDomain]
  rfl

/-- **Theorem 4.2 (exact sequence).** Let `M` and `M ＼ v` be connected and `|E| ≥ 2`. Then
`0 → ker_ℤ A_{M＼v} → ker_ℤ A_M → Γ → 0` is exact, where the second map is the inclusion
and the third map `π` restricts to the bases containing `v`. -/
theorem thm42 (M : Matroid α) [M.Finite] [M.RankPos] {v : α} (hM : Conn M) (hv : v ∈ M.E)
    (hne : (M.E \ {v}).Nonempty) (hMd : Conn (M ＼ {v})) :
    ∃ hrX : rk M (M.E \ {v}) = rk M M.E,
      Function.Injective (Finsupp.mapDomain (M := ℤ) (delInc M hrX)) ∧
      (∀ h, Finsupp.mapDomain (delInc M hrX) h ∈ LinearMap.ker (incidence M) ↔
        h ∈ LinearMap.ker (incidence (M ＼ {v}))) ∧
      (∀ f ∈ LinearMap.ker (incidence M), restrictV M v f = 0 →
        ∃ h ∈ LinearMap.ker (incidence (M ＼ {v})), Finsupp.mapDomain (delInc M hrX) h = f) ∧
      (∀ f ∈ LinearMap.ker (incidence M), total (restrictV M v f) = 0) ∧
      (∀ g, total g = 0 → ∃ f ∈ LinearMap.ker (incidence M), restrictV M v f = g) := by
  classical
  obtain ⟨hrv, hrX⟩ := conn_rk_facts hM hv hne
  refine ⟨hrX, Finsupp.mapDomain_injective (delInc_injective M hrX), ?_, ?_, ?_, ?_⟩
  · intro h
    simp only [LinearMap.mem_ker, incidence_delInc]
  · intro f hf hfv
    have hsupp : ↑f.support ⊆ range (delInc M hrX) := by
      intro B hB
      have hvB : v ∉ B.1 := by
        intro hvB
        have := congrArg (fun F => F ⟨B, hvB⟩) hfv
        simp only [restrictV_apply, Finsupp.coe_zero, Pi.zero_apply] at this
        exact (Finsupp.mem_support_iff.1 hB) this
      exact ⟨⟨B.1, (delete_isBase_iff_of_rk hrX).2 ⟨B.2, hvB⟩⟩, rfl⟩
    have hg := Finsupp.mapDomain_comapDomain (delInc M hrX) (delInc_injective M hrX) f hsupp
    refine ⟨_, ?_, hg⟩
    rw [LinearMap.mem_ker, ← incidence_delInc M hrX, hg]
    exact hf
  · intro f hf
    rw [total_restrictV, LinearMap.mem_ker.1 hf]
    rfl
  · intro g hg
    -- extend `g` by zero
    set f₀ := Finsupp.mapDomain (Subtype.val : basesWith M v → Bases M) g with hf₀
    have hrf₀ : restrictV M v f₀ = g := by
      ext w
      rw [restrictV_apply, hf₀, Finsupp.mapDomain_apply_of_injective Subtype.val_injective]
    set y₀ := incidence M f₀ with hy₀
    have hy₀v : y₀ v = 0 := by rw [hy₀, ← total_restrictV, hrf₀, hg]
    -- the coordinate sum of `y₀` over `E - v` is `(k - 1) ∑ g = 0`
    have hsum : ∀ g' : basesWith M v →₀ ℤ, sumOn (M.E \ {v}) (M.ground_finite.subset sdiff_subset)
        (incidence M (Finsupp.mapDomain Subtype.val g')) = (rk M M.E - 1) * total g' := by
      intro g'
      induction g' using Finsupp.induction_linear with
      | zero => simp [sumOn, total]
      | add a b ha hb =>
        rw [Finsupp.mapDomain_add, map_add]
        have h1 : total (a + b) = total a + total b := by
          simp only [total]; rw [Finsupp.sum_add_index'] <;> simp
        simp only [sumOn, Pi.add_apply, Finset.sum_add_distrib] at ha hb ⊢
        rw [ha, hb, h1]; ring
      | single w c =>
        rw [Finsupp.mapDomain_single]
        simp only [sumOn, incidence, Finsupp.linearCombination_single, Pi.smul_apply,
          Set.indicator_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        have hEv : (M.E \ {v}).Finite := M.ground_finite.subset sdiff_subset
        have h1 : ((hEv.toFinset.filter (· ∈ w.1.1) : Finset α) : Set α) = w.1.1 \ {v} := by
          ext x
          simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, mem_sdiff,
            mem_singleton_iff]
          constructor
          · rintro ⟨⟨-, hxv⟩, hx⟩; exact ⟨hx, hxv⟩
          · rintro ⟨hx, hxv⟩; exact ⟨⟨w.1.2.subset_ground hx, hxv⟩, hx⟩
        have h2 := Set.ncard_coe_finset (hEv.toFinset.filter (· ∈ w.1.1))
        rw [h1] at h2
        rw [← h2]
        have hfin : w.1.1.Finite := M.ground_finite.subset w.1.2.subset_ground
        have h3 := Set.ncard_sdiff_singleton_add_one (show v ∈ w.1.1 from w.2) hfin
        have h4 := rk_ground_eq_of_isBase w.1.2
        simp only [total, Finsupp.sum_single_index]
        have h3' : ((w.1.1 \ {v}).ncard : ℤ) = w.1.1.ncard - 1 := by
          have : ((w.1.1 \ {v}).ncard : ℤ) + 1 = w.1.1.ncard := by exact_mod_cast h3
          linarith
        rw [h4, h3']
    have hy₀sum : sumOn (M.E \ {v}) (M.ground_finite.subset sdiff_subset) y₀ = 0 := by
      rw [hy₀, hf₀, hsum, hg, mul_zero]
    -- Lemma 4.1 for `M ＼ v`
    have : (M ＼ {v}).RankPos := rankPos_delete hrX
    have hmem : -y₀ ∈ LinearMap.range (incidence (M ＼ {v})) := by
      rw [lemma41 (M ＼ {v}) hMd]
      refine ⟨fun a ha => ?_, ?_⟩
      · rw [delete_ground] at ha
        simp only [Pi.neg_apply, neg_eq_zero]
        by_cases hav : a = v
        · rw [hav]; exact hy₀v
        · have haE : a ∉ M.E := fun h => ha ⟨h, hav⟩
          rw [hy₀]; exact incidence_eq_zero_of_notMem M f₀ haE
      · have e : sumOn (M ＼ {v}).E (M ＼ {v}).ground_finite (-y₀) =
            -sumOn (M.E \ {v}) (M.ground_finite.subset sdiff_subset) y₀ := by
          simp [sumOn, delete_ground]
        rw [e, hy₀sum, neg_zero]
        exact dvd_zero _
    obtain ⟨h', hh'⟩ := hmem
    refine ⟨f₀ + Finsupp.mapDomain (delInc M hrX) h', ?_, ?_⟩
    · rw [LinearMap.mem_ker, map_add, incidence_delInc, hh', ← hy₀, add_neg_cancel]
    · rw [map_add, hrf₀]
      have : restrictV M v (Finsupp.mapDomain (delInc M hrX) h') = 0 := by
        ext w
        rw [restrictV_apply]
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨B, hB⟩
        have := ((delete_isBase_iff_of_rk hrX).1 B.2).2
        have hw := w.2
        rw [← hB] at hw
        exact this hw
      rw [this, add_zero]

/-! ### Proposition 4.4, both directions -/

/-- Two elements of `N(J)` are linked by a cocircuit through `v` (the cocircuit `E - cl(J)`). -/
theorem linked_of_nbr {M : Matroid α} [M.Finite] {v x x' : α} (a : basesWith M v)
    (hx : x ∈ nbr M v a) (hx' : x' ∈ nbr M v a) : Linked M✶ v x x' := by
  have hva : v ∈ a.1.1 := a.2
  have hxv : x ≠ v := fun h => hx.1 (h ▸ hva)
  have hx'v : x' ≠ v := fun h => hx'.1 (h ▸ hva)
  set Bs := M.E \ a.1.1 with hBs
  have hBsb : M✶.IsBase Bs := a.1.2.compl_isBase_dual
  have hvBs : v ∉ Bs := fun h => h.2 hva
  have hvE : v ∈ M.E := a.1.2.subset_ground hva
  have hrank : rk M✶ (insert v Bs) = rk M✶ Bs := by
    have h1 := rk_mono M✶ (show insert v Bs ⊆ M✶.E from
      insert_subset (by simpa using hvE) (by rw [dual_ground]; exact sdiff_subset))
    have h2 := rk_mono M✶ (subset_insert v Bs)
    have h3 : rk M✶ M✶.E = rk M✶ Bs := by
      rw [rk_ground_eq_of_isBase hBsb, rk_indep hBsb.indep]
    linarith
  obtain ⟨K, hK, hKs, hvK⟩ := exists_isCircuit_insert hBsb.indep hvBs (by simpa using hvE) hrank
  have mem : ∀ {y : α}, y ∈ nbr M v a → y ∈ K := by
    intro y hy
    by_contra hyK
    have hyBs : y ∈ Bs := ⟨hy.2.subset_ground (mem_insert _ _), hy.1⟩
    -- `Bs - y + v` is a base of `M✶`, being the complement of `J + y`
    have hb : M✶.IsBase (insert v (Bs \ {y})) := by
      have h1 := hy.2.compl_isBase_dual
      have e : M.E \ insert y (a.1.1 \ {v}) = insert v (Bs \ {y}) := by
        ext z
        simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, hBs, not_or, not_and, not_not]
        constructor
        · rintro ⟨hz, hzy, hza⟩
          by_cases hzv : z = v
          · exact Or.inl hzv
          · exact Or.inr ⟨⟨hz, fun h => hzv (hza h)⟩, hzy⟩
        · rintro (rfl | ⟨⟨hz, hza⟩, hzy⟩)
          · exact ⟨hvE, fun h => hy.1 (h ▸ hva), fun _ => rfl⟩
          · exact ⟨hz, hzy, fun h => absurd h hza⟩
      rwa [e] at h1
    apply hK.dep.not_indep (hb.indep.subset _)
    intro z hz
    rcases hKs hz with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun h' => hyK (by rw [mem_singleton_iff] at h'; exact h' ▸ hz)⟩
  exact ⟨hxv, hx'v, K, hK, hvK, mem hx, mem hx'⟩

/-- **Proposition 4.4, converse direction.** If `M` is connected and `H` is connected, then
the cocircuits of `M` through `v` link `E - v`. -/
theorem prop44_converse {M : Matroid α} [M.Finite] {v : α} (hM : Conn M) (hv : v ∈ M.E)
    (hH : ∀ a b : basesWith M v, Relation.ReflTransGen (HAdj M v) a b) :
    ∀ x ∈ M.E \ {v}, ∀ y ∈ M.E \ {v}, Relation.ReflTransGen (Linked M✶ v) x y := by
  have hMd : Conn M✶ := (conn_dual M).2 hM
  -- every `x ∈ E - v` lies in some `N(J)`
  have hcover : ∀ x ∈ M.E \ {v}, ∃ a : basesWith M v, x ∈ nbr M v a := by
    intro x hx
    have hxv : x ≠ v := fun h => hx.2 (by rw [h]; rfl)
    obtain ⟨K, hK, hvK, hxK⟩ := conn_exists_isCircuit hMd (by simpa using hv)
      (by simpa using hx.1) (Ne.symm hxv)
    obtain ⟨a, ha, -⟩ := exists_nbr_of_linked (M := M) ⟨hxv, hxv, K, hK, hvK, hxK, hxK⟩
    exact ⟨a, ha⟩
  intro x hx y hy
  obtain ⟨a, hxa⟩ := hcover x hx
  obtain ⟨b, hyb⟩ := hcover y hy
  have walk : ∀ c, Relation.ReflTransGen (HAdj M v) a c → ∀ z ∈ nbr M v c,
      Relation.ReflTransGen (Linked M✶ v) x z := by
    intro c hc
    induction hc with
    | refl => exact fun z hz => Relation.ReflTransGen.single (linked_of_nbr a hxa hz)
    | tail _ hcd ih =>
      obtain ⟨-, j, hj1, hj2, hj3, hj4⟩ := hcd
      intro z hz
      exact (ih j ⟨hj1, hj3⟩).tail (linked_of_nbr _ ⟨hj2, hj4⟩ hz)
  exact walk b (hH a b) y hyb

/-- **Proposition 4.4.** If `M` and `M ＼ v` are connected (and `|E| ≥ 2`), then `H` is
connected if and only if `Φ` is connected. -/
theorem prop44_iff {M : Matroid α} [M.Finite] {v : α} (hM : Conn M) (hv : v ∈ M.E)
    (hne : (M.E \ {v}).Nonempty) :
    (∀ a b : basesWith M v, Relation.ReflTransGen (HAdj M v) a b) ↔
      (∀ x ∈ M.E \ {v}, ∀ y ∈ M.E \ {v}, Relation.ReflTransGen (Linked M✶ v) x y) :=
  ⟨prop44_converse hM hv, prop44 (conn_rk_facts hM hv hne).2⟩

end SquareBasis
