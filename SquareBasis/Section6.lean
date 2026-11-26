module

public import SquareBasis.Uniform
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Section 6 of the paper: uniform matroids

* `rank_nullity` — `rank A_M + rank ker_ℤ A_M = N`.
* `lemma61` — **Lemma 6.1** (unitriangularity).
* `prop62` — **Proposition 6.2**: `rank A_{U_{k,n}} = n`, and the squares `r_s` (`s ∈ S`)
  form a `ℤ`-basis of `ker_ℤ A_{U_{k,n}}`.
* `example63` — **Example 6.3** (`U_{2,4}`).
-/

@[expose] public section

namespace SquareBasis

open Finset Matroid Module

universe u

/-! ### A unitriangular family -/

/-- A family `r_i` with `r_i(p_i) = ±1` and `r_i(p_j) = 0` for `i < j` is "unitriangular":
(1) a combination `∑ g_i r_i` vanishing at all `p_j` has `g = 0`, and (2) every `x` agrees at all
`p_j` with some element of the span of the `r_i`. -/
theorem unitri {ι : Type*} [LinearOrder ι] [Fintype ι] {P : Type*} (p : ι → P)
    (r : ι → (P →₀ ℤ)) (hdiag : ∀ i, r i (p i) = 1 ∨ r i (p i) = -1)
    (htri : ∀ i j, i < j → r i (p j) = 0) :
    (∀ g : ι → ℤ, (∀ j, (∑ i, g i • r i) (p j) = 0) → ∀ i, g i = 0) ∧
    ∀ x : P →₀ ℤ, ∃ l ∈ Submodule.span ℤ (Set.range r), ∀ i, x (p i) = l (p i) := by
  classical
  have hunit : ∀ i, r i (p i) * r i (p i) = 1 := fun i => by
    rcases hdiag i with h | h <;> rw [h] <;> norm_num
  constructor
  · intro g hg
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀⟩ := hne
    set U := univ.filter (fun i => g i ≠ 0) with hU
    have hUne : U.Nonempty := ⟨i₀, by simp [hU, hi₀]⟩
    set m := U.max' hUne
    have hm : g m ≠ 0 := by have := U.max'_mem hUne; simpa [hU] using this
    have := hg m
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single m] at this
    · rw [Finsupp.smul_apply, smul_eq_mul] at this
      rcases hdiag m with h | h <;> rw [h] at this <;> simp at this <;> exact hm this
    · intro i _ him
      rw [Finsupp.smul_apply, smul_eq_mul]
      by_cases hgi : g i = 0
      · rw [hgi, zero_mul]
      · have : i ≤ m := U.le_max' i (by simp [hU, hgi])
        rw [htri i m (lt_of_le_of_ne this him), mul_zero]
    · intro h; exact absurd (mem_univ m) h
  · intro x
    -- fix the coordinates from the top down: induction adding a new minimum
    suffices H : ∀ s : Finset ιᵒᵈ, ∃ l ∈ Submodule.span ℤ (Set.range r),
        ∀ i ∈ s, x (p (OrderDual.ofDual i)) = l (p (OrderDual.ofDual i)) by
      obtain ⟨l, hl, h⟩ := H univ
      exact ⟨l, hl, fun i => h (OrderDual.toDual i) (mem_univ _)⟩
    intro s
    induction s using Finset.induction_on_max with
    | empty => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | insert a s has ih =>
      obtain ⟨l, hl, h⟩ := ih
      set a' := OrderDual.ofDual a
      set d := x (p a') - l (p a')
      refine ⟨l + (d * r a' (p a')) • r a', Submodule.add_mem _ hl
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a', rfl⟩)), fun i hi => ?_⟩
      rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      rcases mem_insert.1 hi with rfl | hi
      · rw [mul_assoc, hunit]; ring
      · have hlt : a' < OrderDual.ofDual i := has i hi
        rw [htri a' _ hlt, mul_zero, add_zero, h i hi]

/-! ### Rank–nullity over `ℤ` -/

/-- `rank A_M + rank ker_ℤ A_M = N`. -/
theorem rank_nullity {α : Type u} (M : Matroid α) [M.Finite] :
    finrank ℤ (LinearMap.range (incidence M)) + finrank ℤ (LinearMap.ker (incidence M)) =
      Nat.card (Bases M) := by
  have := Fintype.ofFinite (Bases M)
  have h := LinearMap.rank_range_add_rank_ker (incidence M)
  rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at h
  rw [Nat.card_eq_fintype_card, ← finrank_finsupp_self (R := ℤ) (ι := Bases M)]
  exact_mod_cast h

/-! ### Lemma 6.1 -/

/-- The colex key of a basis. -/
noncomputable def colexKey {n : ℕ} {M : Matroid (Fin n)} (B : Bases M) :
    Colex (Finset (Fin n)) :=
  open scoped Classical in toColex (univ.filter (· ∈ B.1))

theorem colexKey_injective {n : ℕ} {M : Matroid (Fin n)} :
    Function.Injective (colexKey (M := M)) := by
  classical
  intro B B' h
  simp only [colexKey, toColex_inj] at h
  apply Subtype.ext
  ext x
  have := congrArg (x ∈ ·) h
  simpa using this

/-- The bases in `S`, ordered by colex. -/
def SubColex {n : ℕ} {M : Matroid (Fin n)} (S : Finset (Bases M)) : Type := {s // s ∈ S}

noncomputable instance {n : ℕ} {M : Matroid (Fin n)} (S : Finset (Bases M)) :
    LinearOrder (SubColex S) :=
  LinearOrder.lift' (fun s : SubColex S => colexKey s.1)
    (fun _ _ h => Subtype.ext (colexKey_injective h))

instance {n : ℕ} {M : Matroid (Fin n)} (S : Finset (Bases M)) : Fintype (SubColex S) :=
  inferInstanceAs (Fintype {s // s ∈ S})

/-- **Lemma 6.1.** Let `S` be a set of `N - rank A_M` bases, and suppose that for each `s ∈ S`
there is a square `r_s` whose `s`-coordinate is `±1` and whose support contains no element of
`S` that is colex-larger than `s`. Then `{r_s : s ∈ S}` is a `ℤ`-basis of `ker_ℤ A_M`. -/
theorem lemma61 {n : ℕ} (M : Matroid (Fin n)) (S : Finset (Bases M))
    (hS : S.card + finrank ℤ (LinearMap.range (incidence M)) = Nat.card (Bases M))
    (r : Bases M → (Bases M →₀ ℤ)) (hsq : ∀ s ∈ S, IsSquare M (r s))
    (hdiag : ∀ s ∈ S, r s s = 1 ∨ r s s = -1)
    (hsupp : ∀ s ∈ S, ∀ t ∈ S, r s t ≠ 0 → ¬ colexLt s.1 t.1) :
    LinearIndependent ℤ (fun s : S => r s) ∧
      Submodule.span ℤ (r '' S) = LinearMap.ker (incidence M) := by
  classical
  have hlt : ∀ s t : SubColex S, s < t ↔ colexLt s.1.1 t.1.1 := fun s t => Iff.rfl
  obtain ⟨hA, hB⟩ := unitri (ι := SubColex S) (fun s => s.1) (fun s => r s.1)
    (fun s => hdiag s.1 s.2)
    (fun s t hst => by
      by_contra h
      exact hsupp s.1 s.2 t.1 t.2 h ((hlt s t).1 hst))
  have hli' : LinearIndependent ℤ (fun s : SubColex S => r s.1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    exact hA g (fun j => by rw [hg]; rfl)
  have hli : LinearIndependent ℤ (fun s : S => r s) := hli'
  refine ⟨hli, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    exact (hsq s hs).mem_ker
  · intro x hx
    obtain ⟨l, hl, hxl⟩ := hB x
    have hrange : Submodule.span ℤ (Set.range (fun s : SubColex S => r s.1)) =
        Submodule.span ℤ (r '' S) := by
      congr 1
      ext v
      simp only [Set.mem_range, Set.mem_image, Finset.mem_coe]
      exact ⟨fun ⟨s, h⟩ => ⟨s.1, s.2, h⟩, fun ⟨s, hs, h⟩ => ⟨⟨s, hs⟩, h⟩⟩
    rw [hrange] at hl
    -- `y = x - l` vanishes on `S` and lies in the kernel
    set y := x - l
    have hlker : l ∈ LinearMap.ker (incidence M) := by
      refine (Submodule.span_le.2 ?_) hl
      rintro _ ⟨s, hs, rfl⟩
      exact (hsq s hs).mem_ker
    have hyker : y ∈ LinearMap.ker (incidence M) := Submodule.sub_mem _ hx hlker
    have hyS : ∀ s : SubColex S, y s.1 = 0 := fun s => by
      simp only [y, Finsupp.coe_sub, Pi.sub_apply, hxl s, sub_self]
    by_contra hxnot
    have hy0 : y ≠ 0 := by
      intro h
      apply hxnot
      have : x = l := by rw [← sub_eq_zero]; exact h
      rw [this]; exact hl
    -- then `S` together with `y` is linearly independent in `ker`: too many vectors
    let v : Option (SubColex S) → LinearMap.ker (incidence M) := fun o => match o with
      | none => ⟨y, hyker⟩
      | some s => ⟨r s.1, (hsq s.1 s.2).mem_ker⟩
    have hv : LinearIndependent ℤ v := by
      apply LinearIndependent.of_comp (LinearMap.ker (incidence M)).subtype
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hsum : ∑ s : SubColex S, g (some s) • r s.1 = - (g none • y) := by
        rw [Fintype.sum_option] at hg
        simp only [Function.comp_apply, Submodule.subtype_apply, v] at hg
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hg
      have hg' := hA (fun s => g (some s)) (fun j => by
        rw [hsum, Finsupp.neg_apply, Finsupp.smul_apply, hyS j, smul_zero, neg_zero])
      have hnone : g none = 0 := by
        have : g none • y = 0 := by
          rw [← neg_eq_zero, ← hsum]
          simp [hg']
        exact (smul_eq_zero.1 this).resolve_right hy0
      intro o
      cases o with
      | none => exact hnone
      | some s => exact hg' s
    have hcard : Fintype.card (Option (SubColex S)) ≤
        finrank ℤ (LinearMap.ker (incidence M)) := hv.fintype_card_le_finrank
    have hcS : Fintype.card (SubColex S) = S.card := Fintype.card_coe S
    rw [Fintype.card_option, hcS] at hcard
    have := rank_nullity M
    omega

/-! ### Proposition 6.2 -/

variable {n : ℕ} (k : ℕ)

open scoped Classical in
/-- The basis vector `e_X` of `ℤ^𝓑(U_{k,n})` for a finset `X` (zero if `X` is not a basis). -/
noncomputable def eF (X : Finset (Fin n)) : Bases (unif k n) →₀ ℤ :=
  if h : (unif k n).IsBase (X : Set (Fin n)) then Finsupp.single ⟨X, h⟩ 1 else 0

theorem eF_of_card (hk : k ≤ n) {X : Finset (Fin n)} (hX : X.card = k) :
    eF k X = Finsupp.single ⟨X, (unif_isBase_coe_iff hk).2 hX⟩ 1 := by
  rw [eF, dite_eq_left]

/-- The square `r_s = z_{i,j;B,B'}` of Proposition 6.2. -/
noncomputable def rS (hk : k < n) (s : Finset (Fin n)) : Bases (unif k n) →₀ ℤ :=
  eF k (insert (iOf k hk s) (BOf k hk s)) - eF k (insert (jOf k hk s) (BOf k hk s))
    - eF k (insert (iOf k hk s) (BpOf k hk s)) + eF k (insert (jOf k hk s) (BpOf k hk s))

/-- A `k`-set as a basis of `U_{k,n}`. -/
def toBase (hk : k ≤ n) (X : Finset (Fin n)) (hX : X.card = k) : Bases (unif k n) :=
  ⟨X, (unif_isBase_coe_iff hk).2 hX⟩

/-- The rows: `A_{U_{k,n}} e_X = 𝟙_X`. -/
theorem incidence_single_coe {M : Matroid (Fin n)} (X : Finset (Fin n)) (h : M.IsBase X) :
    incidence M (Finsupp.single ⟨X, h⟩ 1) = ∑ y ∈ X, Pi.single y (1 : ℤ) := by
  classical
  rw [incidence, Finsupp.linearCombination_single, one_smul]
  funext z
  simp only [Set.indicator_apply, Finset.mem_coe, Finset.sum_apply, Pi.single_apply,
    Finset.sum_ite_eq]

/-- For `1 ≤ k ≤ n - 1`, `rank A_{U_{k,n}} = n`. -/
theorem rank_unif (hk1 : 1 ≤ k) (hk : k < n) :
    finrank ℤ (LinearMap.range (incidence (unif k n))) = n := by
  apply le_antisymm
  · have := Submodule.finrank_le (LinearMap.range (incidence (unif k n)))
    rwa [finrank_fintype_fun_eq_card, Fintype.card_fin] at this
  -- `k e_x` lies in the range for every `x`
  have hdiff : ∀ x y : Fin n, x ≠ y →
      Pi.single x (1 : ℤ) - Pi.single y 1 ∈ LinearMap.range (incidence (unif k n)) := by
    intro x y hxy
    obtain ⟨D, hD, hDc⟩ := Finset.exists_subset_card_eq (s := (univ.erase x).erase y)
      (n := k - 1) (by
        rw [card_erase_of_mem (mem_erase.2 ⟨hxy.symm, mem_univ y⟩),
          card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]; omega)
    have hxD : x ∉ D := fun h => by have := hD h; simp at this
    have hyD : y ∉ D := fun h => by have := hD h; simp at this
    have h1 : (insert x D).card = k := by rw [card_insert_of_notMem hxD, hDc]; omega
    have h2 : (insert y D).card = k := by rw [card_insert_of_notMem hyD, hDc]; omega
    refine ⟨Finsupp.single (toBase k hk.le _ h1) 1 - Finsupp.single (toBase k hk.le _ h2) 1, ?_⟩
    rw [map_sub, toBase, toBase, incidence, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, one_smul, one_smul]
    simp only [Finset.coe_insert]
    convert indicator_insert_sub (Finset.mem_coe.not.2 hxD) (Finset.mem_coe.not.2 hyD) using 3
  have hmul : ∀ x : Fin n, (k : ℤ) • Pi.single x (1 : ℤ) ∈
      LinearMap.range (incidence (unif k n)) := by
    intro x
    obtain ⟨D, hD, hDc⟩ := Finset.exists_subset_card_eq (s := univ.erase x) (n := k - 1) (by
        rw [card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]; omega)
    have hxD : x ∉ D := fun h => by have := hD h; simp at this
    set I := insert x D
    have hI : I.card = k := by rw [card_insert_of_notMem hxD, hDc]; omega
    have hsum : (k : ℤ) • Pi.single x (1 : ℤ) = (∑ y ∈ I, Pi.single y (1 : ℤ)) +
        ∑ y ∈ D, (Pi.single x (1 : ℤ) - Pi.single y 1) := by
      rw [sum_insert hxD, sum_sub_distrib, sum_const, hDc]
      have : (k : ℤ) = 1 + ((k - 1 : ℕ) : ℤ) := by omega
      rw [this, add_smul, one_smul, natCast_zsmul]
      abel
    rw [hsum]
    refine Submodule.add_mem _ ⟨Finsupp.single (toBase k hk.le I hI) 1, ?_⟩
      (Submodule.sum_mem _ fun y hy => hdiff x y fun h => hxD (h ▸ hy))
    exact incidence_single_coe I _
  let v : Fin n → LinearMap.range (incidence (unif k n)) := fun x => ⟨_, hmul x⟩
  have hv : LinearIndependent ℤ v := by
    apply LinearIndependent.of_comp (LinearMap.range (incidence (unif k n))).subtype
    rw [Fintype.linearIndependent_iff]
    intro g hg x
    have := congrFun hg x
    simp only [Function.comp_apply, Submodule.subtype_apply, v, Finset.sum_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.zero_apply] at this
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    exact (mul_eq_zero.1 this).resolve_right hk0
  have := hv.fintype_card_le_finrank
  rwa [Fintype.card_fin] at this

/-- The number of bases of `U_{k,n}` is the number of `k`-subsets. -/
theorem card_bases_unif (hk : k ≤ n) :
    Nat.card (Bases (unif k n)) = (univ.powersetCard k : Finset (Finset (Fin n))).card := by
  classical
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun B => ⟨B.1.toFinset, ?_⟩
      invFun := fun X => toBase k hk X.1 (mem_powersetCard.1 X.2).2
      left_inv := fun B => Subtype.ext (by simp [toBase])
      right_inv := fun X => Subtype.ext (by ext; exact Iff.trans Set.mem_toFinset Finset.mem_coe) }
  rw [mem_powersetCard]
  refine ⟨subset_univ _, ?_⟩
  have := (unif_isBase_iff hk).1 B.2
  rwa [← Set.ncard_coe_finset, Set.coe_toFinset]

/-- The image of `S` in the bases of `U_{k,n}`. -/
noncomputable def Sbases (hk : k < n) : Finset (Bases (unif k n)) :=
  (Sset k hk).attach.image fun s => toBase k hk.le s.1
    (by have := s.2; simp only [Sset, mem_filter, mem_powersetCard] at this; exact this.1.2)

open scoped Classical in
/-- The finset of a basis of `U_{k,n}`. -/
noncomputable def finsetOf (b : Bases (unif k n)) : Finset (Fin n) := univ.filter (· ∈ b.1)

theorem finsetOf_toBase (hk : k ≤ n) (X : Finset (Fin n)) (hX : X.card = k) :
    finsetOf k (toBase k hk X hX) = X := by
  classical
  ext x; simp [finsetOf, toBase]

theorem toBase_injective (hk : k ≤ n) {X Y : Finset (Fin n)} (hX : X.card = k) (hY : Y.card = k)
    (h : toBase k hk X hX = toBase k hk Y hY) : X = Y := by
  have := congrArg (finsetOf k) h
  rwa [finsetOf_toBase, finsetOf_toBase] at this

theorem eF_apply (hk : k ≤ n) {X : Finset (Fin n)} (hX : X.card = k) (t : Bases (unif k n)) :
    eF k X t = if t = toBase k hk X hX then 1 else 0 := by
  classical
  rw [eF_of_card k hk hX, Finsupp.single_apply]
  simp only [toBase]
  split_ifs with h1 h2 h2
  · simp [h2]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp [h2]

theorem mem_Sset (hk : k < n) {s : Finset (Fin n)} :
    s ∈ Sset k hk ↔ s.card = k ∧ s ∉ Tset k hk := by
  simp [Sset, mem_powersetCard]

/-- The four sets of `r_s` have size `k`, and `r_s` is a square, with `B + i = s`. -/
theorem rS_data (hk1 : 1 ≤ k) (hk : k < n) {s : Finset (Fin n)} (hs : s ∈ Sset k hk) :
    let i := iOf k hk s
    let B := BOf k hk s
    let j := jOf k hk s
    let B' := BpOf k hk s
    (insert i B).card = k ∧ (insert j B).card = k ∧ (insert i B').card = k ∧
      (insert j B').card = k ∧ insert i B = s ∧ toColex (insert j B) < toColex s ∧
      toColex (insert i B') < toColex s ∧ toColex (insert j B') < toColex s ∧
      IsSquare (unif k n) (rS k hk s) := by
  intro i B j B'
  obtain ⟨hsB, hiB, hBc, hB'c, hji, hjB, hjB', hiB', hBlt, hB'lt, hlex⟩ := S_data k hk1 hk hs
  have c1 : (insert i B).card = k := by rw [card_insert_of_notMem hiB, hBc]; omega
  have c2 : (insert j B).card = k := by rw [card_insert_of_notMem hjB, hBc]; omega
  have c3 : (insert i B').card = k := by rw [card_insert_of_notMem hiB', hB'c]; omega
  have c4 : (insert j B').card = k := by rw [card_insert_of_notMem hjB', hB'c]; omega
  have his : i ∈ s := hsB ▸ mem_insert_self i B
  refine ⟨c1, c2, c3, c4, hsB.symm, ?_, ?_, ?_, ?_⟩
  · refine colex_lt_of_forall_lt his fun x hx => ?_
    rcases mem_insert.1 hx with rfl | hx; exacts [hji, hBlt x hx]
  · rw [hsB]; exact colex_insert_lt_insert hiB hlex
  · refine colex_lt_of_forall_lt his fun x hx => ?_
    rcases mem_insert.1 hx with rfl | hx; exacts [hji, hB'lt x hx]
  · have b1 := (unif_isBase_coe_iff hk.le).2 c1
    have b2 := (unif_isBase_coe_iff hk.le).2 c2
    have b3 := (unif_isBase_coe_iff hk.le).2 c3
    have b4 := (unif_isBase_coe_iff hk.le).2 c4
    rw [Finset.coe_insert] at b1 b2 b3 b4
    have hBB' : (B : Set (Fin n)) ≠ B' := by
      intro h; rw [Finset.coe_inj] at h
      have hl : toColex B' < toColex B := hlex
      rw [h] at hl; exact lt_irrefl _ hl
    refine ⟨i, j, B, B', b1, b2, b3, b4, (ne_of_lt hji).symm, hBB',
      Finset.mem_coe.not.2 hiB, Finset.mem_coe.not.2 hjB, Finset.mem_coe.not.2 hiB',
      Finset.mem_coe.not.2 hjB', ?_⟩
    change eF k (insert i B) - eF k (insert j B) - eF k (insert i B') + eF k (insert j B') = _
    rw [eF_of_card k hk.le c1, eF_of_card k hk.le c2, eF_of_card k hk.le c3,
      eF_of_card k hk.le c4]
    rw [single_congr _ b1 (Finset.coe_insert i B), single_congr _ b2 (Finset.coe_insert j B),
      single_congr _ b3 (Finset.coe_insert i B'), single_congr _ b4 (Finset.coe_insert j B')]

/-- **Proposition 6.2.** For `1 ≤ k ≤ n - 1`: `rank A_{U_{k,n}} = n`; `T` consists of `n`
subsets of size `k`; each `r_s` (`s ∈ S`) is a square; and the squares `r_s` form a `ℤ`-basis
of `ker_ℤ A_{U_{k,n}}`. -/
theorem prop62 (hk1 : 1 ≤ k) (hk : k < n) :
    finrank ℤ (LinearMap.range (incidence (unif k n))) = n ∧
    ((Tset k hk).card = n ∧ ∀ X ∈ Tset k hk, X.card = k) ∧
    (∀ s ∈ Sset k hk, IsSquare (unif k n) (rS k hk s)) ∧
    LinearIndependent ℤ (fun s : Sset k hk => rS k hk s) ∧
    Submodule.span ℤ (rS k hk '' (Sset k hk : Set (Finset (Fin n)))) =
      LinearMap.ker (incidence (unif k n)) := by
  classical
  have hrank := rank_unif k hk1 hk
  have hT := Tset_card k hk1 hk
  have hsq : ∀ s ∈ Sset k hk, IsSquare (unif k n) (rS k hk s) :=
    fun s hs => (rS_data k hk1 hk hs).2.2.2.2.2.2.2.2
  refine ⟨hrank, hT, hsq, ?_⟩
  have hcS : ∀ s ∈ Sset k hk, s.card = k := fun s hs => ((mem_Sset k hk).1 hs).1
  -- `S` as a set of bases, and `r`
  let φ : Sset k hk → Bases (unif k n) := fun s => toBase k hk.le s.1 (hcS s.1 s.2)
  have hφinj : Function.Injective φ := fun a b h =>
    Subtype.ext (toBase_injective k hk.le _ _ h)
  let Sb : Finset (Bases (unif k n)) := univ.image φ
  let r : Bases (unif k n) → (Bases (unif k n) →₀ ℤ) := fun b => rS k hk (finsetOf k b)
  have hrφ : ∀ s, r (φ s) = rS k hk s.1 := fun s => by
    simp only [r, φ, finsetOf_toBase]
  have hmemSb : ∀ {b}, b ∈ Sb ↔ ∃ s, φ s = b := by simp [Sb]
  -- the cardinality condition
  have hSbcard : Sb.card = (Sset k hk).card := by
    rw [card_image_of_injective _ hφinj, card_univ, Fintype.card_coe]
  have hScard : (Sset k hk).card + n = (univ.powersetCard k : Finset (Finset (Fin n))).card := by
    have hsub : Tset k hk ⊆ univ.powersetCard k := fun X hX =>
      mem_powersetCard.2 ⟨subset_univ _, hT.2 X hX⟩
    have : Sset k hk = univ.powersetCard k \ Tset k hk := by
      ext X; simp [Sset, mem_powersetCard]
    rw [this, card_sdiff_of_subset hsub, hT.1]
    have := card_le_card hsub
    omega
  have hS : Sb.card + finrank ℤ (LinearMap.range (incidence (unif k n))) =
      Nat.card (Bases (unif k n)) := by
    rw [hSbcard, hrank, hScard, card_bases_unif k hk.le]
  have hsqb : ∀ b ∈ Sb, IsSquare (unif k n) (r b) := by
    intro b hb
    obtain ⟨s, rfl⟩ := hmemSb.1 hb
    rw [hrφ]; exact hsq s.1 s.2
  have hdiag : ∀ b ∈ Sb, r b b = 1 ∨ r b b = -1 := by
    intro b hb
    obtain ⟨s, rfl⟩ := hmemSb.1 hb
    left
    obtain ⟨c1, c2, c3, c4, hs, l2, l3, l4, -⟩ := rS_data k hk1 hk s.2
    rw [hrφ]
    simp only [rS, Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply]
    rw [eF_apply k hk.le c1, eF_apply k hk.le c2, eF_apply k hk.le c3, eF_apply k hk.le c4]
    have e1 : φ s = toBase k hk.le _ c1 := by
      simp only [φ]; congr 1; exact hs.symm
    have ne : ∀ {X : Finset (Fin n)} (hX : X.card = k), toColex X < toColex s.1 →
        φ s ≠ toBase k hk.le X hX := by
      intro X hX hlt h
      have := toBase_injective k hk.le _ _ h
      rw [← this] at hlt; exact lt_irrefl _ hlt
    rw [ite_eq_left e1, ite_eq_right (ne c2 l2), ite_eq_right (ne c3 l3), ite_eq_right (ne c4 l4)]
    norm_num
  have hsupp : ∀ b ∈ Sb, ∀ t ∈ Sb, r b t ≠ 0 → ¬ colexLt b.1 t.1 := by
    intro b hb t ht hne hlt
    obtain ⟨s, rfl⟩ := hmemSb.1 hb
    obtain ⟨s', rfl⟩ := hmemSb.1 ht
    obtain ⟨c1, c2, c3, c4, hs, l2, l3, l4, -⟩ := rS_data k hk1 hk s.2
    rw [hrφ] at hne
    simp only [rS, Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply] at hne
    rw [eF_apply k hk.le c1, eF_apply k hk.le c2, eF_apply k hk.le c3,
      eF_apply k hk.le c4] at hne
    have hlt' : toColex s.1 < toColex s'.1 := by
      have := (colexLt_coe s.1 s'.1).1
      exact this hlt
    -- `s'` is one of the four sets, all colex-`≤ s`
    have key : ∀ {X : Finset (Fin n)} (hX : X.card = k), toColex X ≤ toColex s.1 →
        φ s' ≠ toBase k hk.le X hX := by
      intro X hX hle h
      have := toBase_injective k hk.le _ _ h
      rw [this] at hlt'; exact absurd hlt' (not_lt.2 hle)
    rw [ite_eq_right (key c1 (by rw [hs])), ite_eq_right (key c2 l2.le), ite_eq_right (key c3 l3.le),
      ite_eq_right (key c4 l4.le)] at hne
    exact hne (by norm_num)
  obtain ⟨hli, hspan⟩ := lemma61 (unif k n) Sb hS r hsqb hdiag hsupp
  -- transport back to `S`
  let ψ : Sset k hk → Sb := fun s => ⟨φ s, hmemSb.2 ⟨s, rfl⟩⟩
  have hψ : Function.Injective ψ := fun a b h => hφinj (congrArg Subtype.val h)
  refine ⟨?_, ?_⟩
  · have := hli.comp ψ hψ
    convert this using 1
    funext s
    simp only [Function.comp_apply, ψ, hrφ]
  · rw [← hspan]
    congr 1
    ext v
    simp only [Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨φ ⟨s, hs⟩, hmemSb.2 ⟨⟨s, hs⟩, rfl⟩, hrφ _⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨s, rfl⟩ := hmemSb.1 hb
      exact ⟨s.1, s.2, (hrφ s).symm⟩

/-! ### Example 6.3 -/

/-- **Example 6.3.** For `U_{2,4}`: `T = {12, 13, 14, 23}`, `S = {24, 34}`,
`r_{24} = e_{24} - e_{23} - e_{14} + e_{13}` and `r_{34} = e_{34} - e_{23} - e_{14} + e_{12}`
(paper indices; here every element is shifted down by one). -/
theorem example63 :
    Tset 2 (n := 4) (by norm_num) = {{0, 1}, {0, 2}, {0, 3}, {1, 2}} ∧
    Sset 2 (n := 4) (by norm_num) = {{1, 3}, {2, 3}} ∧
    rS 2 (n := 4) (by norm_num) {1, 3} = eF 2 {1, 3} - eF 2 {1, 2} - eF 2 {0, 3} + eF 2 {0, 2} ∧
    rS 2 (n := 4) (by norm_num) {2, 3} = eF 2 {2, 3} - eF 2 {1, 2} - eF 2 {0, 3} + eF 2 {0, 1} := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · have h1 : iOf 2 (n := 4) (by norm_num) {1, 3} = 3 := by decide
    have h2 : BOf 2 (n := 4) (by norm_num) {1, 3} = {1} := by decide
    have h3 : jOf 2 (n := 4) (by norm_num) {1, 3} = 2 := by decide
    have h4 : BpOf 2 (n := 4) (by norm_num) {1, 3} = {0} := by decide
    rw [rS, h1, h2, h3, h4,
      show (insert (3 : Fin 4) {1} : Finset (Fin 4)) = {1, 3} by decide,
      show (insert (2 : Fin 4) {1} : Finset (Fin 4)) = {1, 2} by decide,
      show (insert (3 : Fin 4) {0} : Finset (Fin 4)) = {0, 3} by decide,
      show (insert (2 : Fin 4) {0} : Finset (Fin 4)) = {0, 2} by decide]
  · have h1 : iOf 2 (n := 4) (by norm_num) {2, 3} = 3 := by decide
    have h2 : BOf 2 (n := 4) (by norm_num) {2, 3} = {2} := by decide
    have h3 : jOf 2 (n := 4) (by norm_num) {2, 3} = 1 := by decide
    have h4 : BpOf 2 (n := 4) (by norm_num) {2, 3} = {0} := by decide
    rw [rS, h1, h2, h3, h4,
      show (insert (3 : Fin 4) {2} : Finset (Fin 4)) = {2, 3} by decide,
      show (insert (1 : Fin 4) {2} : Finset (Fin 4)) = {1, 2} by decide,
      show (insert (3 : Fin 4) {0} : Finset (Fin 4)) = {0, 3} by decide,
      show (insert (1 : Fin 4) {0} : Finset (Fin 4)) = {0, 1} by decide]

end SquareBasis
