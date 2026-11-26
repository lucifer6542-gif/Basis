module

public import SquareBasis.Section6
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Corollary 7.1 of the paper (toric ideals)

`K[y] = K[y_I : I ∈ 𝓑]`, `p = ∏_I y_I`, and `𝒴 = K[y][p⁻¹] = K[y^{±1}]`, realized as the group
algebra `K[ℤ^𝓑]` (`Laurent`); `isLocalization` shows that it is the localization of `K[y]` at the
powers of `p`. The toric ideal `I_M` is the kernel of the monomial map `y_I ↦ ∏_{i ∈ I} x_i`.
For `z ∈ ℤ^𝓑`, `f_z = y^{z⁺} - y^{z⁻}` (`binom`), and `J : p^∞` is `satP J`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace SquareBasis

open Matroid Module

variable {α : Type*} (M : Matroid α) [M.Finite] (K : Type*) [Field K]

noncomputable instance : Fintype (Bases M) := Fintype.ofFinite _

/-! ### The objects -/

section Defs

open scoped Classical

/-- `𝟙_B ∈ ℕ^α`. -/
noncomputable def indN (B : Bases M) : α →₀ ℕ :=
  ∑ x ∈ M.ground_finite.toFinset.filter (· ∈ B.1), Finsupp.single x 1

/-- `A_M` on exponent vectors. -/
noncomputable def Aexp : (Bases M →₀ ℕ) →+ (α →₀ ℕ) :=
  Finsupp.liftAddHom fun B => multiplesHom (α →₀ ℕ) (indN M B)

/-- The monomial map `K[y] → K[x]`, `y_B ↦ ∏_{i ∈ B} x_i`. -/
noncomputable def phi : MvPolynomial (Bases M) K →ₐ[K] MvPolynomial α K :=
  AddMonoidAlgebra.mapDomainAlgHom K K (Aexp M)

/-- The toric ideal `I_M`. -/
noncomputable def toricIdeal : Ideal (MvPolynomial (Bases M) K) := RingHom.ker (phi M K)

/-- `𝒴 = K[y^{±1}] = K[ℤ^𝓑]`. -/
abbrev Laurent := AddMonoidAlgebra K (Bases M →₀ ℤ)

/-- `ℕ^𝓑 → ℤ^𝓑`. -/
noncomputable def castZ : (Bases M →₀ ℕ) →+ (Bases M →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

/-- `K[y] → 𝒴`. -/
noncomputable def iY : MvPolynomial (Bases M) K →ₐ[K] Laurent M K :=
  AddMonoidAlgebra.mapDomainAlgHom K K (castZ M)

noncomputable instance : Algebra (MvPolynomial (Bases M) K) (Laurent M K) :=
  (iY M K).toRingHom.toAlgebra

/-- `p = ∏_I y_I`. -/
noncomputable def pM : MvPolynomial (Bases M) K := ∏ B, MvPolynomial.X B

/-- `y^u ∈ 𝒴`. -/
noncomputable def ymon (u : Bases M →₀ ℤ) : Laurent M K := AddMonoidAlgebra.single u 1

/-- `(1, …, 1) ∈ ℤ^𝓑`. -/
noncomputable def oneV : Bases M →₀ ℤ := ∑ B, Finsupp.single B 1

/-- `z⁺`. -/
noncomputable def zpos (z : Bases M →₀ ℤ) : Bases M →₀ ℕ := Finsupp.mapRange Int.toNat (by simp) z

/-- `z⁻`. -/
noncomputable def zneg (z : Bases M →₀ ℤ) : Bases M →₀ ℕ := Finsupp.mapRange (fun a => (-a).toNat) (by simp) z

/-- `f_z = y^{z⁺} - y^{z⁻}`. -/
noncomputable def binom (z : Bases M →₀ ℤ) : MvPolynomial (Bases M) K :=
  MvPolynomial.monomial (zpos M z) 1 - MvPolynomial.monomial (zneg M z) 1

/-- The `p`-saturation `J : p^∞`. -/
noncomputable def satP (J : Ideal (MvPolynomial (Bases M) K)) : Ideal (MvPolynomial (Bases M) K) where
  carrier := {f | ∃ m : ℕ, pM M K ^ m * f ∈ J}
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [mul_add, pow_add]
    exact J.add_mem (by rw [mul_right_comm]; exact J.mul_mem_right _ ha)
      (by rw [mul_assoc]; exact J.mul_mem_left _ hb)
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c f ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact J.mul_mem_left _ ha

/-- `K[ℤ^𝓑] → K[ℤ^𝓑 / L]`. -/
noncomputable def chi (L : Submodule ℤ (Bases M →₀ ℤ)) :
    Laurent M K →ₐ[K] AddMonoidAlgebra K ((Bases M →₀ ℤ) ⧸ L) :=
  AddMonoidAlgebra.mapDomainAlgHom K K L.mkQ.toAddMonoidHom

/-- The lattice ideal of `L` in `𝒴`, as the kernel of `𝒴 → K[ℤ^𝓑 / L]`. -/
noncomputable def latKer (L : Submodule ℤ (Bases M →₀ ℤ)) : Ideal (Laurent M K) :=
  RingHom.ker (chi M K L)

/-- `c = rank ker_ℤ A_M` (`= N - rank A_M` by `rank_nullity`). -/
noncomputable def codim : ℕ := finrank ℤ (LinearMap.ker (incidence M))

end Defs

/-! ### Basic computations -/

variable {M K}

theorem algebraMap_eq : algebraMap (MvPolynomial (Bases M) K) (Laurent M K) = (iY M K).toRingHom :=
  rfl

theorem iY_monomial (a : Bases M →₀ ℕ) (c : K) :
    iY M K (MvPolynomial.monomial a c) = AddMonoidAlgebra.single (castZ M a) c := by
  simp [iY, MvPolynomial.monomial, AddMonoidAlgebra.mapDomainAlgHom_apply]

theorem ymon_add (u v : Bases M →₀ ℤ) : ymon M K (u + v) = ymon M K u * ymon M K v := by
  simp [ymon, AddMonoidAlgebra.single_mul_single]

theorem ymon_zero : ymon M K 0 = 1 := rfl

theorem ymon_mul_neg (u : Bases M →₀ ℤ) : ymon M K u * ymon M K (-u) = 1 := by
  rw [← ymon_add, add_neg_cancel, ymon_zero]

theorem isUnit_ymon (u : Bases M →₀ ℤ) : IsUnit (ymon M K u) :=
  ⟨⟨ymon M K u, ymon M K (-u), ymon_mul_neg u, by rw [mul_comm]; exact ymon_mul_neg u⟩, rfl⟩

theorem ymon_nsmul (m : ℕ) (u : Bases M →₀ ℤ) : ymon M K (m • u) = ymon M K u ^ m := by
  induction m with
  | zero => simp [ymon_zero]
  | succ m ih => rw [succ_nsmul, ymon_add, ih, pow_succ]

theorem castZ_injective : Function.Injective (castZ M) := by
  intro a b h
  ext B
  have := congrArg (fun f => f B) h
  simpa [castZ] using this

theorem iY_injective : Function.Injective (iY M K) := by
  intro a b h
  exact AddMonoidAlgebra.mapDomain_injective (castZ_injective (M := M)) h

theorem iY_pM : iY M K (pM M K) = ymon M K (oneV M) := by
  classical
  rw [pM, map_prod, oneV]
  induction (Finset.univ : Finset (Bases M)) using Finset.induction_on with
  | empty => simp [ymon_zero]
  | insert B s hB ih =>
    rw [Finset.prod_insert hB, Finset.sum_insert hB, ih, ymon_add, MvPolynomial.X,
      iY_monomial]
    congr 1
    simp [ymon, castZ]

theorem castZ_zpos_sub_zneg (z : Bases M →₀ ℤ) : castZ M (zpos M z) - castZ M (zneg M z) = z := by
  ext B
  simp [castZ, zpos, zneg]
  omega

theorem iY_binom (z : Bases M →₀ ℤ) :
    iY M K (binom M K z) = ymon M K (castZ M (zneg M z)) * (ymon M K z - 1) := by
  have h : castZ M (zneg M z) + z = castZ M (zpos M z) := by
    calc _ = castZ M (zneg M z) + (castZ M (zpos M z) - castZ M (zneg M z)) := by
          rw [castZ_zpos_sub_zneg]
      _ = _ := by abel
  rw [binom, map_sub, iY_monomial, iY_monomial, mul_sub, mul_one, ← ymon_add, h]
  rfl

/-! ### `𝒴` is the localization of `K[y]` at `p` -/

theorem oneV_apply (B : Bases M) : oneV M B = 1 := by
  classical
  simp [oneV, Finsupp.finsetSum_apply, Finsupp.single_apply]

instance isLocalization : IsLocalization (Submonoid.powers (pM M K)) (Laurent M K) := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, rfl⟩
    rw [map_pow, algebraMap_eq]
    exact (by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, iY_pM]; exact isUnit_ymon _ :
      IsUnit ((iY M K).toRingHom (pM M K))).pow m
  · intro z
    induction z using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨(0, 1), by simp⟩
    | add f g hf hg =>
      obtain ⟨⟨a, s⟩, hs⟩ := hf
      obtain ⟨⟨b, t⟩, ht⟩ := hg
      refine ⟨(a * t + b * s, s * t), ?_⟩
      simp only [Submonoid.coe_mul, map_mul, map_add] at hs ht ⊢
      rw [← hs, ← ht]; ring
    | single u c =>
      let m : ℕ := ∑ B, (u B).natAbs
      have hm : ∀ B, (u B).natAbs ≤ m := fun B =>
        Finset.single_le_sum (f := fun B => (u B).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ B)
      let v : Bases M →₀ ℤ := u + m • oneV M
      have hv : castZ M (Finsupp.mapRange Int.toNat (by simp) v) = v := by
        ext B
        have h1 := hm B
        have h2 : 0 ≤ v B := by
          simp only [v, Finsupp.add_apply, Finsupp.smul_apply, oneV_apply, nsmul_eq_mul,
            mul_one]
          omega
        simp [castZ, Int.toNat_of_nonneg h2]
      refine ⟨(MvPolynomial.monomial (Finsupp.mapRange Int.toNat (by simp) v) c,
        ⟨pM M K ^ m, m, rfl⟩), ?_⟩
      simp only [algebraMap_eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, iY_pM,
        iY_monomial, hv]
      rw [← ymon_nsmul, ymon, AddMonoidAlgebra.single_mul_single, mul_one]
  · intro x y h
    exact ⟨1, by rw [iY_injective h]⟩

/-! ### Lattice ideals in `𝒴` -/

theorem mapDomain_comp' {G H T : Type*} [AddMonoid G] [AddMonoid H] [AddMonoid T] (f : G → H)
    (g : H → T) (x : AddMonoidAlgebra K G) :
    AddMonoidAlgebra.mapDomain (g ∘ f) x =
      AddMonoidAlgebra.mapDomain g (AddMonoidAlgebra.mapDomain f x) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp [AddMonoidAlgebra.mapDomain_zero]
  | add x y hx hy => rw [AddMonoidAlgebra.mapDomain_add, hx, hy, AddMonoidAlgebra.mapDomain_add,
      AddMonoidAlgebra.mapDomain_add]
  | single m r => simp [AddMonoidAlgebra.mapDomain_single]

theorem chi_apply (L : Submodule ℤ (Bases M →₀ ℤ)) (x : Laurent M K) :
    chi M K L x = AddMonoidAlgebra.mapDomain L.mkQ x := by
  simp [chi, AddMonoidAlgebra.mapDomainAlgHom_apply]

theorem chi_ymon (L : Submodule ℤ (Bases M →₀ ℤ)) (u : Bases M →₀ ℤ) :
    chi M K L (ymon M K u) = AddMonoidAlgebra.single (L.mkQ u) 1 := by
  rw [chi_apply, ymon, AddMonoidAlgebra.mapDomain_single]

/-- `y^u - 1 ∈ 𝔞_L` iff `u ∈ L`. -/
theorem ymon_sub_one_mem_latKer (L : Submodule ℤ (Bases M →₀ ℤ)) (u : Bases M →₀ ℤ) :
    ymon M K u - 1 ∈ latKer M K L ↔ u ∈ L := by
  rw [latKer, RingHom.mem_ker, map_sub, map_one, sub_eq_zero, chi_ymon, AddMonoidAlgebra.one_def,
    ← map_zero L.mkQ, AddMonoidAlgebra.single_left_inj one_ne_zero, ← sub_eq_zero, ← map_sub,
    sub_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

variable (M K) in
/-- The ideal `(y^u - 1 : u ∈ L)` of `𝒴`. -/
noncomputable def latGen (L : Submodule ℤ (Bases M →₀ ℤ)) : Ideal (Laurent M K) :=
  Ideal.span {x | ∃ u ∈ L, x = ymon M K u - 1}

/-- The kernel of `𝒴 → K[ℤ^𝓑/L]` is generated by the `y^u - 1`, `u ∈ L`. -/
theorem latKer_eq_latGen (L : Submodule ℤ (Bases M →₀ ℤ)) : latKer M K L = latGen M K L := by
  apply le_antisymm
  · intro h hh
    let r := Function.surjInv (Submodule.mkQ_surjective L)
    have hr : ∀ q, L.mkQ (r q) = q := Function.surjInv_eq _
    have key : ∀ x : Laurent M K,
        x - AddMonoidAlgebra.mapDomain (r ∘ L.mkQ) x ∈ latGen M K L := by
      intro x
      induction x using AddMonoidAlgebra.induction_linear with
      | zero => simp [AddMonoidAlgebra.mapDomain_zero]
      | add x y hx hy =>
        rw [AddMonoidAlgebra.mapDomain_add, add_sub_add_comm]; exact add_mem hx hy
      | single u c =>
        rw [AddMonoidAlgebra.mapDomain_single]
        have hmem : u - r (L.mkQ u) ∈ L := by
          rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hr, sub_self]
        have : AddMonoidAlgebra.single u c - AddMonoidAlgebra.single (r (L.mkQ u)) c =
            AddMonoidAlgebra.single (r (L.mkQ u)) c * (ymon M K (u - r (L.mkQ u)) - 1) := by
          rw [ymon, mul_sub, mul_one, AddMonoidAlgebra.single_mul_single, mul_one,
            add_sub_cancel]
        simp only [Function.comp_apply]
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, hmem, rfl⟩)
    have h0 : AddMonoidAlgebra.mapDomain (r ∘ L.mkQ) h = 0 := by
      rw [mapDomain_comp', ← chi_apply, (RingHom.mem_ker).1 hh, AddMonoidAlgebra.mapDomain_zero]
    simpa [h0] using key h
  · rw [latGen, Ideal.span_le]
    rintro _ ⟨u, hu, rfl⟩
    exact (ymon_sub_one_mem_latKer L u).2 hu

theorem latKer_mono {L L' : Submodule ℤ (Bases M →₀ ℤ)} (h : L ≤ L') :
    latKer M K L ≤ latKer M K L' := by
  rw [latKer_eq_latGen, latGen, Ideal.span_le]
  rintro _ ⟨u, hu, rfl⟩
  exact (ymon_sub_one_mem_latKer L' u).2 (h hu)

theorem latKer_injective {L L' : Submodule ℤ (Bases M →₀ ℤ)} (h : latKer M K L = latKer M K L') :
    L = L' := by
  ext u
  rw [← ymon_sub_one_mem_latKer (K := K), ← ymon_sub_one_mem_latKer (K := K), h]

/-- For `L = ⟨R⟩`: `(f_z : z ∈ R) 𝒴 = 𝔞_L`. -/
theorem map_span_binom (R : Set (Bases M →₀ ℤ)) :
    (Ideal.span (binom M K '' R)).map (iY M K).toRingHom = latKer M K (Submodule.span ℤ R) := by
  apply le_antisymm
  · rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, iY_binom]
    exact Ideal.mul_mem_left _ _
      ((ymon_sub_one_mem_latKer _ z).2 (Submodule.subset_span hz))
  · rw [latKer_eq_latGen, latGen, Ideal.span_le]
    rintro _ ⟨u, hu, rfl⟩
    set F := (Ideal.span (binom M K '' R)).map (iY M K).toRingHom
    have hR : ∀ z ∈ R, ymon M K z - 1 ∈ F := by
      intro z hz
      have h1 : iY M K (binom M K z) ∈ F :=
        Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨z, hz, rfl⟩)
      rw [iY_binom] at h1
      have := F.mul_mem_left (ymon M K (-castZ M (zneg M z))) h1
      rwa [← mul_assoc, ← ymon_add, neg_add_cancel, ymon_zero, one_mul] at this
    have hu' : u ∈ AddSubgroup.closure R := by
      rw [← Submodule.span_int_eq_addSubgroupClosure]; exact hu
    clear hu
    induction hu' using AddSubgroup.closure_induction with
    | mem z hz => exact hR z hz
    | zero => simp [ymon_zero]
    | add u v _ _ hu hv =>
      have : ymon M K (u + v) - 1 = ymon M K u * (ymon M K v - 1) + (ymon M K u - 1) := by
        rw [ymon_add]; ring
      rw [this]; exact F.add_mem (F.mul_mem_left _ hv) hu
    | neg u _ hu =>
      have : ymon M K (-u) - 1 = -(ymon M K (-u) * (ymon M K u - 1)) := by
        rw [mul_sub, mul_comm, ymon_mul_neg]; ring
      rw [this]; exact F.neg_mem (F.mul_mem_left _ hu)

/-! ### `I_M 𝒴` is the lattice ideal of `ker_ℤ A_M` -/

/-- `ℕ^α → ℤ^α`. -/
def castA (w : α →₀ ℕ) : α → ℤ := fun x => (w x : ℤ)

theorem castA_injective : Function.Injective (castA (α := α)) := by
  intro a b h
  ext x
  have := congrFun h x
  simp only [castA] at this
  exact_mod_cast this

theorem indN_apply (B : Bases M) (x : α) : (indN M B x : ℤ) = Set.indicator B.1 (fun _ => 1) x := by
  classical
  simp only [indN, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases hx : x ∈ B.1
  · simp [hx, B.2.subset_ground hx]
  · simp [hx]

theorem castA_Aexp (a : Bases M →₀ ℕ) : castA (Aexp M a) = incidence M (castZ M a) := by
  induction a using Finsupp.induction_linear with
  | zero => funext x; simp [castA]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ← ha, ← hb]; funext x; simp [castA]
  | single B m =>
    funext x
    simp only [castA, Aexp, Finsupp.liftAddHom_apply_single, multiplesHom_apply, castZ,
      Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single, incidence,
      Finsupp.linearCombination_single, Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul,
      Nat.cast_mul, indN_apply]
    simp

variable (M) in
/-- The induced map `ℤ^𝓑 / ker A_M → ℤ^α` (injective). -/
noncomputable def jA : ((Bases M →₀ ℤ) ⧸ LinearMap.ker (incidence M)) →ₗ[ℤ] (α → ℤ) :=
  (LinearMap.ker (incidence M)).liftQ (incidence M) le_rfl

variable (M) in
theorem jA_injective : Function.Injective (jA M) := by
  rw [← LinearMap.ker_eq_bot, jA]
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

theorem mapDomain_phi (g : MvPolynomial (Bases M) K) :
    AddMonoidAlgebra.mapDomain castA (phi M K g) =
      AddMonoidAlgebra.mapDomain (jA M) (chi M K (LinearMap.ker (incidence M)) (iY M K g)) := by
  have h1 : phi M K g = AddMonoidAlgebra.mapDomain (Aexp M) g := by
    simp [phi, AddMonoidAlgebra.mapDomainAlgHom_apply]
  have h2 : iY M K g = AddMonoidAlgebra.mapDomain (castZ M) g := by
    simp [iY, AddMonoidAlgebra.mapDomainAlgHom_apply]
  rw [chi_apply, h1, h2, ← mapDomain_comp', ← mapDomain_comp', ← mapDomain_comp']
  congr 1
  funext a
  simp [jA, castA_Aexp]

theorem iY_mem_latKer_iff (g : MvPolynomial (Bases M) K) :
    iY M K g ∈ latKer M K (LinearMap.ker (incidence M)) ↔ g ∈ toricIdeal M K := by
  rw [latKer, toricIdeal, RingHom.mem_ker, RingHom.mem_ker]
  constructor
  · intro h
    have := mapDomain_phi (K := K) g
    rw [h, AddMonoidAlgebra.mapDomain_zero] at this
    exact AddMonoidAlgebra.mapDomain_injective castA_injective
      (this.trans (AddMonoidAlgebra.mapDomain_zero _).symm)
  · intro h
    have := mapDomain_phi (K := K) g
    rw [h, AddMonoidAlgebra.mapDomain_zero] at this
    exact AddMonoidAlgebra.mapDomain_injective (jA_injective M)
      (this.symm.trans (AddMonoidAlgebra.mapDomain_zero _).symm)

/-- `I_M 𝒴 = 𝔞_{ker_ℤ A_M}`. -/
theorem map_toric : (toricIdeal M K).map (algebraMap _ (Laurent M K)) =
    latKer M K (LinearMap.ker (incidence M)) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    exact (iY_mem_latKer_iff g).2 hg
  · intro h hh
    obtain ⟨⟨g, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (pM M K)) h
    have hs : IsUnit (algebraMap _ (Laurent M K) (s : MvPolynomial (Bases M) K)) :=
      IsLocalization.map_units _ s
    have hspec := IsLocalization.mk'_spec (Laurent M K) g s
    have hg : algebraMap _ (Laurent M K) g ∈ latKer M K (LinearMap.ker (incidence M)) := by
      rw [← hspec]; exact Ideal.mul_mem_right _ _ hh
    have hg' : g ∈ toricIdeal M K := (iY_mem_latKer_iff g).1 hg
    rw [← Ideal.mul_unit_mem_iff_mem _ hs, hspec]
    exact Ideal.mem_map_of_mem _ hg'

/-! ### Saturation -/

theorem satP_eq_comap (J : Ideal (MvPolynomial (Bases M) K)) :
    satP M K J = (J.map (algebraMap _ (Laurent M K))).comap (algebraMap _ (Laurent M K)) := by
  ext f
  rw [Ideal.mem_comap, IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers (pM M K))]
  constructor
  · rintro ⟨m, hm⟩; exact ⟨_, ⟨m, rfl⟩, hm⟩
  · rintro ⟨_, ⟨m, rfl⟩, hm⟩; exact ⟨m, hm⟩

theorem toric_isPrime : (toricIdeal M K).IsPrime := RingHom.ker_isPrime _

theorem pM_not_mem : pM M K ∉ toricIdeal M K := by
  classical
  rw [toricIdeal, RingHom.mem_ker, pM, map_prod]
  rw [Finset.prod_eq_zero_iff]
  rintro ⟨B, -, hB⟩
  rw [MvPolynomial.X, phi, AddMonoidAlgebra.mapDomainAlgHom_apply] at hB
  have := congrArg (fun x : MvPolynomial α K => x.coeff (Aexp M (Finsupp.single B 1))) hB
  simp [MvPolynomial.monomial, AddMonoidAlgebra.mapDomain_single] at this

theorem satP_toric : satP M K (toricIdeal M K) = toricIdeal M K := by
  apply le_antisymm
  · rintro f ⟨m, hm⟩
    rcases (toric_isPrime (M := M) (K := K)).mem_or_mem hm with h | h
    · exact absurd ((toric_isPrime (M := M) (K := K)).mem_of_pow_mem m h) pM_not_mem
    · exact h
  · intro f hf; exact ⟨0, by simpa using hf⟩

/-! ### Corollary 7.1: the equivalences -/

/-- **Corollary 7.1**, (a) ⇔ (b) ⇔ (c). Here `R` is a set of `c` squares. -/
theorem cor71 (R : Finset (Bases M →₀ ℤ)) (hsq : ∀ z ∈ R, IsSquare M z)
    (hc : R.card = codim M) :
    ((LinearIndependent ℤ (fun z : R => (z : Bases M →₀ ℤ)) ∧
        Submodule.span ℤ (R : Set (Bases M →₀ ℤ)) = LinearMap.ker (incidence M)) ↔
      (toricIdeal M K).map (algebraMap _ (Laurent M K)) =
        (Ideal.span (binom M K '' R)).map (algebraMap _ (Laurent M K))) ∧
    ((toricIdeal M K).map (algebraMap _ (Laurent M K)) =
        (Ideal.span (binom M K '' R)).map (algebraMap _ (Laurent M K)) ↔
      toricIdeal M K = satP M K (Ideal.span (binom M K '' R))) := by
  have hb : (toricIdeal M K).map (algebraMap _ (Laurent M K)) =
        (Ideal.span (binom M K '' R)).map (algebraMap _ (Laurent M K)) ↔
      Submodule.span ℤ (R : Set (Bases M →₀ ℤ)) = LinearMap.ker (incidence M) := by
    rw [map_toric, algebraMap_eq, map_span_binom]
    exact ⟨fun h => (latKer_injective h).symm, fun h => by rw [h]⟩
  refine ⟨?_, ?_⟩
  · rw [hb]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    -- a spanning set of `c` vectors is a basis (Orzech property of `ℤ`)
    have hRk : ∀ z ∈ R, z ∈ LinearMap.ker (incidence M) := fun z hz => (hsq z hz).mem_ker
    let b : R → LinearMap.ker (incidence M) := fun z => ⟨z, hRk z z.2⟩
    have hspan : ⊤ ≤ Submodule.span ℤ (Set.range b) := by
      rw [top_le_iff]
      apply Submodule.map_injective_of_injective (Submodule.injective_subtype _)
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
      have hr : Set.range ((LinearMap.ker (incidence M)).subtype ∘ b) = (R : Set _) := by
        ext x; simp [b]
      rw [hr]; exact h
    have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan
      (by rw [Fintype.card_coe, hc]; rfl)
    exact hli.map' _ (Submodule.ker_subtype _)
  · constructor
    · intro h
      rw [satP_eq_comap, ← h, ← satP_eq_comap, satP_toric]
    · intro h
      rw [h, satP_eq_comap]
      exact (Ideal.gc_map_comap _).l_u_l_eq_l _

/-! ### Heights -/

instance : IsNoetherianRing (Laurent M K) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (pM M K)) _ inferInstance

theorem disjoint_powers_toric :
    Disjoint (Submonoid.powers (pM M K) : Set (MvPolynomial (Bases M) K))
      (toricIdeal M K : Set (MvPolynomial (Bases M) K)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨m, rfl⟩ h
  exact pM_not_mem ((toric_isPrime (M := M) (K := K)).mem_of_pow_mem m h)

instance latKer_ker_isPrime : (latKer M K (LinearMap.ker (incidence M))).IsPrime := by
  rw [← map_toric]
  exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (pM M K)) _ _
    toric_isPrime disjoint_powers_toric

/-- `ht I_M = ht (I_M 𝒴)`. -/
theorem height_toric : (toricIdeal M K).height =
    (latKer M K (LinearMap.ker (incidence M))).height := by
  have := toric_isPrime (M := M) (K := K)
  rw [← map_toric, IsLocalization.height_map_of_disjoint (Submonoid.powers (pM M K))
    _ disjoint_powers_toric]

/-- **Krull's height theorem**: `ht (I_M 𝒴) ≤ |s|` whenever `I_M 𝒴` is generated by `s`. -/
theorem height_le_card {s : Finset (Laurent M K)}
    (hs : Ideal.span (s : Set (Laurent M K)) = latKer M K (LinearMap.ker (incidence M))) :
    (latKer M K (LinearMap.ker (incidence M))).height ≤ s.card := by
  have hmin : latKer M K (LinearMap.ker (incidence M)) ∈
      (Ideal.span (s : Set (Laurent M K))).minimalPrimes := by
    rw [hs, Ideal.minimalPrimes_eq_subsingleton_self]; rfl
  refine (Ideal.height_le_encard_of_mem_minimalPrimes_span hmin).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard]

section Chain

variable (b : Basis (Fin (codim M)) ℤ (LinearMap.ker (incidence M)))

variable (M) in
/-- `L_j = {x ∈ ker_ℤ A_M : x_i = 0 for i ≥ j}` in the coordinates of a basis `b`. -/
def Lsub (j : ℕ) : Submodule ℤ (Bases M →₀ ℤ) where
  carrier := {x | ∃ h : x ∈ LinearMap.ker (incidence M),
    ∀ i : Fin (codim M), j ≤ i.val → b.repr ⟨x, h⟩ i = 0}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨add_mem hx hy, fun i hi => ?_⟩
    have : (⟨x + y, add_mem hx hy⟩ : LinearMap.ker (incidence M)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, Finsupp.add_apply, hx' i hi, hy' i hi, add_zero]
  zero_mem' := ⟨zero_mem _, fun i _ => by
    have : (⟨0, zero_mem _⟩ : LinearMap.ker (incidence M)) = 0 := rfl
    rw [this, map_zero, Finsupp.zero_apply]⟩
  smul_mem' := by
    rintro a x ⟨hx, hx'⟩
    refine ⟨Submodule.smul_mem _ a hx, fun i hi => ?_⟩
    have : (⟨a • x, Submodule.smul_mem _ a hx⟩ : LinearMap.ker (incidence M)) = a • ⟨x, hx⟩ :=
      rfl
    rw [this, map_smul, Finsupp.smul_apply, hx' i hi, smul_zero]

theorem Lsub_top : Lsub M b (codim M) = LinearMap.ker (incidence M) := by
  ext x
  refine ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, fun i hi => absurd i.2 (not_lt.2 hi)⟩⟩

theorem Lsub_saturated (j : ℕ) {n : ℕ} (hn : n ≠ 0) {x : Bases M →₀ ℤ}
    (hx : n • x ∈ Lsub M b j) : x ∈ Lsub M b j := by
  obtain ⟨h, h'⟩ := hx
  have hxk : x ∈ LinearMap.ker (incidence M) := by
    rw [LinearMap.mem_ker] at h ⊢
    rw [map_nsmul] at h
    funext a
    have := congrFun h a
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero] at this
    exact this.resolve_left hn
  refine ⟨hxk, fun i hi => ?_⟩
  have := h' i hi
  have e : (⟨n • x, h⟩ : LinearMap.ker (incidence M)) = n • ⟨x, hxk⟩ := rfl
  rw [e, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero] at this
  exact this.resolve_left hn

theorem Lsub_lt (j : Fin (codim M)) : Lsub M b j.val < Lsub M b (j.val + 1) := by
  refine lt_of_le_of_ne (fun x ⟨h, h'⟩ => ⟨h, fun i hi => h' i (by omega)⟩) (fun he => ?_)
  have hmem : ((b j : LinearMap.ker (incidence M)) : Bases M →₀ ℤ) ∈ Lsub M b (j.val + 1) := by
    refine ⟨(b j).2, fun i hi => ?_⟩
    rw [Subtype.coe_eta, Basis.repr_self, Finsupp.single_apply, ite_eq_right_iff.2 (fun h => ?_)]
    rw [h] at hi; omega
  rw [← he] at hmem
  obtain ⟨_, h'⟩ := hmem
  have := h' j le_rfl
  rw [Subtype.coe_eta, Basis.repr_self, Finsupp.single_eq_same] at this
  exact one_ne_zero this

instance (j : ℕ) : HasUniqueDiv ((Bases M →₀ ℤ) ⧸ Lsub M b j) where
  nsmul_right_injective n hn := by
    intro q₁ q₂ h
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q₁
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q₂
    simp only [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h ⊢
    rw [← smul_sub] at h
    exact Lsub_saturated b j hn h

instance (j : ℕ) : AddMonoid.FG ((Bases M →₀ ℤ) ⧸ Lsub M b j) := by
  rw [← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]; infer_instance

instance (j : ℕ) : (latKer M K (Lsub M b j)).IsPrime := by
  have : TwoUniqueSums ((Bases M →₀ ℤ) ⧸ Lsub M b j) := AffineAddMonoid.to_twoUniqueSums
  exact RingHom.ker_isPrime _

theorem le_height_Lsub (j : ℕ) (hj : j ≤ codim M) :
    (j : ℕ∞) ≤ (latKer M K (Lsub M b j)).height := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hlt : latKer M K (Lsub M b j) < latKer M K (Lsub M b (j + 1)) := by
      refine lt_of_le_of_ne (latKer_mono (Lsub_lt b ⟨j, by omega⟩).le) (fun he => ?_)
      exact (Lsub_lt b ⟨j, by omega⟩).ne (latKer_injective he)
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    push_cast
    calc (j : ℕ∞) + 1 ≤ (latKer M K (Lsub M b j)).height + 1 := by
          gcongr; exact ih (by omega)
      _ ≤ _ := this

end Chain

/-- `c ≤ ht (I_M 𝒴)`, via the chain of prime lattice ideals `𝔞_{L_0} ⊊ ⋯ ⊊ 𝔞_{L_c}`. -/
theorem codim_le_height :
    (codim M : ℕ∞) ≤ (latKer M K (LinearMap.ker (incidence M))).height := by
  let b := Module.finBasisOfFinrankEq ℤ (LinearMap.ker (incidence M)) (rfl : _ = codim M)
  have := le_height_Lsub (K := K) b (codim M) le_rfl
  rwa [Lsub_top] at this

/-! ### Corollary 7.1: existence, height and minimality -/

/-- A square basis consists of exactly `c` squares. -/
theorem exists_square_finset [M.RankPos] :
    ∃ R : Finset (Bases M →₀ ℤ), (∀ z ∈ R, IsSquare M z) ∧ R.card = codim M ∧
      LinearIndependent ℤ (fun z : R => (z : Bases M →₀ ℤ)) ∧
      Submodule.span ℤ (R : Set (Bases M →₀ ℤ)) = LinearMap.ker (incidence M) := by
  obtain ⟨S, hsq, hli, hspan⟩ := square_basis_theorem_paper M
  have hfin : S.Finite := hli.set_finite_of_isNoetherian
  refine ⟨hfin.toFinset, by simpa using hsq, ?_, ?_, by simpa using hspan⟩
  · have := hfin.fintype
    have hr : Set.range (fun z : S => (z : Bases M →₀ ℤ)) = S := Subtype.range_coe
    let bb : Basis S ℤ (LinearMap.ker (incidence M)) :=
      (Basis.span hli).map (LinearEquiv.ofEq _ _ (by rw [hr, hspan]))
    rw [codim, Module.finrank_eq_card_basis bb, Set.Finite.card_toFinset]
  · have := hli.comp (fun z : hfin.toFinset => (⟨z.1, (Set.Finite.mem_toFinset hfin).1 z.2⟩ : S))
      (fun a b h => Subtype.ext (Subtype.mk.inj h))
    exact this

/-- `c = N - rank A_M`. -/
theorem codim_eq : codim M = Nat.card (Bases M) - finrank ℤ (LinearMap.range (incidence M)) := by
  have := rank_nullity M
  rw [codim]; omega

open scoped Classical in
theorem map_span_finset (s : Finset (MvPolynomial (Bases M) K)) :
    (Ideal.span (s : Set (MvPolynomial (Bases M) K))).map (algebraMap _ (Laurent M K)) =
      Ideal.span ((s.image (algebraMap _ (Laurent M K)) : Finset _) : Set (Laurent M K)) := by
  rw [Ideal.map_span, Finset.coe_image]

/-- **Corollary 7.1**: `ht I_M = c`. -/
theorem cor71_height [M.RankPos] : (toricIdeal M K).height = codim M := by
  classical
  rw [height_toric]
  apply le_antisymm
  · obtain ⟨R, hsq, hc, hli, hspan⟩ := exists_square_finset (M := M)
    have hb := ((cor71 (K := K) R hsq hc).1).1 ⟨hli, hspan⟩
    have hs := map_span_finset (M := M) (K := K) (R.image (binom M K))
    rw [Finset.coe_image, ← hb, map_toric] at hs
    refine (height_le_card hs.symm).trans ?_
    exact_mod_cast (Finset.card_image_le.trans Finset.card_image_le).trans hc.le
  · exact codim_le_height

/-- **Corollary 7.1**: `I_M` is the `p`-saturation of an ideal generated by `c` symmetric exchange
binomials `f_z` (`z` running over a square basis). -/
theorem cor71_exists [M.RankPos] :
    ∃ R : Finset (Bases M →₀ ℤ), (∀ z ∈ R, IsSquare M z) ∧ R.card = codim M ∧
      toricIdeal M K = satP M K (Ideal.span (binom M K '' R)) := by
  obtain ⟨R, hsq, hc, hli, hspan⟩ := exists_square_finset (M := M)
  have h := cor71 (K := K) R hsq hc
  exact ⟨R, hsq, hc, h.2.1 (h.1.1 ⟨hli, hspan⟩)⟩

/-- **Corollary 7.1**: no ideal with fewer than `c` generators has `p`-saturation `I_M`. -/
theorem cor71_minimal (J : Ideal (MvPolynomial (Bases M) K)) (hJ : satP M K J = toricIdeal M K)
    (s : Finset (MvPolynomial (Bases M) K)) (hs : Ideal.span (s : Set _) = J) :
    codim M ≤ s.card := by
  classical
  have hmap : J.map (algebraMap _ (Laurent M K)) =
      (toricIdeal M K).map (algebraMap _ (Laurent M K)) := by
    rw [← hJ, satP_eq_comap]
    exact ((Ideal.gc_map_comap _).l_u_l_eq_l _).symm
  have h := map_span_finset (M := M) (K := K) s
  rw [hs, hmap, map_toric] at h
  have h1 := (codim_le_height (M := M) (K := K)).trans (height_le_card h.symm)
  have h2 : ((s.image (algebraMap _ (Laurent M K))).card : ℕ∞) ≤ s.card := by
    exact_mod_cast Finset.card_image_le
  have h3 : (codim M : ℕ∞) ≤ s.card := h1.trans h2
  exact_mod_cast h3

/-! ### The binomial of a square (Lemma 2.2, binomial form) -/

/-- For a square `z = z_{i,j;B,B'}`, `f_z = y_{B+i} y_{B'+j} - y_{B+j} y_{B'+i}`, the symmetric
exchange binomial of `B₁ = B + i`, `B₂ = B' + j`, `a = i`, `b = j`. -/
theorem binom_square {i j : α} {B B' : Set α} (h₁ : M.IsBase (insert i B))
    (h₂ : M.IsBase (insert j B)) (h₃ : M.IsBase (insert i B')) (h₄ : M.IsBase (insert j B'))
    (hij : i ≠ j) (hBB' : B ≠ B') (hiB : i ∉ B) (hjB : j ∉ B) (hiB' : i ∉ B') (hjB' : j ∉ B') :
    binom M K (Finsupp.single ⟨_, h₁⟩ 1 - Finsupp.single ⟨_, h₂⟩ 1
        - Finsupp.single ⟨_, h₃⟩ 1 + Finsupp.single ⟨_, h₄⟩ 1) =
      MvPolynomial.X ⟨_, h₁⟩ * MvPolynomial.X ⟨_, h₄⟩ -
        MvPolynomial.X ⟨_, h₂⟩ * MvPolynomial.X ⟨_, h₃⟩ := by
  classical
  set b₁ : Bases M := ⟨_, h₁⟩
  set b₂ : Bases M := ⟨_, h₂⟩
  set b₃ : Bases M := ⟨_, h₃⟩
  set b₄ : Bases M := ⟨_, h₄⟩
  have hdel : ∀ {a : α} {C C' : Set α}, a ∉ C → a ∉ C' → insert a C = insert a C' → C = C' := by
    intro a C C' hC hC' h
    have := congrArg (· \ {a}) h
    simpa [Set.insert_sdiff_self_of_notMem hC, Set.insert_sdiff_self_of_notMem hC'] using this
  have d12 : b₁ ≠ b₂ := fun h => by
    have hv : insert i B = insert j B := congrArg Subtype.val h
    have : i ∈ insert j B := by rw [← hv]; exact Set.mem_insert _ _
    rcases this with h' | h'
    · exact hij h'
    · exact hiB h'
  have d13 : b₁ ≠ b₃ := fun h => hBB' (hdel hiB hiB' (congrArg Subtype.val h))
  have d14 : b₁ ≠ b₄ := fun h => by
    have hv : insert i B = insert j B' := congrArg Subtype.val h
    have : i ∈ insert j B' := by rw [← hv]; exact Set.mem_insert _ _
    rcases this with h' | h'
    · exact hij h'
    · exact hiB' h'
  have d23 : b₂ ≠ b₃ := fun h => by
    have hv : insert j B = insert i B' := congrArg Subtype.val h
    have : j ∈ insert i B' := by rw [← hv]; exact Set.mem_insert _ _
    rcases this with h' | h'
    · exact hij h'.symm
    · exact hjB' h'
  have d24 : b₂ ≠ b₄ := fun h => hBB' (hdel hjB hjB' (congrArg Subtype.val h))
  have d34 : b₃ ≠ b₄ := fun h => by
    have hv : insert i B' = insert j B' := congrArg Subtype.val h
    have : i ∈ insert j B' := by rw [← hv]; exact Set.mem_insert _ _
    rcases this with h' | h'
    · exact hij h'
    · exact hiB' h'
  have hp : zpos M (Finsupp.single b₁ 1 - Finsupp.single b₂ 1 - Finsupp.single b₃ 1 +
      Finsupp.single b₄ 1) = Finsupp.single b₁ 1 + Finsupp.single b₄ 1 := by
    ext C
    simp only [zpos, Finsupp.mapRange_apply, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply]
    split_ifs <;> simp_all
  have hn : zneg M (Finsupp.single b₁ 1 - Finsupp.single b₂ 1 - Finsupp.single b₃ 1 +
      Finsupp.single b₄ 1) = Finsupp.single b₂ 1 + Finsupp.single b₃ 1 := by
    ext C
    simp only [zneg, Finsupp.mapRange_apply, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply]
    split_ifs <;> simp_all
  rw [binom, hp, hn, MvPolynomial.X, MvPolynomial.X, MvPolynomial.X, MvPolynomial.X,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial, one_mul]

end SquareBasis
