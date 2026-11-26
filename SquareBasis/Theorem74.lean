module

public import SquareBasis.Plucker

/-!
# Theorem 7.4 of the paper

Let `Q, Q'` be real `k × n` matrices with `𝓑(Q) = 𝓑(Q') = 𝓑`, let `M` be the matroid with set
of bases `𝓑` (hypothesis `hM`), and let `R` be a square basis of `M`. With
`ε_I = sgn (p_I(Q') / p_I(Q))` and `η_I = log |p_I(Q') / p_I(Q)|`:

* `thm74a` — **Theorem 7.4(a)**: `Q' = GQD` with `G ∈ GL(k, ℝ)` and `D` invertible diagonal iff
  `∏_I ε_I^{z_I} = 1` and `zᵀη = 0` for every `z ∈ R`;
* `thm74b` — **Theorem 7.4(b)**: `Q' = GQD` with `D` positive diagonal iff `ε` is constant on
  `𝓑` and `zᵀη = 0` for every `z ∈ R`;
* `thm74_unique` — if `M` is connected, `D` is unique up to a nonzero scalar factor.

The proof follows the paper. The step "`zᵀη = 0` for `z ∈ R` gives `η = A_Mᵀ x`" is obtained
from `orth_ker` (the forest argument that the paper uses for the signs), applied to `η`.
-/

@[expose] public section

namespace SquareBasis

open Matrix Matroid

variable {k n : ℕ}

/-! ### The sign function -/

/-- `sgn x ∈ {1, -1, 0}`. -/
noncomputable def sgn (x : ℝ) : ℝ := if 0 < x then 1 else if x < 0 then -1 else 0

theorem sgn_mul_abs (x : ℝ) : sgn x * |x| = x := by
  unfold sgn
  split_ifs with h1 h2
  · rw [abs_of_pos h1, one_mul]
  · rw [abs_of_neg h2]; ring
  · have : x = 0 := by linarith [not_lt.1 h1, not_lt.1 h2]
    simp [this]

theorem sgn_of_pos {x : ℝ} (hx : 0 < x) : sgn x = 1 := by simp [sgn, hx]

theorem sgn_of_neg {x : ℝ} (hx : x < 0) : sgn x = -1 := by
  simp [sgn, hx, not_lt.2 hx.le]

theorem sgn_zero : sgn 0 = 0 := by simp [sgn]

theorem sgn_mul (x y : ℝ) : sgn (x * y) = sgn x * sgn y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> rcases lt_trichotomy y 0 with hy | rfl | hy
  · rw [sgn_of_neg hx, sgn_of_neg hy, sgn_of_pos (mul_pos_of_neg_of_neg hx hy)]; norm_num
  · simp [sgn_zero]
  · rw [sgn_of_neg hx, sgn_of_pos hy, sgn_of_neg (mul_neg_of_neg_of_pos hx hy)]; norm_num
  · simp [sgn_zero]
  · simp [sgn_zero]
  · simp [sgn_zero]
  · rw [sgn_of_pos hx, sgn_of_neg hy, sgn_of_neg (mul_neg_of_pos_of_neg hx hy)]; norm_num
  · simp [sgn_zero]
  · rw [sgn_of_pos hx, sgn_of_pos hy, sgn_of_pos (mul_pos hx hy)]; norm_num

theorem sgn_pos {x : ℝ} (hx : 0 < x) : sgn x = 1 := by simp [sgn, hx]

theorem sgn_eq_or {x : ℝ} (hx : x ≠ 0) : sgn x = 1 ∨ sgn x = -1 := by
  unfold sgn
  rcases lt_or_gt_of_ne hx with h | h
  · right; simp [h, not_lt.2 h.le]
  · left; simp [h]

theorem sgn_ne_zero {x : ℝ} (hx : x ≠ 0) : sgn x ≠ 0 := by
  rcases sgn_eq_or hx with h | h <;> rw [h] <;> norm_num

theorem sgn_sgn {x : ℝ} (hx : x ≠ 0) : sgn (sgn x) = sgn x := by
  rcases sgn_eq_or hx with h | h <;> rw [h] <;> simp [sgn]

theorem sgn_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    sgn (∏ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, sgn_mul, ih]

/-! ### The setting -/

open scoped Classical in
/-- The finset of a basis. -/
noncomputable def bset {M : Matroid (Fin n)} (B : Bases M) : Finset (Fin n) :=
  Finset.univ.filter (· ∈ B.1)

theorem coe_bset {M : Matroid (Fin n)} (B : Bases M) : (bset B : Set (Fin n)) = B.1 := by
  ext x; simp [bset]

open scoped Classical in
theorem filter_ground_eq_bset {M : Matroid (Fin n)} (B : Bases M) :
    M.ground_finite.toFinset.filter (· ∈ B.1) = bset B := by
  ext x
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, bset, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨B.2.subset_ground h, h⟩⟩

/-- The hypotheses of Theorem 7.4: `M` is the matroid whose bases are the `k`-sets `I` with
`p_I(Q) ≠ 0`, and `𝓑(Q) = 𝓑(Q')`. -/
structure Setup (Q Q' : Matrix (Fin k) (Fin n) ℝ) (M : Matroid (Fin n)) : Prop where
  bases : ∀ I : Finset (Fin n), M.IsBase (I : Set (Fin n)) ↔ I.card = k ∧ pl Q I ≠ 0
  same : ∀ I : Finset (Fin n), pl Q I ≠ 0 ↔ pl Q' I ≠ 0

/-- `p_I(Q') / p_I(Q)`. -/
noncomputable def ratio (Q Q' : Matrix (Fin k) (Fin n) ℝ) {M : Matroid (Fin n)} (B : Bases M) :
    ℝ := pl Q' (bset B) / pl Q (bset B)

/-- `ε_I = sgn (p_I(Q') / p_I(Q))`. -/
noncomputable def eps (Q Q' : Matrix (Fin k) (Fin n) ℝ) {M : Matroid (Fin n)} (B : Bases M) :
    ℝ := sgn (ratio Q Q' B)

/-- `η_I = log |p_I(Q') / p_I(Q)|`. -/
noncomputable def eta (Q Q' : Matrix (Fin k) (Fin n) ℝ) {M : Matroid (Fin n)} (B : Bases M) :
    ℝ := Real.log |ratio Q Q' B|

variable {Q Q' : Matrix (Fin k) (Fin n) ℝ} {M : Matroid (Fin n)}

theorem Setup.base_facts (hS : Setup Q Q' M) (B : Bases M) :
    (bset B).card = k ∧ pl Q (bset B) ≠ 0 ∧ pl Q' (bset B) ≠ 0 ∧ ratio Q Q' B ≠ 0 := by
  have h := (hS.bases (bset B)).1 (by rw [coe_bset]; exact B.2)
  have h' := (hS.same _).1 h.2
  exact ⟨h.1, h.2, h', div_ne_zero h' h.2⟩

theorem Setup.isBase_of_pl (hS : Setup Q Q' M) {I : Finset (Fin n)} (hI : I.card = k)
    (h : pl Q I ≠ 0) : ∃ B : Bases M, bset B = I := by
  refine ⟨⟨I, (hS.bases I).2 ⟨hI, h⟩⟩, ?_⟩
  ext x; simp [bset]

/-- If `M` has a square basis, then `rank M ≥ 1` (Proposition 2.3(a)). -/
theorem rankPos_of_hasSquareBasis (h : HasSquareBasis M) : M.RankPos := by
  by_contra hne
  have h0 : M.IsBase ∅ := by
    by_contra h'; exact hne ⟨h'⟩
  exact (prop23a M h0).2.2 h

/-! ### Multiplicative bookkeeping -/

/-- In `Additive ℝˣ`, a linear combination is a product of powers. -/
theorem lc_units {M : Matroid (Fin n)} (u : Bases M → ℝˣ) (z : Bases M →₀ ℤ) :
    ((Additive.toMul (Finsupp.linearCombination ℤ (fun B => Additive.ofMul (u B)) z) : ℝˣ) : ℝ) =
      z.prod (fun B c => (u B : ℝ) ^ c) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, toMul_add, Units.val_mul, hf, hg,
      Finsupp.prod_add_index' (fun _ => by simp) (fun B a b => zpow_add₀ (u B).ne_zero a b)]
  | single B c =>
    rw [Finsupp.linearCombination_single, Finsupp.prod_single_index (by simp), toMul_zsmul,
      toMul_ofMul, Units.val_zpow_eq_zpow_val]

/-- The ratio under `Q' = GQD`. -/
theorem ratio_of_eq (hS : Setup Q Q' M) {G : Matrix (Fin k) (Fin k) ℝ} {μ : Fin n → ℝ}
    (hQ : Q' = G * Q * diagonal μ) (B : Bases M) :
    ratio Q Q' B = G.det * ∏ i ∈ bset B, μ i := by
  obtain ⟨-, h1, -, -⟩ := hS.base_facts B
  rw [ratio, hQ, pl_scale]
  field_simp

/-! ### Theorem 7.4 -/

/-- The absolute-value condition holds for all of `ker_ℤ A_M` when it holds on a spanning set. -/
theorem forall_ker_of_span {G : Type} [AddCommGroup G] {R : Set (Bases M →₀ ℤ)}
    (hR : Submodule.span ℤ R = LinearMap.ker (incidence M)) (ψ : Bases M → G)
    (h : ∀ z ∈ R, Finsupp.linearCombination ℤ ψ z = 0) :
    ∀ u ∈ LinearMap.ker (incidence M), Finsupp.linearCombination ℤ ψ u = 0 := by
  intro u hu
  rw [← hR] at hu
  have : R ⊆ LinearMap.ker (Finsupp.linearCombination ℤ ψ) := fun z hz => h z hz
  exact (Submodule.span_le.2 this) hu

/-- From the conditions on `R`, the Plücker ratios factor as `c ∏_{i ∈ I} μ_i`, and then
`Q' = GQD` (sufficiency in Theorem 7.4). -/
theorem eq_of_ratio_factor (hS : Setup Q Q' M) {c : ℝ} (hc : c ≠ 0) {μ : Fin n → ℝ}
    (hμ : ∀ B : Bases M, ratio Q Q' B = c * ∏ i ∈ bset B, μ i) :
    ∃ G : Matrix (Fin k) (Fin k) ℝ, G.det ≠ 0 ∧ Q' = G * Q * diagonal μ := by
  have hpl : ∀ I : Finset (Fin n), I.card = k → pl Q' I = c * pl (Q * diagonal μ) I := by
    intro I hI
    have hD : pl (Q * diagonal μ) I = (∏ i ∈ I, μ i) * pl Q I := by
      have := pl_scale 1 Q μ I
      rwa [Matrix.one_mul, det_one, one_mul] at this
    rw [hD]
    by_cases h : pl Q I = 0
    · have : pl Q' I = 0 := by
        by_contra h'; exact (hS.same I).2 h' h
      rw [this, h]; ring
    · obtain ⟨B, rfl⟩ := hS.isBase_of_pl hI h
      have := hμ B
      rw [ratio, div_eq_iff h] at this
      rw [this]; ring
  obtain ⟨B₀, hB₀⟩ := M.exists_isBase
  set I₀ := bset (⟨B₀, hB₀⟩ : Bases M)
  obtain ⟨hI₀, hQI₀, -, hr⟩ := hS.base_facts ⟨B₀, hB₀⟩
  have hμ0 : ∏ i ∈ I₀, μ i ≠ 0 := by
    intro h0; apply hr; rw [hμ, h0, mul_zero]
  have h₀ : pl (Q * diagonal μ) I₀ ≠ 0 := by
    have := pl_scale 1 Q μ I₀
    rw [Matrix.one_mul, det_one, one_mul] at this
    rw [this]; exact mul_ne_zero hμ0 hQI₀
  obtain ⟨G, hG, hQ'⟩ := plucker_inj hc hpl hI₀ h₀
  exact ⟨G, hG ▸ hc, by rw [hQ', Matrix.mul_assoc]⟩

/-- The `η`-part of Theorem 7.4: `zᵀη = 0` for `z ∈ R` gives `η_I = τ + ∑_{i ∈ I} x_i`. -/
theorem eta_factor {R : Set (Bases M →₀ ℤ)}
    (hR : Submodule.span ℤ R = LinearMap.ker (incidence M))
    (h : ∀ z ∈ R, z.sum (fun B c => (c : ℝ) * eta Q Q' B) = 0) :
    ∃ (x : Fin n → ℝ) (τ : ℝ), ∀ B : Bases M, eta Q Q' B = τ + ∑ i ∈ bset B, x i := by
  have hker := forall_ker_of_span hR (eta Q Q') (fun z hz => by
    rw [Finsupp.linearCombination_apply]
    simpa [zsmul_eq_mul] using h z hz)
  obtain ⟨x, τ, hx⟩ := orth_ker M (eta Q Q') hker
  exact ⟨x, τ, fun B => by rw [hx B, filter_ground_eq_bset]⟩

/-- `ρ_I = ε_I exp(η_I)`. -/
theorem ratio_eq_eps_exp (hS : Setup Q Q' M) (B : Bases M) :
    ratio Q Q' B = eps Q Q' B * Real.exp (eta Q Q' B) := by
  obtain ⟨-, -, -, hr⟩ := hS.base_facts B
  rw [eps, eta, Real.exp_log (abs_pos.2 hr), sgn_mul_abs]

/-- **Theorem 7.4(a).** -/
theorem thm74a (hS : Setup Q Q' M) {R : Set (Bases M →₀ ℤ)} (hRsq : ∀ z ∈ R, IsSquare M z)
    (hRli : LinearIndependent ℤ (fun z : R => (z : Bases M →₀ ℤ)))
    (hR : Submodule.span ℤ R = LinearMap.ker (incidence M)) :
    (∃ (G : Matrix (Fin k) (Fin k) ℝ) (μ : Fin n → ℝ), G.det ≠ 0 ∧ (∀ i, μ i ≠ 0) ∧
        Q' = G * Q * diagonal μ) ↔
      ∀ z ∈ R, z.prod (fun B c => eps Q Q' B ^ c) = 1 ∧
        z.sum (fun B c => (c : ℝ) * eta Q Q' B) = 0 := by
  classical
  have := rankPos_of_hasSquareBasis ⟨R, hRsq, hRli, hR⟩
  have heps0 : ∀ B : Bases M, eps Q Q' B ≠ 0 := fun B => sgn_ne_zero (hS.base_facts B).2.2.2
  let u : Bases M → ℝˣ := fun B => Units.mk0 (eps Q Q' B) (heps0 B)
  constructor
  · -- necessity
    rintro ⟨G, μ, hG, hμ, hQ⟩
    intro z hz
    have hzker : z ∈ LinearMap.ker (incidence M) := (hRsq z hz).mem_ker
    have hr := ratio_of_eq hS hQ
    constructor
    · -- the signs: `ε_I = sgn(det G) ∏_{i ∈ I} sgn μ_i`
      have hpot : ∀ B : Bases M, Additive.ofMul (u B) =
          Additive.ofMul (Units.mk0 (sgn G.det) (sgn_ne_zero hG)) +
            ∑ x ∈ M.ground_finite.toFinset.filter (· ∈ B.1),
              Additive.ofMul (Units.mk0 (sgn (μ x)) (sgn_ne_zero (hμ x))) := by
        intro B
        apply Additive.toMul.injective
        apply Units.ext
        rw [toMul_add, toMul_sum, filter_ground_eq_bset]
        simp only [toMul_ofMul, Units.val_mul, Units.val_mk0, Units.coe_prod, u, eps, hr B,
          sgn_mul, sgn_prod]
      have h0 := lc_eq_zero_of_potential M _ _ _ hpot hzker
      have := lc_units u z
      rw [h0, toMul_zero, Units.val_one] at this
      simpa [u] using this.symm
    · -- the absolute values: `η_I = log |det G| + ∑_{i ∈ I} log |μ_i|`
      have hpot : ∀ B : Bases M, eta Q Q' B = Real.log |G.det| +
          ∑ x ∈ M.ground_finite.toFinset.filter (· ∈ B.1), Real.log |μ x| := by
        intro B
        rw [eta, hr B, filter_ground_eq_bset, abs_mul, Finset.abs_prod,
          Real.log_mul (abs_ne_zero.2 hG) (Finset.prod_ne_zero_iff.2 fun i _ => abs_ne_zero.2 (hμ i)),
          Real.log_prod (fun i _ => abs_ne_zero.2 (hμ i))]
      have h0 := lc_eq_zero_of_potential M _ _ _ hpot hzker
      rw [Finsupp.linearCombination_apply] at h0
      simpa [zsmul_eq_mul] using h0
  · -- sufficiency
    intro h
    -- the signs: `ε_I = sgn(t) ∏_{i ∈ I} sgn(s_i)`
    have hker := forall_ker_of_span hR (fun B => Additive.ofMul (u B)) (fun z hz => by
      apply Additive.toMul.injective
      apply Units.ext
      rw [lc_units, toMul_zero, Units.val_one]
      simpa [u] using (h z hz).1)
    obtain ⟨σs, τs, hs⟩ := orth_ker M _ hker
    obtain ⟨x, τ, hx⟩ := eta_factor hR (fun z hz => (h z hz).2)
    set t : ℝ := ((Additive.toMul τs : ℝˣ) : ℝ)
    set s : Fin n → ℝ := fun i => ((Additive.toMul (σs i) : ℝˣ) : ℝ)
    have ht : t ≠ 0 := Units.ne_zero _
    have hs0 : ∀ i, s i ≠ 0 := fun i => Units.ne_zero _
    have heps : ∀ B : Bases M, eps Q Q' B = sgn t * ∏ i ∈ bset B, sgn (s i) := by
      intro B
      have := congrArg (fun a => ((Additive.toMul a : ℝˣ) : ℝ)) (hs B)
      simp only [toMul_ofMul, Units.val_mk0, u, toMul_add, toMul_sum, Units.val_mul,
        Units.coe_prod, filter_ground_eq_bset] at this
      have h1 : eps Q Q' B = sgn (eps Q Q' B) := (sgn_sgn (hS.base_facts B).2.2.2).symm
      rw [h1, show eps Q Q' B = t * ∏ i ∈ bset B, s i from this, sgn_mul, sgn_prod]
    obtain ⟨G, hG, hQ⟩ := eq_of_ratio_factor (c := sgn t * Real.exp τ)
      (μ := fun i => sgn (s i) * Real.exp (x i)) hS
      (mul_ne_zero (sgn_ne_zero ht) (Real.exp_pos _).ne') (fun B => by
        rw [ratio_eq_eps_exp hS, heps, hx, Real.exp_add, Real.exp_sum, Finset.prod_mul_distrib]
        ring)
    exact ⟨G, _, hG, fun i => mul_ne_zero (sgn_ne_zero (hs0 i)) (Real.exp_pos _).ne', hQ⟩

/-! ### Theorem 7.4(b) -/

/-- If `R ⊆ ker_ℤ A_M` spans `ker_ℝ A_M` (some nonzero multiple of every `u ∈ ker_ℤ A_M` lies in
the span of `R`), then `zᵀη = 0` for `z ∈ R` gives `uᵀη = 0` for all `u ∈ ker_ℤ A_M`. -/
theorem eta_ker_of_rat_span {R : Set (Bases M →₀ ℤ)}
    (hR : ∀ u ∈ LinearMap.ker (incidence M), ∃ m : ℤ, m ≠ 0 ∧ m • u ∈ Submodule.span ℤ R)
    (h : ∀ z ∈ R, z.sum (fun B c => (c : ℝ) * eta Q Q' B) = 0) :
    ∀ u ∈ LinearMap.ker (incidence M), Finsupp.linearCombination ℤ (eta Q Q') u = 0 := by
  intro u hu
  obtain ⟨m, hm, hmu⟩ := hR u hu
  have hsub : R ⊆ (LinearMap.ker (Finsupp.linearCombination ℤ (eta (M := M) Q Q')) :
      Set (Bases M →₀ ℤ)) := fun z hz => by
    rw [SetLike.mem_coe, LinearMap.mem_ker, Finsupp.linearCombination_apply]
    simpa [zsmul_eq_mul] using h z hz
  have h0 : Finsupp.linearCombination ℤ (eta Q Q') (m • u) = 0 := (Submodule.span_le.2 hsub) hmu
  rw [map_zsmul, zsmul_eq_mul, mul_eq_zero] at h0
  exact h0.resolve_left (Int.cast_ne_zero.2 hm)

/-- **Theorem 7.4(b)**, under the weaker hypothesis of Remark 7.5: `R ⊆ ker_ℤ A_M` spans
`ker_ℝ A_M`. -/
theorem thm74b_of_span [M.RankPos] (hS : Setup Q Q' M) {R : Set (Bases M →₀ ℤ)}
    (hRk : R ⊆ LinearMap.ker (incidence M))
    (hR : ∀ u ∈ LinearMap.ker (incidence M), ∃ m : ℤ, m ≠ 0 ∧ m • u ∈ Submodule.span ℤ R) :
    (∃ (G : Matrix (Fin k) (Fin k) ℝ) (μ : Fin n → ℝ), G.det ≠ 0 ∧ (∀ i, 0 < μ i) ∧
        Q' = G * Q * diagonal μ) ↔
      (∃ e : ℝ, ∀ B : Bases M, eps Q Q' B = e) ∧
        ∀ z ∈ R, z.sum (fun B c => (c : ℝ) * eta Q Q' B) = 0 := by
  classical
  constructor
  · -- necessity
    rintro ⟨G, μ, hG, hμ, hQ⟩
    have hr := ratio_of_eq hS hQ
    refine ⟨⟨sgn G.det, fun B => ?_⟩, fun z hz => ?_⟩
    · rw [eps, hr B, sgn_mul, sgn_prod]
      simp [sgn_pos (hμ _)]
    · have hpot : ∀ B : Bases M, eta Q Q' B = Real.log |G.det| +
          ∑ x ∈ M.ground_finite.toFinset.filter (· ∈ B.1), Real.log |μ x| := by
        intro B
        rw [eta, hr B, filter_ground_eq_bset, abs_mul, Finset.abs_prod,
          Real.log_mul (abs_ne_zero.2 hG)
            (Finset.prod_ne_zero_iff.2 fun i _ => abs_ne_zero.2 (hμ i).ne'),
          Real.log_prod (fun i _ => abs_ne_zero.2 (hμ i).ne')]
      have h0 := lc_eq_zero_of_potential M _ _ _ hpot (hRk hz)
      rw [Finsupp.linearCombination_apply] at h0
      simpa [zsmul_eq_mul] using h0
  · -- sufficiency
    rintro ⟨⟨e, he⟩, h⟩
    obtain ⟨x, τ, hx⟩ := orth_ker M (eta Q Q') (eta_ker_of_rat_span hR h)
    obtain ⟨B₀, hB₀⟩ := M.exists_isBase
    have he0 : e ≠ 0 := by
      rw [← he ⟨B₀, hB₀⟩]; exact sgn_ne_zero (hS.base_facts _).2.2.2
    obtain ⟨G, hG, hQ⟩ := eq_of_ratio_factor (c := e * Real.exp τ)
      (μ := fun i => Real.exp (x i)) hS (mul_ne_zero he0 (Real.exp_pos _).ne') (fun B => by
        rw [ratio_eq_eps_exp hS, he, hx B, filter_ground_eq_bset, Real.exp_add, Real.exp_sum]
        ring)
    exact ⟨G, _, hG, fun i => Real.exp_pos _, hQ⟩

/-- **Theorem 7.4(b)**, as stated in the paper (`R` a square basis). -/
theorem thm74b (hS : Setup Q Q' M) {R : Set (Bases M →₀ ℤ)} (hRsq : ∀ z ∈ R, IsSquare M z)
    (hRli : LinearIndependent ℤ (fun z : R => (z : Bases M →₀ ℤ)))
    (hR : Submodule.span ℤ R = LinearMap.ker (incidence M)) :
    (∃ (G : Matrix (Fin k) (Fin k) ℝ) (μ : Fin n → ℝ), G.det ≠ 0 ∧ (∀ i, 0 < μ i) ∧
        Q' = G * Q * diagonal μ) ↔
      (∃ e : ℝ, ∀ B : Bases M, eps Q Q' B = e) ∧
        ∀ z ∈ R, z.sum (fun B c => (c : ℝ) * eta Q Q' B) = 0 := by
  have := rankPos_of_hasSquareBasis ⟨R, hRsq, hRli, hR⟩
  exact thm74b_of_span hS (fun z hz => (hRsq z hz).mem_ker)
    (fun u hu => ⟨1, one_ne_zero, by rw [one_smul, hR]; exact hu⟩)

/-! ### Uniqueness of `D` for connected `M` -/

open scoped Classical in
theorem bset_insert {B : Bases M} {a : Fin n} {D : Set (Fin n)} (hB : B.1 = insert a D)
    (ha : a ∉ D) :
    bset B = insert a (Finset.univ.filter (· ∈ D)) ∧ a ∉ Finset.univ.filter (· ∈ D) := by
  refine ⟨?_, by simpa using ha⟩
  ext x; simp [bset, hB]

/-- **Uniqueness after Theorem 7.4.** If `M` is connected (on the ground set `[n]`), then `D` is
unique up to a nonzero scalar factor. -/
theorem thm74_unique (hS : Setup Q Q' M) (hE : M.E = Set.univ) (hC : Conn M)
    {G₁ G₂ : Matrix (Fin k) (Fin k) ℝ} {μ₁ μ₂ : Fin n → ℝ} (hμ₁ : ∀ i, μ₁ i ≠ 0)
    (hμ₂ : ∀ i, μ₂ i ≠ 0) (h₁ : Q' = G₁ * Q * diagonal μ₁) (h₂ : Q' = G₂ * Q * diagonal μ₂) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ i, μ₂ i = c * μ₁ i := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨a₀⟩⟩
  · exact ⟨1, one_ne_zero, fun i => hn.elim i⟩
  -- the two factorizations on a basis `insert a D`
  have key : ∀ (a : Fin n) (D : Set (Fin n)) (hB : M.IsBase (insert a D)), a ∉ D →
      ∃ X Y : ℝ, Y ≠ 0 ∧ μ₁ a * X = μ₂ a * Y ∧
        X = G₁.det * ∏ i ∈ Finset.univ.filter (· ∈ D), μ₁ i ∧
        Y = G₂.det * ∏ i ∈ Finset.univ.filter (· ∈ D), μ₂ i := by
    intro a D hB ha
    obtain ⟨hb, hna⟩ := bset_insert (B := ⟨insert a D, hB⟩) rfl ha
    have e1 := ratio_of_eq hS h₁ ⟨insert a D, hB⟩
    have e2 := ratio_of_eq hS h₂ ⟨insert a D, hB⟩
    have hr := (hS.base_facts ⟨insert a D, hB⟩).2.2.2
    rw [hb, Finset.prod_insert hna] at e1 e2
    refine ⟨_, _, ?_, ?_, rfl, rfl⟩
    · intro h0; apply hr; rw [e2, ← mul_assoc, mul_comm G₂.det, mul_assoc, h0, mul_zero]
    · linear_combination e2 - e1
  have hμ2 : ∀ a, μ₂ a * μ₁ a₀ = μ₂ a₀ * μ₁ a := by
    intro a
    by_cases haa : a = a₀
    · rw [haa]
    obtain ⟨K, hK, haK, ha₀K⟩ := conn_exists_isCircuit hC (by rw [hE]; trivial)
      (by rw [hE]; trivial) haa
    obtain ⟨D, haD, ha₀D, hBa, hBa₀⟩ := exists_pair_of_isCircuit' hK haK ha₀K haa
    obtain ⟨X, Y, hY, ea, hXa, hYa⟩ := key a D hBa haD
    obtain ⟨X', Y', -, ea₀, hXa₀, hYa₀⟩ := key a₀ D hBa₀ ha₀D
    rw [hXa₀.trans hXa.symm, hYa₀.trans hYa.symm] at ea₀
    have h0 : (μ₂ a * μ₁ a₀ - μ₂ a₀ * μ₁ a) * Y = 0 := by
      linear_combination (-μ₁ a₀) * ea + μ₁ a * ea₀
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hY)
  refine ⟨μ₂ a₀ / μ₁ a₀, div_ne_zero (hμ₂ a₀) (hμ₁ a₀), fun i => ?_⟩
  rw [div_mul_eq_mul_div, eq_div_iff (hμ₁ a₀)]
  linarith [hμ2 i]

/-- In Theorem 7.4(b), for connected `M`, the positive `D` is unique up to a positive factor. -/
theorem thm74b_unique (hS : Setup Q Q' M) (hE : M.E = Set.univ) (hC : Conn M)
    {G₁ G₂ : Matrix (Fin k) (Fin k) ℝ} {μ₁ μ₂ : Fin n → ℝ} (hμ₁ : ∀ i, 0 < μ₁ i)
    (hμ₂ : ∀ i, 0 < μ₂ i)
    (h₁ : Q' = G₁ * Q * diagonal μ₁) (h₂ : Q' = G₂ * Q * diagonal μ₂) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, μ₂ i = c * μ₁ i := by
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨a₀⟩⟩
  · exact ⟨1, one_pos, fun i => hn.elim i⟩
  obtain ⟨c, -, hc⟩ := thm74_unique hS hE hC (fun i => (hμ₁ i).ne') (fun i => (hμ₂ i).ne') h₁ h₂
  refine ⟨c, ?_, hc⟩
  have h1 := hμ₁ a₀
  have h2 := hμ₂ a₀
  rw [hc a₀] at h2
  exact pos_of_mul_pos_left h2 h1.le

end SquareBasis
