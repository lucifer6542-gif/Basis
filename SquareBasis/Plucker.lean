module

public import SquareBasis.Criterion
public import SquareBasis.Exact
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Section 7.2 of the paper: invertible column scaling (Theorem 7.4)

For real `k × n` matrices `Q`, `Q'` of rank `k`:

* `minorF Q f = det (Q with columns f)`, `pl Q I = p_I(Q)` (columns of `I` in increasing order).
* `pl_scale` — the formula `p_I(GQD) = det G · (∏_{i ∈ I} μ_i) · p_I(Q)` before Theorem 7.4.
* `plucker_inj` — the injectivity of the Plücker embedding used in the proof.

Theorem 7.4 itself is in `Theorem74.lean`.
-/

@[expose] public section

namespace SquareBasis

open Matrix Matroid

variable {k n : ℕ}

/-- The `k × k` minor of `Q` on the columns `f`. -/
noncomputable def minorF (Q : Matrix (Fin k) (Fin n) ℝ) (f : Fin k → Fin n) : ℝ :=
  (Q.submatrix id f).det

/-- The Plücker coordinate `p_I(Q) = det Q_I` (zero unless `|I| = k`). -/
noncomputable def pl (Q : Matrix (Fin k) (Fin n) ℝ) (I : Finset (Fin n)) : ℝ :=
  if h : I.card = k then minorF Q (I.orderEmbOfFin h) else 0

/-! ### Minors -/

/-- Every minor is `0` or `±` a Plücker coordinate, with a sign independent of `Q`. -/
theorem minorF_eq (f : Fin k → Fin n) :
    ∃ (I : Finset (Fin n)) (e : ℝ), ∀ Q : Matrix (Fin k) (Fin n) ℝ, minorF Q f = e * pl Q I := by
  classical
  by_cases hf : Function.Injective f
  · set I : Finset (Fin n) := Finset.univ.image f
    have hI : I.card = k := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ c, f c ∈ I := fun c => Finset.mem_image_of_mem f (Finset.mem_univ c)
    let π₀ : Fin k → Fin k := fun c => (I.orderIsoOfFin hI).symm ⟨f c, hmem c⟩
    have hπ₀ : ∀ c, I.orderEmbOfFin hI (π₀ c) = f c := by
      intro c
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp [π₀]
    have hinj : Function.Injective π₀ := by
      intro a b h
      apply hf
      rw [← hπ₀ a, ← hπ₀ b, h]
    let π : Equiv.Perm (Fin k) := Equiv.ofBijective π₀ (Finite.injective_iff_bijective.1 hinj)
    refine ⟨I, (Equiv.Perm.sign π : ℝ), fun Q => ?_⟩
    have : Q.submatrix id f = (Q.submatrix id (I.orderEmbOfFin hI)).submatrix id π := by
      ext r c
      simp [π, hπ₀]
    rw [minorF, this, det_permute', pl, dite_eq_left hI]
    rfl
  · refine ⟨∅, 0, fun Q => ?_⟩
    obtain ⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by
      by_contra h
      push Not at h
      exact hf fun a b hab => h a b hab
    rw [zero_mul, minorF]
    exact det_zero_of_column_eq hne (fun r => by simp [hab])

/-- Scaling all Plücker coordinates scales all minors. -/
theorem minorF_scale {Q₁ Q₂ : Matrix (Fin k) (Fin n) ℝ} {c : ℝ}
    (h : ∀ I : Finset (Fin n), I.card = k → pl Q₂ I = c * pl Q₁ I) (f : Fin k → Fin n) :
    minorF Q₂ f = c * minorF Q₁ f := by
  obtain ⟨I, e, he⟩ := minorF_eq f
  rw [he, he]
  by_cases hI : I.card = k
  · rw [h I hI]; ring
  · simp [pl, hI]

/-- **Equation (7.1).** `p_I(GQD) = det(G) (∏_{i ∈ I} μ_i) p_I(Q)` for `D = diag(μ)`. -/
theorem pl_scale (G : Matrix (Fin k) (Fin k) ℝ) (Q : Matrix (Fin k) (Fin n) ℝ) (μ : Fin n → ℝ)
    (I : Finset (Fin n)) :
    pl (G * Q * diagonal μ) I = G.det * (∏ i ∈ I, μ i) * pl Q I := by
  by_cases hI : I.card = k
  · simp only [pl, dite_eq_left hI, minorF]
    set f := I.orderEmbOfFin hI
    have : (G * Q * diagonal μ).submatrix id f =
        G * Q.submatrix id f * diagonal (fun c => μ (f c)) := by
      ext r c
      rw [submatrix_apply, mul_diagonal, mul_diagonal]
      rfl
    rw [this, det_mul, det_mul, det_diagonal]
    have hprod : ∏ c, μ (f c) = ∏ i ∈ I, μ i := by
      rw [← Finset.image_orderEmbOfFin_univ I hI,
        Finset.prod_image (fun a _ b _ h => f.injective h)]
    rw [hprod]; ring
  · simp [pl, hI]

/-- The determinant of the identity with column `r` replaced by `v` is `v r`. -/
theorem det_updateCol_one (r : Fin k) (v : Fin k → ℝ) :
    ((1 : Matrix (Fin k) (Fin k) ℝ).updateCol r v).det = v r := by
  rw [← cramer_apply, cramer_one]
  rfl

/-- **Injectivity of the Plücker embedding.** If `p(Q₂) = c · p(Q₁)` with `c ≠ 0` and `Q₁` has
rank `k`, then `Q₂ = G Q₁` for some `G` with `det G = c`. -/
theorem plucker_inj {Q₁ Q₂ : Matrix (Fin k) (Fin n) ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : ∀ I : Finset (Fin n), I.card = k → pl Q₂ I = c * pl Q₁ I)
    {I₀ : Finset (Fin n)} (hI₀ : I₀.card = k) (h₀ : pl Q₁ I₀ ≠ 0) :
    ∃ G : Matrix (Fin k) (Fin k) ℝ, G.det = c ∧ Q₂ = G * Q₁ := by
  classical
  have hm := minorF_scale h
  set f₀ := (I₀.orderEmbOfFin hI₀ : Fin k → Fin n)
  have hd₁ : (Q₁.submatrix id f₀).det ≠ 0 := by
    have := h₀; simp only [pl, dite_eq_left hI₀, minorF] at this; exact this
  have hd₂ : (Q₂.submatrix id f₀).det ≠ 0 := by
    have := hm f₀; simp only [minorF] at this; rw [this]; exact mul_ne_zero hc hd₁
  set A₁ := Q₁.submatrix id f₀
  set A₂ := Q₂.submatrix id f₀
  -- `R_t = A_t⁻¹ Q_t` has entries given by ratios of minors
  have hsub : ∀ (A : Matrix (Fin k) (Fin k) ℝ) (Q : Matrix (Fin k) (Fin n) ℝ) (f : Fin k → Fin n),
      (A * Q).submatrix id f = A * Q.submatrix id f := by
    intro A Q f; ext r c; rfl
  have hentry : ∀ (Q : Matrix (Fin k) (Fin n) ℝ), (Q.submatrix id f₀).det ≠ 0 →
      ∀ r j, ((Q.submatrix id f₀)⁻¹ * Q) r j =
        minorF Q (Function.update f₀ r j) / (Q.submatrix id f₀).det := by
    intro Q hQ r j
    have hinv : (Q.submatrix id f₀)⁻¹ * Q.submatrix id f₀ = 1 :=
      nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hQ)
    have hupd : ((Q.submatrix id f₀)⁻¹ * Q).submatrix id (Function.update f₀ r j) =
        (1 : Matrix (Fin k) (Fin k) ℝ).updateCol r (fun s => ((Q.submatrix id f₀)⁻¹ * Q) s j) := by
      rw [← hinv]
      ext s c
      by_cases hcr : c = r
      · subst hcr; simp
      · simp only [submatrix_apply, id, updateCol_apply, hcr, ite_false,
          Function.update_of_ne hcr]
        rfl
    have := congrArg det hupd
    rw [det_updateCol_one, hsub, det_mul, det_nonsing_inv] at this
    rw [← this, minorF, Ring.inverse_eq_inv']
    field_simp
  have hR : A₂⁻¹ * Q₂ = A₁⁻¹ * Q₁ := by
    ext r j
    rw [hentry Q₂ hd₂, hentry Q₁ hd₁, hm, show (Q₂.submatrix id f₀).det =
      c * (Q₁.submatrix id f₀).det from hm f₀]
    field_simp
  refine ⟨A₂ * A₁⁻¹, ?_, ?_⟩
  · rw [det_mul, det_nonsing_inv, Ring.inverse_eq_inv',
      show A₂.det = c * A₁.det from hm f₀]
    field_simp
  · have hA₂ : A₂ * A₂⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd₂)
    calc Q₂ = A₂ * (A₂⁻¹ * Q₂) := by rw [← Matrix.mul_assoc, hA₂, Matrix.one_mul]
      _ = A₂ * (A₁⁻¹ * Q₁) := by rw [hR]
      _ = A₂ * A₁⁻¹ * Q₁ := by rw [Matrix.mul_assoc]

end SquareBasis
