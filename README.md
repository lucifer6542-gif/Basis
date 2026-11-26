# SquareBasis — Lean 4 formalization of *A Square Basis Theorem for Matroids*

[![Lean build](https://github.com/lucifer6542-gif/Basis/actions/workflows/lean.yml/badge.svg)](https://github.com/lucifer6542-gif/Basis/actions/workflows/lean.yml)

A machine-checked formalization of Youngsu Kim, *A Square Basis Theorem for Matroids*:
Theorem 1.1 **along the route of the paper**, and the other results proved in the paper
(Sections 2–8 and the claims of Figure 1). The list of what is not formalized is below.

Paper: [A Square Basis Theorem for Matroids](https://lucifer6542-gif.github.io/Matroid/square-basis.html)
(DOI [10.5281/zenodo.24135970](https://doi.org/10.5281/zenodo.24135970)).

> For every finite matroid `M` of rank at least one, the integer kernel `ker_ℤ A_M` of the
> basis incidence matrix has a `ℤ`-basis consisting of square relations
> `e_{B+i} - e_{B+j} - e_{B'+i} + e_{B'+j}`.

```lean
theorem SquareBasis.square_basis_theorem_paper {α : Type*} (M : Matroid α)
    [M.Finite] [M.RankPos] :
    ∃ S : Set (Bases M →₀ ℤ), (∀ z ∈ S, IsSquare M z) ∧
      LinearIndependent ℤ (fun z : S => (z : Bases M →₀ ℤ)) ∧
      Submodule.span ℤ S = LinearMap.ker (incidence M)
```

The statement uses Mathlib's own definitions of matroids (`Matroid`, `Matroid.IsBase`),
linear independence and span. The project-specific definitions (`Bases`, `incidence`,
`IsSquare`) are short and are in `SquareBasis/Defs.lean`.

## Status

- No `sorry`. A clean build finishes with no errors and no warnings.
- `lake env lean CheckAxioms.lean` reports, for every Lean theorem named in the table below,
  only Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound`.
- `axiom-audit` (leanprover-community) checks every declaration of the project (about 840)
  and finds no axiom outside these three.
- Two independent re-checks are run as well: `leanchecker` replays every module of the
  project in the Lean kernel, and `nanoda` (an external type checker, shipped with the pinned
  toolchain) checks every result named in the table below together with all the
  declarations it depends on (about 35,000), permitting only the three axioms above. Both
  report no errors.
- GitHub Actions rebuilds the project and reruns the axiom check, `axiom-audit`,
  `leanchecker` and `nanoda` on every push; the badge above shows the latest result.

## Results of the paper and their Lean names

| Paper | Lean | File |
|---|---|---|
| Theorem 1.1 | `square_basis_theorem_paper`; with the count `N - rank A_M`: `thm11` | `PaperRoute.lean`, `Section8.lean` |
| Figure 1 (`U_{2,4}`: the squares are `±z₁, ±z₂, ±z₃`, `rank ker_ℤ = 2`, `z₁ = z₂ - z₃`, any two form a `ℤ`-basis) | `figure1` | `Figure1.lean` |
| Definition 2.1 (square relations) | `IsSquare`, `HasSquareBasis` | `Defs.lean` |
| Lemma 2.2 (squares = nonzero symmetric exchange binomials) | `lemma22`; binomial form `binom_square` | `Section2.lean`, `Toric.lean` |
| Proposition 2.3(a) (rank 0) | `prop23a` | `PaperRoute.lean` |
| Proposition 2.3(b) (deleting a loop) | `prop23b`, `prop23b_full` | `PaperRoute.lean`, `Section2.lean` |
| Proposition 2.3(c) (coloops) | `prop23c` | `Section2.lean` |
| Lemma 2.4 (duality) | `hasSquareBasis_dual_iff` | `Duality.lean` |
| `ht I_M = N - rank A_M` (Section 2, cited in the paper; proved here for rank ≥ 1) | `cor71_height`, `codim_eq` | `Toric.lean` |
| Proposition 3.1 (direct sums), Steps 1–5 | `prop31` (`mem_ker_iff_split`, `step3`, `tensor_basis`, `forest_basis`, `sq1`–`sq3`) | `Section3.lean`, `LinAlg.lean` |
| Lemma 4.1 | `lemma41`, `lemma41_full` | `Exact.lean` |
| Theorem 4.2 (exact sequence) | `thm42` | `Exact.lean` |
| Theorem 4.3 (lifting along a spanning tree of `H`) | `thm43` | `Section4.lean` |
| Proposition 4.4 (`H` connected ⟺ `Φ` connected) | `prop44_iff` | `Exact.lean` |
| Theorem 4.5 | `thm45` | `Section5.lean` |
| Theorem 4.6 (connected matroids) | `thm46` | `Section4.lean` |
| Lemma 5.1 | `lemma51` | `Section5.lean` |
| Lemma 5.2 | `lemma52` | `Section5.lean` |
| Proposition 5.3 (`λ = 1`, minimal counterexample) | `prop53` | `Section5.lean` |
| Tutte's theorem (cited in the paper; proved here) | `tutte_minor` | `Minor.lean` |
| Lemma 6.1 (unitriangularity) | `lemma61` | `Section6.lean` |
| Proposition 6.2 (uniform matroids) | `prop62` | `Section6.lean` |
| Example 6.3 (`U_{2,4}`; `r_{24} = z₁`, `r_{34} = z₂`) | `example63`, `example63_z` | `Section6.lean`, `Figure1.lean` |
| Corollary 7.1 (a) ⟺ (b) ⟺ (c) | `cor71` | `Toric.lean` |
| Corollary 7.1, existence and minimal number of generators | `cor71_exists`, `cor71_minimal` | `Toric.lean` |
| Theorem 7.4(a), (b) | `thm74a`, `thm74b` | `Theorem74.lean` |
| Uniqueness of `D` for connected `M` (after Theorem 7.4) | `thm74_unique`, `thm74b_unique` | `Theorem74.lean` |
| Remark 7.5 (part (b) needs only an `ℝ`-spanning set; `U_{2,5}` example of index 2) | `thm74b_of_span`, `remark75` | `Theorem74.lean`, `Remark75.lean` |
| Proposition 8.2 (`L_□(M) = ker_ℤ A_M`), from Theorem 1.1 | `prop82` | `Section8.lean` |

Each formal proof follows the argument written in the paper, with these differences in detail:

- Where a formal statement has weaker hypotheses than the paper's (Theorem 4.3 and
  Proposition 4.4 need only that `v` is not a coloop, resp. that `M` is connected; Theorem 7.4(b)
  needs only that `R` spans `ker_ℝ A_M`, as noted in Remark 7.5), the paper's statement follows
  from it.
- Proposition 6.2: `rank A_{U_{k,n}} = n` is shown by an elementary argument (`k e_x` lies in
  the image for every `x`).
- Theorem 7.4: the step "`zᵀη = 0` for `z ∈ R` gives `η = A_Mᵀ x`" uses the same
  spanning-forest argument that the paper uses for the signs (`orth_ker`, for any abelian
  group). The hypothesis that `M` is the matroid with set of bases `𝓑(Q) = 𝓑(Q')` is
  `Setup Q Q' M`. The uniqueness statement takes `M` on the ground set `[n]` and is proved
  directly from the exchange pairs `W + a`, `W + b`.
- Corollary 7.1: `𝒴 = K[y^{±1}]` is the group algebra `K[ℤ^𝓑]`, shown to be the localization
  of `K[y]` at `p` (`isLocalization`). The standard facts used in the proof
  (`J𝒴 ∩ K[y] = J : p^∞`, and that `𝒴 → K[ℤ^𝓑/L]` has kernel `(y^u - 1 : u ∈ L)`) are proved
  (`satP_eq_comap`, `latKer_eq_latGen`). The height `c` of `I_M 𝒴` is bounded below by a chain
  of `c + 1` prime lattice ideals (`codim_le_height`) and above by Krull's height theorem
  (Mathlib).

Not formalized: results that the paper cites from the literature (Theorem 8.1 of Lasoń and
Michałek, Lehman's theorem in Remark 5.4), the second proof of Proposition 8.2 and Remark 7.2,
which rely on Theorem 8.1, the bibliographic Remarks 7.3 and 8.3, and the complexity estimate
of Remark 8.4.

## Versions (pinned)

| Component | Version |
|---|---|
| Lean | `leanprover/lean4:v4.37.0-rc1` (`lean-toolchain`) |
| Mathlib | commit `e62b985f6c61653ebb17cb81d85565022fb1103d` |

All dependencies are pinned (`lean-toolchain`, `lake-manifest.json`), so the project builds
with exactly these versions on any machine, independently of later changes to Lean or Mathlib.
The CI workflow is pinned as well (runner image and action versions).

## Build

```
# install elan (Lean version manager) first: https://github.com/leanprover/elan
lake exe cache get   # download prebuilt Mathlib
lake build           # must end with "Build completed successfully"
lake env lean CheckAxioms.lean
```

## Files

| File | Content |
|---|---|
| `Defs.lean` | definitions; squares lie in `ker_ℤ A_M` |
| `Rank.lean` | integer rank, submodularity, dual rank |
| `Duality.lean` | coordinate sums, transport of square bases, Lemma 2.4 |
| `Connectivity.lean` | separators, circuit transitivity, common circuits, Tutte (set form) |
| `Minor.lean` | ranks of `M ＼ e`, `M ／ e`; connectivity of minors; Tutte's theorem |
| `Exchange.lean` | the basis-exchange condition |
| `LinAlg.lean` | bases through exact sequences, spanning trees and forests, tensor bases |
| `Lifting.lean` | the lifting step of Theorems 4.2–4.3 |
| `Section3.lean` | Proposition 3.1 |
| `Section5.lean` | Section 5 and Theorem 4.5 |
| `Section4.lean` | Theorems 4.3, 4.6 and Proposition 4.4 (`Φ ⇒ H`) |
| `Exact.lean` | Lemma 4.1, Theorem 4.2, Proposition 4.4 (both directions) |
| `PaperRoute.lean` | Proposition 2.3(a), (b) and Theorem 1.1 along the paper |
| `Section2.lean` | Lemma 2.2, Proposition 2.3(b) in full, Proposition 2.3(c) |
| `Uniform.lean` | `U_{k,n}`, the colex order, the sets `T` and `S` of Proposition 6.2 |
| `Section6.lean` | Lemma 6.1, Proposition 6.2, Example 6.3 |
| `Figure1.lean` | the claims of Figure 1 |
| `Toric.lean` | Corollary 7.1, `ht I_M = c`, binomials of squares |
| `Potential.lean` | potentials along a spanning forest |
| `Criterion.lean` | vectors orthogonal to `ker_ℤ A_M` (`orth_ker`) |
| `Plucker.lean` | Plücker coordinates, column scaling, injectivity of the Plücker embedding |
| `Theorem74.lean` | Theorem 7.4 and the uniqueness of `D` |
| `Remark75.lean` | Remark 7.5 (`U_{2,5}`) |
| `Section8.lean` | Theorem 1.1 with the count, Proposition 8.2 |

## License

Copyright 2026 Youngsu Kim.

The Lean code in this repository is released under the
[Apache License 2.0](LICENSE), the same license as Mathlib. The paper itself is released
separately under CC BY 4.0.
