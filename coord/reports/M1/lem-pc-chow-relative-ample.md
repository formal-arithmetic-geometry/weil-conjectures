## Worker report

The module states `AlgebraicGeometry.chow_relative_ample`. It binds a natural number `m`, schemes
`S`, `Z`, `X'`, proper morphisms `g` and `π`, and an immersion `j` compatible with the structure
map of `ℙ(ULift (Fin (m+1)); S)`. The conclusion has: (1) closedness of `j` and projectivity of
`π ≫ g`; (2) closedness of the base-change lift and projectivity of `π`; and (3) an invertible
pullback of the Proj twisting sheaf whose restriction to every affine open inverse image from `S`
and `Z` is ample. The inverse-image restrictions are expressed by `Scheme.Modules.tensorPullback`
of the corresponding open immersion.

The hypotheses are rendered by `[IsProper g]`, `[IsProper π]`, `[IsImmersion j]`, and the equality
`hj : π ≫ g = j ≫ (ℙ(...) ↘ S)`. The first two conclusion clauses use `IsClosedImmersion`,
`IsProjective`, and `ProjectiveSpace.liftBaseChange`; the final clause uses the explicit
`Proj.twist (MvPolynomial.homogeneousSubmodule ...) 1` pulled back by `tensorPullback`, with
`Scheme.Modules.IsAmple` on each affine inverse image.

Dependencies used are `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` (`ProjectiveSpace`,
`ProjectiveSpace.liftBaseChange`), `Sheaf.AlgebraicGeometry.TensorPullback`
(`Scheme.Modules.tensorPullback`), `Sheaf.AlgebraicGeometry.Morphisms.Projective`
(`IsProjective`), `Sheaf.AlgebraicGeometry.Ample` (`IsAmple`), and Mathlib's
`IsProper`, `IsImmersion`, and `IsClosedImmersion`.

Edge cases checked: `m = 0`; arbitrary schemes including empty schemes; affine opens that are
empty; and the inverse-image open equal to top. The finite coordinate type is `ULift (Fin (m+1))`.
Searches: LeanFinder/grep found no existing Chow relative ampleness statement; Loogle found no
matching theorem; grep of Mathlib and `WeilConjectures` found only the affine projective ampleness
input, which is cited above.

## Earlier second reading (a previous round; superseded)

The node and module were read together. The properness and immersion hypotheses match exactly.
The first two clauses match closedness and projectivity of `g'` and `π`, with the induced morphism
represented by `ProjectiveSpace.liftBaseChange`. The twisting sheaf is the pullback of the integral
Proj twist, and both affine-open clauses use the appropriate inverse-image open and module
restriction. No mismatch was found.


## Second reading by M1

Read the sandbox node and Lean signature independently, every statement dependency's
statement and recorded declaration, and the source declarations themselves. There are no
new definition nodes, dependency modules, or statement corrections in this delivery.

Source reading: this clone has no `literature/stacks-project/coherent.tex`; the same Stacks
TeX is available at `/home/ubuntu/c1-stacks-review/coherent.tex`, which I read at
`remark-chow-Noetherian` (lines 5074–5092) and the Chow paragraph of
`proposition-proper-pushforward-coherent` (lines 5180–5204). The paragraph explicitly
asserts the isomorphism between the two pulled-back O(1)'s and both relative ampleness
properties. I also read `/home/ubuntu/c1-stacks-review/morphisms.tex` at
`lemma-image-proper-scheme-closed` (9949) and `lemma-characterize-ample-on-finite-type`
(9611). The ambient coherence proposition assumes a locally Noetherian base, and Chow's
existence theorem uses a Noetherian base. This node concerns the consequences once the
proper maps and immersion are given, not existence of a Chow modification. Those
consequences use proper-over-separated, base change, and finite-type relative ampleness;
the latter two source lemmas have arbitrary scheme bases. No Noetherian assumption belongs
in this node's signature, and none is added.

Objects, hypotheses, and conclusions, matched item by item:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Dimension m ≥ 0 | `(m : ℕ)` | Exact; zero included. |
| Schemes S, Z, X' | `(S Z X' : Scheme.{u})` | Exact; arbitrary universe u. |
| Proper g : Z → S | `(g : Z ⟶ S) [IsProper g]` | Exact Mathlib properness. |
| Proper π : X' → Z | `(π : X' ⟶ Z) [IsProper π]` | Exact; no finiteness hypothesis added. |
| Projective m-space over S | `ℙ(ULift.{u} (Fin (m + 1)); S)` | Exact recorded base-change model, m+1 homogeneous coordinates. |
| Immersion j into that space | `(j : X' ⟶ ℙ(...; S)) [IsImmersion j]` | Exact; `isImmersion_iff_exists` gives closed-then-open factorization. |
| p ∘ j = g ∘ π | `hj : π ≫ g = j ≫ (ℙ(...; S) ↘ S)` | Exact, reversed equality with Lean's composition order. |
| g' = g ∘ π | Explicit `π ≫ g` | Exact; no unconstrained extra map. |
| L = j* O(1) | Twice-applied `Scheme.Modules.tensorPullback`, first along `toProjInt`, then along j, to `Proj.twist ... 1` | Exact integral-model O(1) with the recorded tensor pullback. |
| L invertible | `∃ hL : (...).IsInvertible` | Exact `Scheme.Modules.IsInvertible`, a Prop witness. |
| (1) j closed | `IsClosedImmersion j` | Exact. |
| (1) g' projective | `IsProjective (π ≫ g)` | Exact H-projective and quasi-compact convention. |
| (2) induced (j,π) closed | `IsClosedImmersion (ProjectiveSpace.liftBaseChange π j hj)` | Exact lift to ℙ(m; Z); read its definition and projection identities. |
| (2) π projective | `IsProjective π` | Exact. |
| (2) L ≅ (j,π)* O(1) over Z | `Nonempty ((tensorPullback j).obj ... ≅ (tensorPullback (liftBaseChange π j hj)).obj ...)` | MISSING originally; now restored, with both O(1)'s explicitly pulled from the same integral twist. |
| (3) every affine open V of S | `∀ V : S.Opens, IsAffineOpen V → ...` | Exact; no fixed cover or quasi-compactness of S. |
| L restricted to g'⁻¹(V) ample | `@Scheme.Modules.IsAmple ((π ≫ g) ⁻¹ᵁ V).toScheme ((tensorPullback ...ι).obj ...) hV` | Exact absolute ampleness on the inverse-image open; hV supplies the definition's invertibility instance. |
| (3) every affine open W of Z | `∀ W : Z.Opens, IsAffineOpen W → ...` | Exact and independent of V. |
| L restricted to π⁻¹(W) ample | `@Scheme.Modules.IsAmple (π ⁻¹ᵁ W).toScheme ((tensorPullback ...ι).obj ...) hW` | Exact, using the same L. |

Dependency audit: `ProjectiveSpace` is the fibre product of S with integral polynomial
Proj; `toProjInt` is its second projection. `liftBaseChange` is the universal-property
lift, with first projection π and its projective-space map recovering j. The declared
`tensorPullback` implements inverse image followed by extension of scalars, not the
Mathlib sectionwise pullback. `IsProjective` extends `IsHProjective` and `QuasiCompact`.
`Scheme.Modules.IsInvertible` is local triviality as an O-module. `IsAmple` includes
quasi-compactness and positive tensor powers with affine nonvanishing neighbourhoods.
`Proj.twist` is the sheaf of locally fractional sections of degree 1. The upstream
`ProjectiveSpace.twist` uses the different sectionwise pullback; the project explicitly
records a stage-3 bridge and the affine-projective ampleness dependency uses the same
integral `Proj.twist` and tensor-pullback expression as this delivery. No definition is
copied or added here. `IsProper` gives finite type because universal closedness gives
quasi-compactness. The permanence matches are Mathlib instances; the closed-image
criterion is `IsClosedImmersion.iff_isPreimmersion`, and proper-over-separated is
`IsProper.of_comp`. Their hypotheses agree with the node; the convention dependency
introduces no separate notion. The affine-projective ampleness theorem has arbitrary
commutative ring A, the same finite-coordinate projective space, and the same twist;
it supplies the required affine-restriction input without adding a field hypothesis.

Edge cases: m = 0 gives one homogeneous coordinate (P^0), not an empty family. An empty
coordinate index is not a case of this node, which uses m+1 coordinates. Empty schemes
and empty affine opens remain permitted: there is no `Nonempty` assumption on a scheme;
`Nonempty` in the conclusion asserts existence of an isomorphism. The zero ring as
an affine base is permitted and gives the empty scheme. A zero module on a nonempty
scheme is not substituted for O(1); on the empty scheme local invertibility and
nonvanishing conditions are vacuous and compactness holds. No characteristic, field,
Noetherian, or separated-scheme hypothesis is introduced. One arbitrary universe u
holds all objects of a diagram; any mixed-size diagram can be lifted to a common
universe. The ULifts keep the finite coordinates and integral coefficient ring in u.
There are no test-scheme quantifiers or independent small universes that could make
a hypothesis vacuous. Affine opens equal to top are included whenever the base is affine.

Independent searches (the exact queries are logged in sandbox `searches.jsonl`):
- LeanSearch: `A proper immersion into projective space is closed and the hyperplane bundle is ample on inverse images of affine opens`; service returned Internal Server Error, recorded unavailable, no search verdict inferred.
- LeanFinder: `Chow lemma projective morphism relative ampleness hyperplane line bundle over a scheme`; eight Proj construction/properness results, no matching three-clause theorem.
- Loogle: `"IsImmersion", "IsProper"`; zero hits.
- Mathlib grep: `Chow|relativelyAmple|relative_ample|chow_relative_ample` under AlgebraicGeometry; zero hits.
- Independent rg on project and upstream AlgebraicGeometry using `Chow`, `relative_ample`, and `relatively.?ample`, and a separate search for projective-space twists. Opened `ChowLemma/EmbeddingOver.lean`: its `isClosedImmersion_toProjectiveSpaceSource` only concerns the chosen `ChowModification f` over a Noetherian base and asserts one closed-immersion clause. It is not this arbitrary-diagram statement. Existing Proj and projective-space twists and the affine-projective ampleness input were read; no duplicate general theorem found. Full declaration name search in upstream names, upstream source, and the project's Lean found no `AlgebraicGeometry.chow_relative_ample`.

Mismatches repaired: restored the missing twist-pullback isomorphism of clause (2);
removed the statement's `let L` by repeating the explicit object (no private definition
or notation); expanded the proof docstring into the node's four steps, including the
graph as the base change of the diagonal of g, the O(1) comparison, and both affine
restrictions; added the standard copyright header. No natural-language node statement,
hypothesis, dependency list, or proof step was changed. The earlier second reading's
claim of no mismatch was incorrect: it missed the displayed isomorphism.

The existing `attribute [local instance] MvPolynomial.gradedAlgebra` is retained:
`coord/STATE.md` FILE-LOCAL NOTATION explicitly permits local registration of existing
instances (LOCAL ATTRIBUTE INSTANCES); no new instance data is declared. All variables
and the universe are bound; there are no hollow definitions and the only proof is the
named theorem's `sorry`. Lines are at most 100 characters. The node's `lean.statement`
is copied verbatim from the final theorem signature. Server single-file compilation
with `scompile.py M1 lem-pc-chow-relative-ample` succeeded in 2.0 seconds without warnings.
