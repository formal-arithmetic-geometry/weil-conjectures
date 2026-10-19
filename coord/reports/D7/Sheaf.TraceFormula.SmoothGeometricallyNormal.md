## What changed

Proved `AlgebraicGeometry.smooth_geometrically_normal` in
`Sheaf.TraceFormula.SmoothGeometricallyNormal`, preserving its entire statement,
universe, visibility, definitions and public imports. For each arbitrary extension K/k,
`pullback.snd` is smooth; `LocallyOfFiniteType.isLocallyNoetherian` and the already
proved `IsRegular.of_smooth` give `IsRegularScheme`. Specializing proves the finite
purely inseparable clause. For an arbitrary extension the regular-local-ring instance
gives domain stalks, `IsRegular.isIntegrallyClosed_stalk` gives integral closedness,
and `isReduced_of_isReduced_stalk` gives reducedness. No new declarations or modules.

The node's proof, proof dependencies and proof origin now describe this shorter route.
The existing theorem docstring retains the original expanded plan; the proof body and
updated node use its already proved source-library replacements. The mathematical route
remains smooth base change, regularity, normality, reducedness, exactly Stacks Varieties
Tags 056T and 056S, with Properties Tag 0569. The unit `sk-i-curve-zero` realizes neither
its statement nor a required step through this auxiliary node, so no unit step is bypassed.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.smooth_geometrically_normal`
(node `lem-trf-smooth-geometrically-normal`). Added 0 holes; split off 0 statements.
There are no remaining `sorry`s in the delivered module, and none added elsewhere.

The final module, with all seven proof imports removed, compiled cleanly through
`lcompile.py` in 2.2 seconds. It quantifies over arbitrary field
extensions before specializing, so finite purely inseparable extensions are included
without any extra perfectness assumption. Empty schemes require no point and are covered
by the universal stalk hypotheses. Neither dimension bounds, connectedness, separation,
quasi-compactness nor finiteness of the arbitrary extension is assumed.

## No longer needed

Removed these proof-only imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: only the smooth clause of
  `lem-pc-proper-base-change` is used; it is available from the existing smooth import.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: smooth-to-finite-type
  instances are already available through the public statement imports.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: same reason.
- `Mathlib.AlgebraicGeometry.Noetherian`: already public through `IsRegularScheme`.
- `Mathlib.RingTheory.Noetherian.Defs`: field Noetherianity is already available.
- `Sheaf.AlgebraicGeometry.GeometricRegularitySmoothFieldCriterion`: use the proved
  `IsRegular.of_smooth` directly, avoiding the identity-extension pullback comparison.
- `Sheaf.AlgebraicGeometry.RegularNormalDecomposition`: use the proved
  `IsRegular.isIntegrallyClosed_stalk` directly, needing none of the decomposition clauses.

Removed the proof dependency
`lem-weil-pbc-geometric-regularity-smooth-field-criterion` and its obsolete `tool_uses`
approval. The module `Sheaf.AlgebraicGeometry.GeometricRegularitySmoothFieldCriterion`
is unnecessary for this proof. Also removed `lem-weil-pbc-finite-type-over-noetherian`
as an explicit dependency: only local Noetherian permanence from `pqf-def-locnoeth` is
needed, with no finite-type compactness argument. Retained `rem-pc-regular-normal` because
its normality clause is still used, realized by the proved source-library theorem rather
than importing the holed full normal-decomposition module. These are pruning claims for
this proof only, not claims that other parents no longer need those modules or nodes.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The original plan was unnecessarily long:
the public `IsRegularScheme` import already exposes
`WeilConjectures.AlgebraicGeometry.Regular`, containing both general smooth regularity
and regular-stalk integral closedness. The former is attached to `lem-sc-smooth-regular`;
its Lean declaration works in every dimension despite that node's curve wording. The
updated proof cites the exact stronger source-library declaration, which has already
been proved. The normality theorem is exactly the first clause of `rem-pc-regular-normal`.

Searches executed with `msearch.py`: LeanFinder for smooth schemes being regular and
normal after field extension (8 smoothness hits, no exact theorem); Loogle for
`AlgebraicGeometry.IsRegular` (identifier unavailable in that search service, not evidence
of absence); grep for `smooth.*regular|regular.*smooth` (no service hits). Direct `rg`
and full source reading found `IsRegular.of_smooth` and
`IsRegular.isIntegrallyClosed_stalk` in the project's source library. Stacks source
`literature/stacks-project/varieties.tex`, labels `lemma-smooth-regular` and
`lemma-smooth-geometrically-normal`, was read and agrees with this route.

Two compile requests received no server answer within the request timeout; retries
succeeded in 2.7 and 2.2 seconds respectively. These were transient service delays.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
