## What changed

Reduced the ordinary cube `moduleAlpha_baseChange` to the restriction formula for
one intrinsic alpha and the ordinary inverse-image compositor cube. The combining
proof constructs the two source beta identifications, detects equality using the
two adjunction Hom equivalences across the clopen lift, proves the beta restriction
normalization from its defining transpose, and performs the naturality calculation.

Proved `alpha_baseChange` from the ordinary cube by finite exact-derived transformation
pasting. Both public comparison definitions and all original theorem signatures stay
unchanged. There is no use of faithfulness of derived evaluation. The complete item compiled in
20.6 seconds during development. A private interface on ordinary functors avoids
expensive conversion through bundled exact functors; the localization proof remains
in this same module.

## Proved and sorry left

The two original holes are closed: `AlgebraicGeometry.ProEtale.VaryingRing.moduleAlpha_baseChange`
and `AlgebraicGeometry.ProEtale.VaryingRing.alpha_baseChange`.
The ordinary cube is a decomposition into two strictly separate results. Two holes
are added, so this is a decomposition with net zero holes closed, not an unconditional
proof of the cube:

- `AlgebraicGeometry.ProEtale.VaryingRing.moduleAlpha_restriction`, in
  `Sheaf.AlgebraicGeometry.SemilinearAlphaRestriction`, node
  `lem-sf-semilinear-alpha-restriction`.
- `AlgebraicGeometry.ProEtale.VaryingRing.moduleSquareG_cube`, in
  `Sheaf.AlgebraicGeometry.SemilinearPullbackCubeCoherence`, node
  `lem-sf-semilinear-pullback-cube-coherence`.

Each remaining proof is exactly `by sorry` in its own public theorem and module.
There are no holes in definitions, private helpers, or the combining proofs.
The first remaining result concerns a single proper/open square, with no base-change
cube; the second concerns only pullback compositors, with no alpha, beta, open,
proper, or cartesian assumptions. The empty scheme and identity-map cases preserve
the displayed unit and compositor formulas; no nonemptiness is required.

## No longer needed

The proof avoids the complementary-open calculation and sheaf sectionwise uniqueness
step. Instead the clopen comparison and the two adjunction Hom equivalences detect
equality. The following original proof dependencies are not used directly:
`lem-weil-pbc-proper-base-change`, `lem-weil-pbc-open-immersion-base-change`,
`lem-pc-quasi-compact-base-change`, `lem-coef-semilinear-derived-sections`,
`lem-pur-site-restriction-module-adjunction-exact`,
`def-weil-sheaf-of-modules-category`, `def-weil-pbc-proetale-site`, and
`lem-weil-pbc-localization-universal-property`. The required exact localization is
supplied instead by `lem-sp-exact-derived-transformation-pasting`. These declarations
may remain dependencies of the imported constructions; no upstream declaration is
withdrawn and no global module-pruning claim is made.

Removed these redundant explicit proof imports (their required public API is already
available from the existing public import):

- `Sheaf.AlgebraicGeometry.VaryingRingOperations`
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`
- `Sheaf.Paper.SemilinearDerivedSections`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`

The explicit strict-tower calculus import is unnecessary: only its already imported
clopen-lift construction from `def-cbc-strict-tower-proper-open-arrows` is used.

## Where the brief, the DAG or earlier work was wrong

The planned complementary-open section argument is unnecessary for equality detection:
the common source is in the image of the larger open extension and its target,
after restriction, is in the image of the clopen direct image. Two adjunction Hom
bijections give the needed injectivity. The DAG previously treated the single-alpha
restriction calculation and ordinary compositor coherence as elementary prose; they
are now stated separately with explicit Lean interfaces. The displayed theorem already
assumes the open, quasi-compact and proper
properties of the changed square, so separate proofs of their preservation under
base change are also unnecessary. No statement is disputed.

## New nodes

`lem-sf-semilinear-alpha-restriction` records the restriction normalization from
step 4 of the original proof, including the prescribed square comparison and both
open units. Its source and full proof in words appear in its module docstring and
DAG node.

`lem-sf-semilinear-pullback-cube-coherence` records the compositor calculation from
step 5 of the original proof. It drops all geometric properties and isolates the
ordinary inverse-image coherence needed after applying the restriction formulas.
Its source and full proof in words appear in its module docstring and DAG node.

No definitions or existing signatures were changed. The conservative interface checker
requires a record for added module commands: see
`coord/changes/R7-semilinear-alpha-proof-commands.md`. The additive helper is a proved
private theorem registered only as a local instance.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
