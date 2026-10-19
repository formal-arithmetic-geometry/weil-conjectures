## What changed

Proved `AlgebraicGeometry.exists_sf_affine_chart_factorization_gluing` with its
original signature. Private proved helpers construct finite affine covers, factor each
finite-type affine morphism through affine space, and glue cohomological and Tor intervals.
The empty scheme case is handled separately and takes no extrema of an empty set.

The geometric factorization uses Mathlib's finite polynomial presentation and affine-space
spectrum isomorphism. Constructibility uses the existing Noetherian open-cover theorem,
after identifying finite-constant-value constructibility with the source notion. Finite
type over the field supplies Noetherianness. Cohomology vanishing uses the source's
jointly-surjective conservativity theorem. Tensor gluing uses the canonical derived
pullback tensor comparison and its compatibility with degree-zero sheaves.

## Proved and sorry left

Closed the one assigned hole:
`AlgebraicGeometry.exists_sf_affine_chart_factorization_gluing`
(node `lem-sf-affine-chart-factorization-gluing`). No holes added; zero direct sorries
remain in the delivered module. All private helpers have complete proofs. The theorem
still uses any unproved dependencies of the existing library declarations it invokes.

## No longer needed

Removed proof imports:

- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal`
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`

The node no longer needs `lem-weil-pbc-etale-inverse-image-restriction`,
`lem-weil-pbc-constructible-qcqs-affine-local`, `lem-weil-pbc-etale-composition-cancellation`,
`lem-weil-pbc-qcqs-over-affine`, or `lem-weil-pbc-affine-scheme-qcqs` as proof dependencies.
The first three obsolete top-level tool-use approvals are withdrawn. The exactness of
upperStar and affine morphism instances are still supplied by source/Mathlib imports;
`prop-weil-pbc-inverse-image-modules-exact` remains recorded for that mathematical fact,
although its longer dictionary theorem is unused. No public statement import is removed. The last four removed imports are redundant
statement wrappers: the unchanged public imports already supply every declaration needed
by the signature, including bounded constructibility, bounded Tor amplitude and derived
categories. Their corresponding definition nodes remain in the DAG because the proof
still uses those notions.

The source's general conservativity theorem replaces the explicit restriction comparison.
Noetherian constructibility locality replaces the qcqs affine-local bridge and its scheme
hypotheses. This pruning concerns this proof; the delivery does not claim that every such
module leaves the targets' entire import closure.

## Where the brief, the DAG or earlier work was wrong

The planned qcqs constructibility argument is unnecessary in the stated finite-type-over-a-field
setting: schemes are Noetherian, so the existing source open-cover constructibility theorem
applies after the existing comparison of the two constructibility notions. The unit's affine
factorization and finite-cover gluing route is retained. No statement or definition was changed.

## New nodes

`lem-sf-noetherian-constructible-open-local` records the existing proved source theorem
`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_iSup_eq_top` in
`WeilConjectures.ConstructibleSheaf.OpenCover`. It adds no Lean declaration and no hole.
The node is the generic Noetherian open-cover locality tool used in the finite-type
setting, sourced to Stacks 095E/095F and the source's finite-cover induction.
LeanSearch and LeanFinder found only topological locality statements in Mathlib;
source grep found this exact existing theorem. The change record
`coord/changes/V3-sf-affine-chart-proof-scope.md` documents the added
`open scoped ZeroObject` command, which the interface checker conservatively flags;
no public definition or statement changed.

Validation on resuming the sandbox (2026-10-19): `lcompile.py` compiled the retained
module against the current server library with exit code 0 in 15.7 seconds on the latest retry. The existing
theorem signature is unchanged (verified after whitespace normalization). All private
helpers remain fully proved, and the module contains no direct `sorry`. The proof docstring
was updated to describe the implemented Noetherian locality and conservativity argument.
The initial dry run compiled the module and reported two metadata issues: the
existing-declaration node must omit `lean.file`, and the added scope command needs a
change record. Both have been repaired before the next dry run.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
