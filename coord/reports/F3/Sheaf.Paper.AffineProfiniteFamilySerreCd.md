## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.affine_profinite_family_serreHeart_cohomology_vanishes`
without changing its signature, coefficient choices or public imports. Added two proved private
helpers in the item module: `AlgebraicGeometry.Scheme.field_strictLocalization_of_zeroDimensional`
and `AlgebraicGeometry.Scheme.torsionCd_of_affine_zeroDimensional`.

The first helper proves directly from the pointed-neighborhood colimit that every strict-local
ring of the reduced zero-dimensional base is a field. Each pointed affine etale neighborhood
has reduced dimension-zero coordinate ring; its localization at the pointing kernel is a field.
An element evaluating to zero is killed by an element outside that kernel, which becomes a
unit in the colimit. The strict-local field is separably closed through its residue-field
isomorphism. This works without identifying an imperfect separably closed field with its
algebraic closure.

The second helper uses field-extension dimension invariance, affine Artin vanishing, torsion
pullback, the strict-henselization stalk formula and geometric stalk conservativity. Leray
vanishing with base bound zero, obtained from affine closed separably closed point acyclicity,
gives the uniform torsion bound. Pullback pasting and etale dimension monotonicity provide the
same bound on all affine etale test schemes. The existing topological-coefficient transfer
then gives the exact stated conclusion. Empty schemes and empty fibres are included.

Updated the theorem's proof docstring and the item's DAG proof, proof dependencies and origin
to match this argument. No source-library declaration, target, definition or unit route changes.
The original w-contractibility hypothesis remains in the theorem's signature; this geometric
argument needs only the stated reduced zero-dimensional and separably closed residue conditions.

Validation: `lcompile.py` compiled the final item cleanly in 10.3 seconds, exit code zero,
with no warnings. Text checks confirm the original theorem signature and every public
import are identical, all lines satisfy the 100-character limit, and the item has zero
textual holes. The import-direction tool permits the three new central dependencies:
topological coefficient transfer, upstream affine Artin vanishing and upstream strict-local
stalk formula. The delivery preflight performs the required axiom probe.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.affine_profinite_family_serreHeart_cohomology_vanishes`
(node `lem-sfb-affine-profinite-family-serre-cd`). Both new private helpers are fully proved.
Zero textual sorry remain in the item, and zero holes are added anywhere. No split-off lemmas.

This is a proof from existing stated dependencies. In particular,
`AlgebraicGeometry.ProEtale.torsionCd_topological_serreHeart_cohomology_vanishes`
(node `lem-sfb-torsion-cd-topological-serre-transfer`) remains an existing imported obligation;
its full ordinary topological-coefficient source question is not solved by this delivery.

## No longer needed

Removed these private imports:

- `WeilConjectures.AlgebraicGeometry.EtaleFieldGsets`
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`
- `Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Sheaf.RingTheory.Etale.QuasiFiniteAtPrime`
- `WeilConjectures.RingTheory.Etale.LocalDimension`
- `Sheaf.AlgebraicGeometry.DimensionExtension`
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine`
- `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula`
- `Sheaf.AlgebraicGeometry.ExactGlobalSectionsLeray`

The direct colimit calculation avoids nodes `lem-exc-etale-field-gsets`,
`def-sc-ring-strict-henselization` and `lem-exc-affine-strict-local-ring-comparison`.
The proved source etale dimension inequality and finite-type instances avoid
`lem-weil-pbc-etale-ring-map-quasi-finite` and `lem-sc-etale-local-dimension`.
Field dimension invariance is reused from the closed upstream source attachment of
`lem-pc-dim-base-change`, so the combined field-extension/dense-open node
`lem-kun-dimension-extension` is unnecessary here. The source affine specialization includes
its separably closed field input and empty case, avoiding the two Sheaf wrapper imports.
Leray vanishing replaces `def-weil-pbc-exact-global-sections-leray`; no separately constructed
exact-sections instance is needed. The redundant direct Mathlib etale import is supplied by
the retained source geometry imports. The empty Sheaf stalk-formula module is replaced by
the actual upstream module.

The corresponding obsolete top-level tool-use entries were removed in their existing order.
These are dependencies pruned from this item's proof, not withdrawals of their declarations
or claims that no other part of the library needs them. No module is deleted.

## Where the brief, the DAG or earlier work was wrong

The DAG's step 1 suggests constructing a separate algebraic strict henselization and then
comparing it with the geometric construction. This is unnecessary: the existing upstream
pointed-neighborhood colimit API proves directly that its evaluation kernel is zero.
Steps 2 and 3 have already-proved source dimension and affine-vanishing specializations.
Step 5 can use the existing proved Leray vanishing theorem instead of building exactness
and then applying an exact-sections comparison. These are shorter realizations of the same
local geometric argument, below the unit level.

The recorded `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula` file is an empty
withdrawn twin; the declaration actually lives in
`WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula`. The proof imports the
actual defining module. The independent coefficient-transfer theorem remains needed.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
