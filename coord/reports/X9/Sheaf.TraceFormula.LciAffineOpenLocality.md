## What changed

Filled `AlgebraicGeometry.lci_affine_open_locality` in
`Sheaf.TraceFormula.LciAffineOpenLocality`, preserving its signature, docstring and imports.
The proof follows the existing DAG route: construct the open cover, descend local finite
type from its finite-type affine charts, apply the scheme part of
`AlgebraicGeometry.lci_pointwise_criterion`, obtain finite generation on the chosen affine
open using `Scheme.Hom.finiteType_appLE`, and apply the algebra part of the same criterion.
For each prime, `IsAffineOpen.isLocalization_stalk'` identifies the corresponding stalk
with its prime localization. The proof explicitly verifies compatibility of the induced
`k`-algebra structures using restriction of germs, then restricts scalars on the
localization equivalence and composes it with the complete-intersection presentation.

The supplied pointwise criterion is used as an existing dependency, as intended by
stage 3. The source passages read were Morphisms `lemma-local-complete-intersection`
(Tag 01UG) and Algebra `lemma-lci-global` (Tag 00SH). Searches through LeanFinder,
Loogle, the source library and Mathlib found the finite-type and affine-stalk APIs used
here. No replacement definition, interface change, auxiliary statement or new import
was needed.

Validation: the complete module compiled cleanly through `lcompile.py`
(exit code 0, 4.8 seconds of server compilation). All Lean lines are at most
100 characters, and the statement and existing documentation are byte-for-byte unchanged.

## Proved and sorry left

Closed the one hole in `AlgebraicGeometry.lci_affine_open_locality`
(node `lem-trf-lci-affine-open-locality`). Zero holes remain in the item; zero holes
were added and zero statements were split off. The existing dependency
`AlgebraicGeometry.lci_pointwise_criterion` remains outside this delivery unchanged.
Empty schemes and empty affine opens require no separate nonemptiness assumption:
the cover argument works for an empty index set and the algebra criterion quantifies
over primes, so its local condition is vacuous for a zero coordinate ring.

## No longer needed

None. All existing imports and declared proof dependencies are retained and used.
The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

None. The existing pointwise criterion and Mathlib declarations suffice to implement
the planned argument. No statement or definition repair was required.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
