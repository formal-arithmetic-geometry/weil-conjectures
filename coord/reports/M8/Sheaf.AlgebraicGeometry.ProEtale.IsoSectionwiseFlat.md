## What changed

Proved `AlgebraicGeometry.Scheme.isoSectionwiseModuleInverseImage_preservesFlat`
in `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseFlat`, preserving its entire
signature. Added a private proved cocontinuity helper and proof imports of
`FlatEquationalCriterionOfUniverses` and Mathlib `Sites.CoverPreserving`.

The proof uses the already proved independent-universe local equational criterion
(Stacks Modules on Sites, Tag 08FC, `lemma-flat-eq`). It transports finite relations
through the coefficient isomorphism, pulls the covering sieve back along the site
equivalence, and transports the factorization matrices back. Naturality and the
inverse identities give the coefficient equations. This is the sectionwise case
of Tag 05VD, `lemma-pullback-flat`; no new intermediate statements are required.
The argument admits empty coefficient families and the zero ring.

Validation: the final module compiled cleanly through `lcompile.py` in 6.3 seconds.
The theorem signature and public imports match the original verbatim.

Updated the item's DAG proof, proof dependencies and proof origin to match this route.
The existing unit record has no realized statement or steps to bypass. The local
criterion is a general tool, already proved, from another unit; it replaces the
longer tensor-comparison argument, not the unit's mathematical route.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.isoSectionwiseModuleInverseImage_preservesFlat`
(node `lem-pod-sectionwise-flat-kflat-flat`). Added 0 holes; 0 split off.
No `sorry` remains in the item or is added elsewhere.

## No longer needed

No existing imports removed and no DAG nodes or modules withdrawn. The planned
inverse module functor and sheafified tensor comparison are unnecessary for this
proof; neither had a separate stated dependency to prune. The existing site
equivalence and flatness definition remain used. No source-library files changed.

## Where the brief, the DAG or earlier work was wrong

The original tensor-comparison plan is mathematically valid but longer than needed:
the already proved local equational criterion proves this sectionwise case directly.
The current server queue marks the item as a proof item, with no rework or build-error
record for this module. No statement or definition repair was necessary.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
