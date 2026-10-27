## What changed

Proved both slice-instance obligations in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`.
Private, explicit constructions identify the etale slice over a scheme chart with that
scheme's small etale site. A pointwise covering-sieve criterion proves that this category
equivalence is an equivalence of sites. Mathlib's affine-etale sheafification and
locally-bijective results then transport to the slice, in the original section universe u.
The predicate and public signatures are unchanged. The three added imports are private
proof imports: `Mathlib.AlgebraicGeometry.Sites.AffineEtale`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale`.
The existing node's proof, proof dependencies and proof origin now record this argument.
Validation: `lcompile.py` compiled the complete module cleanly (exit 0, 14.2 seconds).

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.AlgebraicSpace.etaleModuleOverHasWeakSheafify`.
- `AlgebraicGeometry.AlgebraicSpace.etaleModuleOverWEqualsLocallyBijective`.

Both belong to `def-trf-space-quasi-coherent-module`. There are no remaining holes
in this module, no added holes and no split-off statements. These are proofs from the
existing declared library inputs, including `isEtale_comp` and
`representable_etale_scheme_tests`, whose proofs are still assigned downstream work.
The new private helpers all have complete proofs. All data in them are explicit
scheme constructions; no arbitrary object is extracted from an unproved existence result.
The site argument includes empty schemes and empty covering families: the pointwise
covering criterion is vacuous exactly when the underlying scheme has no points.

## No longer needed

None. Both original public imports remain necessary for the unchanged definitions.
The node originally had no proof dependencies; none are removed. No node or module is
withdrawn, and the unit route is preserved. Mathlib already constructs the small-universe
sheafification, so there is no need to add a new plus-construction obligation here.

## Where the brief, the DAG or earlier work was wrong

The original definition node had an empty proof despite its two slice-instance
obligations. This delivery records and implements the argument from their docstrings.
No mathematical statement was disputed or changed, and no consumer adaptation is needed.

The preflight requested a record for proof-context commands and private instances.
`coord/changes/R8-algebraic-space-slice-proof-context.md` documents these and all
33 downstream consumers; their mathematical interfaces require no adaptation.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
