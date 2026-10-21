## What changed

Restored `Sheaf.SixFunctors.ClosedImmersionTensorProjection` from the quarantine path
listed in `coord/rework.tsv`. Repaired `supportTensorNatIso` using a proved private helper `comparisonNatIso` for
arbitrary bifunctors. The generic helper specializes the normalized two-variable
naturality equation and explicitly rewrites functor identities, natural transformation
identities, and composition with identities. The concrete support comparison is then
passed to this helper. Local transparency settings match those of the existing support
projection proofs and avoid repeatedly unfolding large sheaf-module instances. This
preserves the chosen normalized comparison rather than unfolding its construction
during simplification.

The theorem now obtains invertibility directly from
`openClosedSupportProjectionFormula`; its full internal-Hom consequence is unnecessary.
The node proof and proof dependencies follow this shorter route. The public signature,
universes, hypotheses, and conclusion of `closedImmersionTensorProjection` are unchanged.
The projection-map equality now uses the unit formula for `homEquiv` followed by
reflexivity, avoiding broad simplification of its concrete construction.
No source-library declarations or public imports were changed.

## Proved and sorry left

This is an assigned quarantine repair with zero textual holes in the archive.
Holes closed: 0. Holes added: 0. Holes remaining in the delivered module: 0.
The restored module compiles through `lcompile.py` in 34.3 seconds with exit code 0
and no warnings (2026-10-21).
`AlgebraicGeometry.ProEtale.CondensedRing.closedImmersionTensorProjection` retains its
complete proof from the existing normalized support projection and tensor comparison.
The private constructions `supportTensorNatIso` and `comparisonNatIso` are proved,
with no postponed data.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom` and
replaced it with `Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula`.
The node `lem-sfb-open-closed-internal-hom-formulas` is no longer a proof dependency of
this item: only invertibility of the closed tensor projection is used, already supplied
by `lem-sfb-condensed-support-projection-formula`. Other consumers may still need the
internal-Hom module; no module is withdrawn. All other archived imports remain used.
The existing tensor-comparison and exact-derived-factorization dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole quarantine repair, rather than a new sorry-filling obligation.
The archived broad `simpa [supportDerivedTensorComparison]` in `supportTensorNatIso`
failed after the tensor normalization interface refactor, as recorded at line 47 in the
rework row. The revised proof uses the same naturality statement with explicit identity
rewrites on the named functors, assembled first in a generic private helper. The archived route also imported a stronger internal-Hom theorem than
needed for this projection formula. No mathematical statement correction is required.
The quarantined parent `Sheaf.SixFunctors.IntTensorProjection` still uses this theorem;
restoration preserves that dependency and the existing Lean attachment.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
