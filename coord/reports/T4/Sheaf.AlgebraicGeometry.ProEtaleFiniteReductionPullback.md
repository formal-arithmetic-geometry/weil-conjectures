## What changed

Proved `AlgebraicGeometry.ProEtale.sfb_finite_reduction_pullback` in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback`, with its statement and the
public coefficient-comparison definitions unchanged. Private proved helpers establish
constant-unit compatibility, extend it through locally surjective sheafification, and
compute the point-comparison mate using the existing compositor coherence theorem.
The point-unit identity is proved for abstract categories as a natural-transformation
identity and evaluated only after specialization. This avoids unfolding concrete
inverse-image constructions in Lean. The final argument compares the two given finite
labels and cancels the representation and composite adjunction. The node's proof and
proof dependencies now describe this route.

The record `coord/changes/T4-proetale-finite-reduction-proof-context.md` documents
the added local proof-context commands required by static preflight. These commands
change no public declaration or attribute of an existing public declaration as seen
by importers.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.sfb_finite_reduction_pullback`
(node `lem-sfb-finite-reduction-pullback`).

Original holes: 1. Holes left in the item: 0. Holes added: 0. Split off: 0.
All private helper theorems have complete proofs. No definition contains a hole.
The final module compiled through lcompile.py in 20.2 seconds with no warnings.
Its unchanged direct consumer,
`Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback`, then compiled in
24.4 seconds against the sandbox build. The temporary consumer source copy was
removed from the packet; no consumer adaptation is delivered.
The public definitions, theorem signature and public imports were compared verbatim
with the current shared source and are unchanged.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`.
- `Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`.
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback` (already publicly available).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` (already publicly available).
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` (already publicly available).

The proof no longer needs the declared proof dependencies
`det-pe-topos-functoriality-site`, `det-pe-topos-functoriality-inverse-image`, or
`lem-galois-yoneda-hom-bijection`. Local surjectivity replaces the proposed construction
of pullbacks of arbitrary representables. Terminality of the singleton test object
follows directly from existing finite-limit instances; the general
`Sheaf.Paper.ProfiniteTestObjectFunctor` theorem is not needed.

No module is withdrawn and no adopted source declaration is changed. The public
integral-limit import is preserved, so these removals claim only the unnecessary
steps and direct imports of this proof, not global unreachability of their modules.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was needed. The original representable/Yoneda
step was more general than required: constant labels and locally surjective
sheafification suffice. The point-compositor identity already exists in the source
library. The unit route and all target statements are preserved.

Worker-process incident: an early over-broad cleanup deleted the existing sandbox
files before this proof was restarted. The delivery files were reconstructed from
the shared sources; no shared repository file was written. Dispatcher budget/check
metadata was not reconstructed or edited afterward.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
