## What changed

Proved `AlgebraicGeometry.ProEtale.finiteCtfRetractEtaleImages` with its exact existing
signature. Added only proved private helpers for resizing constructibility covers,
converting boundedness conventions, choosing an etale model from bounded descent,
splitting an idempotent through its canonical image, and lifting the cohomology projector.
The normalized encoding and its actual termwise derived functor are used throughout.
No definition, public statement, source-library file, or consumer was changed.

The route uses the existing fixed-module bounded constructible origin theorem and source
Tor comparison, avoiding coefficient-model changes of site. The image splitting directly
constructs the required isomorphism; no unbounded descent of the retract is used.
The item node records this route. The first compile reported local namespace and proof-glue issues in 6.5 seconds; these
were repaired. The revised proof compiled in 20.3 seconds with zero errors. Its single unused simp
argument was removed before delivery. The delivery reruns compilation and the required
preflight checks. Static checks confirm zero sorry occurrences, no line over 100 characters,
and the same public theorem signature (the original generic Tor names are explicitly
qualified to avoid a namespace collision from proof imports).

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.finiteCtfRetractEtaleImages`
(node `lem-sfb-finite-ctf-retract-etale-images`).
No holes remain in the item; no holes or split-off statements were added.
`finiteCtfComparisonHomologyIso` is unchanged.

## No longer needed

The proof does not use `det-pe-finite-tor-comparison-noetherian`
(`Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`): finite-coefficient
fixed-module bounded descent and the source fixed-module Tor comparison provide precisely
the model required by the statement, without passing through coefficient site models.

It does not use `sk-thm-pe-constructible-comparison`
(`Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`): use the already proved
fixed-module constructible sheaf origin/preservation theorem instead.

It does not use `lem-weil-pbc-constructible-qcqs-affine-local`
(`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal`): the ordinary encoding
and the source fixed-module convention already use a global finite stratification on qcqs
schemes, and only the covering index requires resizing. The existing finite-value/source
constructibility comparison handles the etale convention directly.

It does not use `lem-sp-exact-functor-preserves-homology` for preservation of images:
functors preserve the explicit splitting equations, which directly give the isomorphism
with the pulled-back image. The exact derived homology comparison remains in use.
Removed these private proof imports: `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`,
`Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`,
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal`, and
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`. Also removed the redundant private
imports `Sheaf.Paper.ComparisonPullbackExact` and
`Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`: the existing source comparison
API already provides the exactness and full-faithfulness instances used here. Every original
public import is preserved.

Removed the corresponding obsolete top-level tool approvals from the item node, retaining
the other approvals in their existing order. No modules are withdrawn, and no assertion
is made that other consumers no longer need these modules.

## Where the brief, the DAG or earlier work was wrong

The proposed general Noetherian comparison is expressed in coefficient-sized site models,
whereas this item's conclusion uses fixed-scalar sheaves. The existing fixed-module source
results avoid that presentation bridge. The general constructible comparison and affine-local
equivalence are likewise unnecessary once using the source finite global stratification.

The explicit image of an idempotent is already a retract, so the existing proved
`Scheme.IsConstructibleSheaf.of_retract` applies directly; no new kernel construction or
image-preservation theorem is needed. All changes are below the unit route: the unit's
realized arrays are empty, and its finite-coefficient thickness argument is preserved.

Edge cases checked in the proof: zero coefficients, the empty scheme, zero/identity
idempotents, the zero retract, and degenerate Tor intervals require no exclusions.
The given ring is finite, so its universe lift is Noetherian for constructible retracts.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
