## What changed

Replaced the sole proof hole in
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.quotient_koszul_unit_comparison`
by composition of a finite strict-tower quasi-isomorphism and the normalized actual
Roos comparison. The statement, all hypotheses, universes, and public imports stay
unchanged. The assembly applies the inverse-limit functor to the quasi-isomorphism,
uses `D.tensorFactors`, and proves the unit equation by naturality of `D.comparison`
and the ordinary-limit unit equation, followed by cancellation of the comparison
isomorphism.

`InternalQuotientTowerModel` explicitly constructs the ordinary exact transport,
its canonical localization isomorphism, the transported actual positive quotient
tower, the compatible actual quotient units, the transposed complex of towers,
and its ordinary-limit unit. The latter uses the proved generic
`strictTowerLimitUnit` construction, so its chain-map calculation is checked
once for an abstract module category. No definition chooses an arbitrary witness from an
unproved existence statement. The quotient successor identity reuses the existing
proved calculation from `DerivedCompletion` through a private proof import.

`InternalKoszulQuotientResolution` and `InternalQuotientRoosLimit` state two
separate steps of the original four-step plan. The first is a quasi-isomorphism
of complexes of towers, before any derived inverse limit. The second has no
Koszul complex, generator, regularity, K-flatness, or completeness assumption.
Neither restates the assigned theorem. Their complete natural-language proofs
are in their docstrings and matching new nodes.

The localization unit calculations `FlatScalarKoszul.unit_app_Q` and
`FlatScalarKoszul.unit_naturality` are reused through a private proof import.
They are proved helpers, not the scalar-comparison theorem in that module.

## Proved and sorry left

Original holes: 1. Closed in the assigned module:
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.quotient_koszul_unit_comparison`
(node `lem-sfb-internal-quotient-koszul-unit-comparison`).

Added holes: 2, both in new public theorem declarations:

- `AlgebraicGeometry.ProEtale.InternalCompletionTransport.koszul_quotient_resolution`
  (node `lem-sfb-internal-koszul-quotient-resolution`).
- `AlgebraicGeometry.ProEtale.InternalCompletionTransport.quotient_roos_limit`
  (node `lem-sfb-internal-quotient-roos-limit`).

This is a decomposition, not a net proof gain: one upper hole is replaced by two
strictly smaller, independent mathematical steps. There are zero holes in the
new tower definitions and zero remaining holes in the assigned module. No
upstream declaration or theorem statement was changed.

## No longer needed

No original public import is removed, and no module is withdrawn. The original
proof dependencies `def-sfb-integral-constant-model-realization`,
`det-prop-sfb-qlbar-colimit-x-integral-limit`, and
`det-prop-integral-criterion-constant-coefficients` are no longer direct proof
steps of the assigned theorem; their coefficient calculations remain needed by
`lem-sfb-internal-koszul-quotient-resolution`. They are not globally pruned.

The assigned theorem now directly uses the two new theorem nodes, the explicit
tower-model node, and `def-weil-pbc-ringed-koszul-system`. No existing mathematical
node has been shown unnecessary globally. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The previous session's missing-source blocker has been resolved in the current
shared source and private compile overlay: both the assigned module and
`InternalCompletionSectionTransport` are available. The unchanged original
assigned module compiled successfully before proof work.

The stated proof dependencies supply coefficient identifications and definitions,
but no existing declaration found states the required strict finite resolution
or its augmented actual Roos computation. Searches included the existing regular
principal completion, strict scalar Koszul, constant completion, and strict Roos
APIs. Their objects differ from the actual internal-module quotient tower here.
The new statements isolate those precise bridges rather than restating the
completion comparison under another name.

Edge cases checked mathematically: P zero, X empty, arbitrary unbounded K-flat P,
and a replaced locally by a unit times a uniformizer. The finite resolution
uses regularity of the uniformizer; it makes no false assertion for arbitrary
zero-divisor generators. The Roos lemma requires neither regularity nor K-flatness.

Sources read: the current blueprint integral-models proof (1), Stacks
`proetale.tex`, section derived-completion-noetherian and lemma naive-completion
(099L, 099M); `sites-cohomology.tex`, lemma derived-limit-is-ok (0941);
`algebraization.tex`, lemmas derived-completion-koszul (0A0E) and
restriction-derived-complete-equivalence. The new nodes record all three kinds
of Mathlib search. A full dependency traversal encounters the pre-existing
`lem-pc-ring-hom-extension-differential` /
`lem-pc-ring-hom-extension-differential-adjacent` cycle below the adopted
coefficient realization; none of the new dependency edges introduces a cycle. No target statement or unit record changes.

## New nodes

`def-sfb-internal-quotient-tower-model` records the explicit ordinary transport,
canonical localization factorization, actual strict quotient tower and unit.
Its declarations are in `InternalQuotientTowerModel`.

`lem-sfb-internal-koszul-quotient-resolution` records the finite regular singleton
resolution and strict augmentation compatibility in
`InternalKoszulQuotientResolution`.

`lem-sfb-internal-quotient-roos-limit` records the generator-independent normalized
actual Roos calculation in `InternalQuotientRoosLimit`.

The categorical assembly was independently compiled in an abstract ringed-site
check. All three new modules have also compiled individually; the final packet
validation is performed by the required delivery command. The optimized tower
model compiled in 48.9 seconds; the two lower statements compiled in 29.8 and
28.2 seconds. The local instance names are distinct across the new modules.

No change record is required: no existing statement or definition changes.
The generic strict Roos and additive cone lemmas are used as tools in the new
nodes' proof plans; no maintainer tool approvals are added by this delivery.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
