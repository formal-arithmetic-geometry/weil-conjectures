## What changed

Replaced the hole in `WeilConjectures.sf_clopen_derived_compatibility` by a reduction
into scalar/quotient comparison, derived-completeness preservation, and objectwise
residue Tor preservation. Its original signature and all public imports are unchanged.
Only the assigned module, its node, and three new theorem modules/nodes are included.

Server validation: `lcompile.py --all` compiled all four modules successfully. The
assigned module took 27.9 seconds; the new modules took 13.0, 13.2 and 16.1 seconds.
Every file is below the unchanged 60-second limit.

The assigned proof constructs its tower comparison from the actual chain quotient
isomorphisms. Localization-factorization naturality proves the consecutive-arrow
squares; `NatTrans.ofOpSequence` supplies naturality for every arrow, and
`NatIso.ofComponents` gives the isomorphism with the required components. The chain
unit and transition equations are checked on sheafified pure tensors, using the
published unit/transition formulas and `d.transition`. The chain unit equation then
proves the prescribed derived augmented unit square. No tower comparison is assumed
as a new intermediate obligation.

The proof imports the three new modules privately. It also uses a private proof import
of `IntegralReductionTowerUnrestricted` to access its existing proved pure-tensor
extensionality lemma; that source module is unchanged.

## Proved and sorry left

This is a decomposition, not an unconditional proof or a net decrease in holes.

Closed the original body of `WeilConjectures.sf_clopen_derived_compatibility` (one of
one original holes) by a complete proof from the intermediate statements. The local
localization-naturality and transition-formula helpers are proved.

Three holes are added, one in each new module:

- `WeilConjectures.sf_clopen_scalar_quotient_comparison`
  (`lem-sf-clopen-scalar-quotient-comparison`): normalized scalar and actual chain
  quotient comparisons, including the universal-counit square for arbitrary complexes.
- `WeilConjectures.sf_clopen_preserves_completeness`
  (`lem-sf-clopen-preserves-completeness`): preservation of the published canonically
  augmented Roos completeness predicate.
- `WeilConjectures.sf_clopen_preserves_residue_tor`
  (`lem-sf-clopen-preserves-residue-tor`): preservation of the identical residue Tor
  interval on every component site object.

The assigned module contains no remaining `sorry`. Each new hole is a public theorem
in its own module, has a source and full proof in words, and is a strict portion of
the original conclusion. No definition, instance, target, or shared interface changed.
The delivery has one original hole closed and three lower holes added (net -2).

## No longer needed

Removed the assigned module's direct proof import
`Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus`: the assembly now uses
the three narrower intermediate statements and Mathlib naturality/sequence APIs.

No mathematical node or module is claimed globally pruned. The old dependencies
`lem-pur-clopen-ringed-module-gluing`,
`lem-pur-finite-product-derived-tensor-calculus`,
`lem-weil-integral-reduction-tower-well-defined`,
`lem-weil-pbc-site-derived-tensor-descent`,
`lem-weil-proetale-weakly-etale-localization`, and `def-weil-derived-limit` remain
needed in the lower arguments and are retained in the corresponding new node plans.

## Where the brief, the DAG or earlier work was wrong

No false statement or required interface repair was found. The former single proof
paragraph hid several independently substantial tasks. In particular, the published
finite-clopen scalar calculus normalizes its counit comparison on K-flat flat-term
representatives; the assigned `reduction_counit` field quantifies over every complex.
The scalar comparison node records the additional universal-counit/naturality argument
instead of treating those signatures as identical.

Edge cases were checked against the definitions: exponent zero is the positive
exponent one, the coefficient isomorphisms preserve 1, the empty component is a zero
module category, and the Tor predicate includes the ordered-interval conjunct. Thus
when a>b its global objectwise premise is impossible. No nonempty-component, affine,
lisse, weak-contractibility, or invertibility hypothesis was added.

The unit record `sk-rem-sf-pf-done` has no realized statement/steps to bypass; its route
and every source-library declaration are preserved. Blueprint searches for clopen and
completeness found no duplicate of the new normalized interfaces. LeanSearch and
LeanFinder returned structure-sheaf restriction APIs rather than these arbitrary
coefficient assertions. Loogle lacked the sequence constructor in its index; source
search found it and the exact localization-naturality API, used in the proof.

## New nodes

`lem-sf-clopen-scalar-quotient-comparison` states the scalar/chain comparison portion
of the assigned source proof, with its pure-tensor and all-complex counit normalization.

`lem-sf-clopen-preserves-completeness` states the Roos portion: restriction preserves
K-flat representatives and products, and carries the canonically augmented triangle
to the local one under the normalized quotient comparison.

`lem-sf-clopen-preserves-residue-tor` states the relocalization portion: identify the
two slices at the same site object and transport every degree-zero tensor test and
its zero cohomology, with the same ordered bounds.

All new nodes inherit the assigned chapter, unit and blueprint ancestry. There are
no change records because no other existing declaration or node is changed.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
