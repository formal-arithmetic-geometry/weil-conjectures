## What changed

Replaced the sole sorry of
`AlgebraicGeometry.ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude`
with a complete proof assembly of the prescribed etale-origin, Tor-reflection, etale
direct-image, and comparison-back argument. The existing theorem signature and public
imports are unchanged. All added imports are private proof dependencies.

The proof uses `finiteRing_constructibleDerived_origin` directly in the intrinsic
constant-ring presentation, avoiding an additional coefficient encoding. It checks
invertibility of the coefficient prime in residue fields by the finite-field
characteristic and the structure morphisms. It combines the canonical bounded-below
comparison with the unbounded compatibility and realization/direct-image isomorphisms,
then transfers intrinsic constructibility and the exact Tor interval.

Validation: the delivered module compiled cleanly through lcompile.py in 7.8 seconds on resumption,
with no errors or warnings. The existing theorem signature was also compared verbatim
with the library version and is unchanged. Every Lean line is at most 100 characters.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude`
(node `cor-sf-direct-image-ctf-proetale`). Zero sorry tokens remain in the item module;
zero holes were added and zero new lemmas were split off. Existing dependency theorems
remain unchanged, including the stated etale direct-image and Tor-reflection inputs.
The proof is complete from those declarations, as required by stage 3.

## No longer needed

Removed private imports `Sheaf.Paper.ProEtaleConstructibleOrigin`,
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`Mathlib.AlgebraicGeometry.Morphisms.Immersion`, and
`Sheaf.Paper.FiniteTorAmplitudeSites`.

The node `lem-sf-proetale-constructible-origin` is replaced by the already stated
`lem-weil-pbc-finite-ring-constructible-derived-origin`: both realize the unit's derived
etale-origin step, and the latter already uses exactly the required intrinsic coefficient
presentation. The node `lem-weil-pbc-proper-fp-permanence` is unnecessary because the
Mathlib separated-to-quasi-separated instance gives the comparison hypothesis directly.
Their old top-level tool-use approvals are removed from the node copy, preserving the
order of the remaining entries. These are local dependency removals, not claims that
these modules have no other target consumers. The etale direct-image, Tor-comparison,
and comparison-direct-image route of the unit is retained.

## Where the brief, the DAG or earlier work was wrong

The directImageCTFNonproper interface now takes structure morphisms and compatibility
through Over/IsOver instances; no explicit f.comm argument is accepted by its current
source. The proof uses that interface, with explicit local finite-type and quasi-compact
instances converting the bundled structure morphisms to the Over notation. The old
proper-diagonal detour is mathematically valid but unnecessary with the existing Mathlib instance. No statement,
definition, target, or consumer has been changed. There are no new nodes or forced
adaptations.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
