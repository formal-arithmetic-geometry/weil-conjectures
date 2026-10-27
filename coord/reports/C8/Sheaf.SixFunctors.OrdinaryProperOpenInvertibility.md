## What changed

Proved `AlgebraicGeometry.ProEtale.ordinaryProperOpenMateIsIso` in
`Sheaf.SixFunctors.OrdinaryProperOpenInvertibility`, preserving its statement and
public import. All new helpers are private and proved.

The proof transfers the existing general-square supported-counit theorem from
intrinsic ringed-site modules to constant-module sheaves. A ring equivalence with
the lift of its finite shrink handles the coefficient-universe difference.
Equivalences preserve membership in the essential image of open extension, so the
actual target counit is invertible without equating different chosen adjunctions.

For the specified mate, the proof specializes the existing generic categorical
clopen calculation. Its open adjunct is inverse to an explicit isomorphism made
from beta, the clopen comparison, open composition, and the adjunction conjugate
of pullback composition. The inverse Hom equivalence expresses the mate as open
extension of this inverse followed by the supported counit.

Added proof-only imports of `SemilinearProperOpenCore`,
`ProperOpenSquareDerivedSupport`, `SfIntrinsicRealizationTransport`, the sheaf
coefficient-whiskering and inverse-mate-equivalence APIs, and Mathlib ring shrinking.
Updated only the item's DAG proof, proof dependencies, and proof origin. The
intrinsic realization node `def-sp-finite-intrinsic-direct-adjunction` supplies
coefficient-presentation comparisons as a tool; no unit route is bypassed.

The full module compiled without warnings in 28.3 seconds using `lcompile.py`.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.ProEtale.ordinaryProperOpenMateIsIso`
(node `lem-sf-ordinary-proper-open-invertibility`). Added 0 holes; split off 0
statements. No `sorry` remains in the delivered module.

## No longer needed

No imports removed and no modules globally pruned. Replaced the direct DAG
proof dependency `lem-sp-proper-open-derived-support` with its existing
general-square extension `lem-sf-proper-open-square-derived-support`. The triangle
support theorem remains needed transitively by that existing extension; this is
not a claim to prune its module. No comparison with a separately chosen proper
pushforward compositor is needed: use the adjunction conjugate itself.

## Where the brief, the DAG or earlier work was wrong

The old support dependency states the triangle case with identical sources for
the two opens. The existing square-support theorem supplies the required statement
for distinct sources. Its ring is in universe u and its categories are intrinsic
constant-ring modules, whereas this item's ring is in universe u+1 and its
categories are sheaves valued in ModuleCat. The proof explicitly transports
between these presentations, including the finite shrink; neither mismatch is
silently discharged by definitional equality. Empty opens and the zero ring need
no additional hypothesis: the same equivalences and fully faithful adjunction
identities apply.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.OrdinaryProperOpenInvertibility": "b43b2710e06b84f36e203bfd554db347b1d7bf14"}, "results": {"Sheaf.SixFunctors.CompositionProjectionMate": {"hash": "3025b4f3cfaecb055e9227e17561cc973271644e", "status": "OK"}}, "seconds": 69, "time": "2026-10-28T06:28:36+0800", "transitive": 0, "version": 1}
```

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
