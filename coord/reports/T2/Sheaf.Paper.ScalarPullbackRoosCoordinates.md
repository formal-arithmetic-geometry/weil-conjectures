## What changed

Prove `WeilConjectures.ScalarExtensionTower.scalarPullbackRoosCoordinates_exists`
without changing its statement. Reconstruct the ordinary quotient presentation
from whole-system coherence. Associate completed scalar extension with finite
reduction by uniqueness of normalized ordinary tensor adjoints. Its unit equation
and the ordinary quotient unit transition give successor compatibility; the
existing strict-system gluing lemma then supplies a chain isomorphism. Apply the
ordinary quotient pullback comparison and calculate its value on the prescribed
nested unit section.

The new module `Sheaf.Paper.ScalarOrdinaryPresentationCoordinates` proves the
scalar-only comparison, with private proved construction helpers. The item imports
it only for its proof. No public signature in an existing module changes.
Existing public definitions, declarations, and imports are preserved.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.ScalarExtensionTower.scalarPullbackRoosCoordinates_exists`
(node `stage3-pur-scalar-pullback-roos-coordinates`). Zero `sorry` statements
remain in either delivered module; zero holes were added.
`scalarPullbackQuotient_computes` retains its existing proof.

The initial complete file compiled in 48.8 seconds, but the delivery compile took
70.5 seconds. After local irreducibility improvements and profiling (which showed
costs spread across adjoint association, section casts, kernel checking and linting),
the self-contained scalar construction was moved to a fully proved module. No
profiling options or temporary scratch modules remain in the packet.
The two final files compile through `lcompile.py --all` in import order:
`ScalarOrdinaryPresentationCoordinates` in 53.1 seconds and
`ScalarPullbackRoosCoordinates` in 19.4 seconds.

## No longer needed

No existing import is removed. The node
`lem-trf-ordinary-quotient-scalar-tower-comparison` and module
`Sheaf.Paper.OrdinaryQuotientScalarTowerComparison` are not needed by this proof.
The proof uses the finite comparisons and strict
successor gluing underlying `ordinaryQuotientScalarTowerComparison`, rather than
its restricted completed-coefficient tower statement: the intermediate strict
sequence is needed before applying sequence pullback. No parent or unit route is
withdrawn.

## Where the brief, the DAG or earlier work was wrong

The listed scalar tower comparison alone ends at direct finite scalar extension;
the pullback comparison starts from a quotient presentation over completed L.
The completed-L finite tensor associator and its compatibility with successors
are the required link. They are constructed and proved in this delivery, rather
than postulated as a new obligation.

The stale `ScalarPullbackQuotientFormula` entry in this node's declaration list
is removed: its existing separate module and node remain unchanged.

The unit record `sk-def-purity-conv` has empty realized statements and steps. Its
recorded `_section.md` path is absent from the current blueprint snapshot; no unit
statement or proof route has been bypassed.

## New nodes

`lem-trf-scalar-ordinary-presentation-coordinates`
(`Sheaf.Paper.ScalarOrdinaryPresentationCoordinates`): fully proved scalar-only
strict quotient presentation association, including successor compatibility and
tensor-unit coordinates. This separates compilation; it introduces zero holes.
The item supplies the independent pullback step and combines the two formulas.

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 5 INFRA.

```json
{"capped": false, "direct": 5, "left_out": 0, "own": {"Sheaf.Paper.ScalarOrdinaryPresentationCoordinates": "f7720d5ea574edd1e4b21fe22d7c567ccba27de9", "Sheaf.Paper.ScalarPullbackRoosCoordinates": "84913ad0c9c76b76fb577627b9f65900a31b906d"}, "results": {"Sheaf.Paper.ScalarPullbackLeftRoos": {"hash": "79711afd3ab5cc39b3c6872fd3792cf84939fd9f", "status": "INFRA"}, "Sheaf.Paper.ScalarPullbackQuotientExt": {"hash": "378e5578f51af965fe6742c3c9bdca41662b564a", "status": "INFRA"}, "Sheaf.Paper.ScalarPullbackRightRoos": {"hash": "610f65e364601c161baf6a78426ea5699d2491a5", "status": "INFRA"}, "Sheaf.Paper.ScalarPullbackRightRoosNormalization": {"hash": "fec53bdfd6a71886ed35109c3432801feec3b77c", "status": "INFRA"}, "Sheaf.Paper.ScalarPullbackRoosCoordinateSystem": {"hash": "c6748187a2781ce968904104aa16cca612203892", "status": "INFRA"}}, "seconds": 83, "time": "2026-10-28T10:55:28+0800", "transitive": 0, "version": 1}
```

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
