## What changed

Filled `AlgebraicGeometry.Scheme.finitePerfectAdic_coordinate_transition_maps` with
its original statement unchanged. At each consecutive level, scalar extension of
the larger actual quotient coordinates is isomorphic to the smaller coordinates.
Conjugate this isomorphism by the supplied comparisons and lift its hom using the
bounded-below comparison Hom bijection. Exact comparison reflects its being an
isomorphism by homology. The scalar-adjunction unit composed with the restriction
of this isomorphism is universal; the existing etale-source universality theorem
then supplies every required pullback. Choice assembles these arrows over all n.

Added the fully proved module `Sheaf.Paper.FinitePerfectAdicCoordinateScalarExtension`.
It proves quotient balancing under the exact constant-scalar coordinate equivalences,
then transports it to the chart using the scalar-pullback mate. Its private helpers
compute the latter from the earlier ordinary adjunction and flat-resolution APIs;
there is no import of the downstream local-systems theorem. The proof includes the
identity-on-sections scalar square, rather than postulating a compatible square.

Removed the unused public import of `Sheaf.Paper.FinitePerfectAdicScalarCoherence`
from the item. Added private proof imports for the new helper, WitnessCompatibility,
EtaleSourceNormalizationUniversal, derived comparison and the comma-adjunction API.
The sole direct consumer already imports ScalarCoherence itself; it is checked
unchanged against this delivery, then excluded from the packet.

Validation: a single import-order compile checked the helper (28.7 seconds), the
item (6.1 seconds), and its unchanged sole direct consumer
`Sheaf.Paper.FinitePerfectAdicCoordinateTransitions` (7.0 seconds), without warnings.
The unchanged consumer copy was then removed from the sandbox. Both delivered
modules have no sorry and no lines over 100 characters.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.finitePerfectAdic_coordinate_transition_maps`
(node `new-w5-finite-perfect-adic-coordinate-transition-maps`).

Also proved the new theorem
`AlgebraicGeometry.Scheme.finitePerfectAdic_coordinate_scalar_extension`
(node `new-g3-finite-perfect-adic-coordinate-scalar-extension`), and all private
helpers in its module. Holes closed: 1. Holes added: 0. Split-off holes: 0.
No sorry remains in either delivered module. This is a proof from existing declared
APIs, including the existing etale-source universality statement, not a claim that
all transitive dependencies are already axiom-free.

## No longer needed

Removed the item's direct public import of
`Sheaf.Paper.FinitePerfectAdicScalarCoherence`; no scalar-realization coherence is
used by this transition-existence and universality statement.

The proof does not import or use
`Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems`
(node `lem-weil-pbc-derived-scalar-extension-local-systems`). Its import would be
cyclic because that module already depends on this item. Instead the proof descends
an isomorphism between scalar extensions and uses the earlier
`Sheaf.Paper.EtaleSourceNormalizationUniversal` statement for source pullback.

The proof also does not import the planned general tensor-pullback module
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
(node `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`). The fixed-coefficient
flat-mate computation and exact coordinate equivalences suffice. Both unused planned
proof dependencies are removed from the item's proof/proof_deps. Existing statement
metadata is preserved. No whole module or upstream declaration is withdrawn; other
consumers may still need those interfaces. The blueprint unit and its realized route
are preserved.

## Where the brief, the DAG or earlier work was wrong

The suggested derived-local-systems interface is downstream of the item, so following
that import plan literally creates a cycle. The needed special case is obtained
without that import from the earlier scalar adjunction and flat-resolution APIs.
There was no defect in the theorem's Lean statement. The proof works for unbounded M,
empty charts and zero rings; only the supplied K_n targets need boundedness in the
comparison Hom bijection. No flatness of a quotient homomorphism is assumed.

## New nodes

`new-g3-finite-perfect-adic-coordinate-scalar-extension` records the proved balancing
isomorphism for the actual finite quotient coordinates, before any etale origins
are supplied. Its proof composes the invertible mate for the coefficient encoding
equivalences with quotient-reduction normalization, then the invertible chart mate.
It has a new fully proved module and adds no hole. The item's node proof and proof
dependencies are updated to match the Lean proof.

Change record: `coord/changes/G3-finite-perfect-transition-scalar-coherence-import.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicCoordinateScalarExtension": "dcab5552cb1c34029e35b72bdaf0c3ea11dbbe09", "Sheaf.Paper.FinitePerfectAdicCoordinateTransitionMaps": "a2833fe8d2618304cf276a2a9ca6688bd8e1b23f"}, "results": {"Sheaf.Paper.FinitePerfectAdicCoordinateTransitions": {"hash": "d9fa0c59926aca9846475834931b5302e3b5fd15", "status": "OK"}}, "seconds": 133, "time": "2026-10-28T10:34:28+0800", "transitive": 0, "version": 1}
```

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
