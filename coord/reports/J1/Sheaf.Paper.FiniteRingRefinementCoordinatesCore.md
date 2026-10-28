## What changed

The statement of `finite_ring_refinement_coordinates_canonical` is unchanged.
Its witness is now the explicit `finiteFixedRefinementOpenIso`, constructed from
finite open and direct-image comparisons and the specified fixed proper/open map.
No data are selected from an unproved existence theorem.

The original existential conjunction is reduced to two separate assertions about
this witness: its open-adjunction normalization and its endpoint-coordinate equation.
The open assertion uses only `hi`; the endpoint assertion uses only `hg`.
Neither remaining statement is the original existential conjunction.

The finite scalar-map equality, ordinary section normalization, ordinary compositor
identity, derived compositor identity, and the single-endpoint open/direct-image
coordinate identity are proved. The ordinary transport is factored through an
explicit scalar-map transport definition, reducing its compile time below 60 seconds.
The coordinate definitions have explicit functor endpoints to keep instance search
from unfolding the derived functors.

Only the assigned existing Lean module is changed. All other Lean files are new.
No source-library file, existing interface, target signature, or public import changes.

Validation: `lcompile.py --all` compiled all eight files in import order.
The longest file took 49.7 seconds; the derived compositor took 27.5 seconds,
and the assigned theorem took 4.5 seconds. All files meet the 60-second limit.

## Proved and sorry left

The original module had one hole:
`WeilConjectures.ConstructibleExceptionalCoefficients.finite_ring_refinement_coordinates_canonical`.
Its new proof constructs the witness and combines its two separate clauses.

Two holes are added, each in its own new module, with proof exactly `by sorry`:

- `WeilConjectures.ConstructibleExceptionalCoefficients.finiteFixedRefinementOpenIso_normalization`
  in `Sheaf.Paper.FiniteRingFixedOpenNormalization`, node
  `lem-sf-finite-ring-fixed-open-normalization`.
- `WeilConjectures.ConstructibleExceptionalCoefficients.finiteFixedEndpointCancellation`
  in `Sheaf.Paper.FiniteRingEndpointCancellation`, node
  `lem-sf-finite-ring-endpoint-cancellation`.

This is a decomposition: one upper hole closed and two strictly smaller holes
added, net minus one. No original hole is claimed as an unconditional proof.
The endpoint statement has no existential witness, open-unit assertion or `hi`;
the open statement has no outer proper compositor, endpoint assertion or `hg`.

The new proved theorems are `finiteRingDirectImageMap_eq`,
`finiteTransportedOrdinaryCompositor_normalization`, `finiteOrdinaryPushComposition`,
`finiteFixedPushIso_composition`, and `finiteFixedEndpointModelAt`.
Every new definition is an actual construction with zero holes. Private helpers
are proved. There are no hidden or anonymous holes.

## No longer needed

No original node, module, declaration or public import is pruned. The original
three dependencies remain needed, directly or through the documented smaller
obligations. No unit realization is bypassed.

The attempted large normalization/congruence machinery is not delivered: its
whole-expression conversions repeatedly exceeded the compile limit. Its imports,
meta helpers, profiler options and diagnostic commands are absent from the final
assigned module. The final endpoint proof plan instead records the existing
normalization equations and the proved smaller coordinate APIs.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The finite scalar comparison closes
by the adjunction inverse equation. The ordinary compositor closes by the existing
proved section-action theorem and uniqueness; its derived coordinate square then
closes by the proved derived-adjunction normalization and intrinsic compositor APIs.

An attempted full endpoint proof reached the cancellation equation, but converting
its concrete derived-category terms to the original intrinsic-refinement expression
repeatedly exceeded 120 seconds. Alias normalization, explicit functor types,
abstract category lemmas and splitting the endpoint calculation were tried. This
conversion is not reported as proved. The remaining endpoint node gives the complete
mathematical cancellation argument and the names of the now-proved APIs it needs.
The narrower single-endpoint naturality equation is retained as a proved theorem.

Identity maps, empty opens and zero objects require only the same inverse-pair
and adjunction identities. No nonvanishing, nonemptiness, properness or coefficient
hypothesis was added to make a statement easier.

## New nodes

`def-sf-finite-ring-fixed-coordinates` records the sectionwise scalar direct image
and the four explicit finite fixed-coordinate constructions.

`lem-sf-finite-ring-scalar-map-equality` records the proved finite scalar-map equality.

`lem-sf-finite-ring-ordinary-compositor-normalization` records the generic scalar
transport, the two ordinary compositors, and their proved section action.

`lem-sf-finite-ring-ordinary-push-coordinates` records the proved ordinary compositor
identity obtained from uniqueness of the section action.

`lem-sf-finite-ring-fixed-push-composition` records the proved derived direct-image
compositor equation; it has no compactification, open immersion or witnessed origin.

`lem-sf-finite-ring-endpoint-pasting` records the proved single-endpoint equation
`finiteFixedEndpointModelAt`; it has no refinement or coefficient-composition premise.

`lem-sf-finite-ring-fixed-open-normalization` and
`lem-sf-finite-ring-endpoint-cancellation` record the two remaining assertions,
with their sources and complete proofs in words.

No change record is needed: no existing module besides the assigned item changes,
and its existing declaration signature and public imports are preserved.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteRingEndpointCancellation": "c7b80a47f1a73fbfbcdc216f551faa0c1ddd225a", "Sheaf.Paper.FiniteRingEndpointPasting": "c275bbb8efef149234ffb0ce873ad0590f752405", "Sheaf.Paper.FiniteRingFixedCoordinates": "d3e99a3e1b5cf479f61d5ee541047fc583cbf779", "Sheaf.Paper.FiniteRingFixedOpenNormalization": "5e6abc08e2f57fed1af0ae77b420d2e42971374a", "Sheaf.Paper.FiniteRingFixedPushComposition": "83216131ba92151caf42a571edb8cc0c764d29e0", "Sheaf.Paper.FiniteRingOrdinaryNormalizedCompositor": "e1a9e90ff56eeed61e4855e05b1d451c73ee5cec", "Sheaf.Paper.FiniteRingOrdinaryPushCoordinates": "523a34b8082718c28e18e5f2409a3af3bcaab682", "Sheaf.Paper.FiniteRingRefinementCoordinatesCore": "1b066b8c1de4ce2ce7cd228ed7eb9f2b58ed65d2"}, "results": {}, "time": "2026-10-28T12:20:18+0800", "transitive": 0, "version": 1}
```

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
