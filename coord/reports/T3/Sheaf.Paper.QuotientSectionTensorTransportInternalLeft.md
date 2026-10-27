## What changed

Completed `section_tensor_transport_internal_left` by transferring the independent K-flat
and termwise flat hypotheses through the section-module equivalence, deriving the
three normalization equations, and applying a new categorical paste lemma. Added the
new module `Sheaf.Paper.QuotientSectionTensorTransportInternalLeftCore` for the
remaining reassociation and cancellation argument.

## Proved and sorry left

The item theorem `section_tensor_transport_internal_left` is proved (1 of 1 original
sorries closed). One strictly smaller statement remains as `section_tensor_transport_internal_left_core`
in the new core module; its hypotheses are the three concrete normalization equations
(`hbn`, `hcn`, and `hqnorm`) and its conclusion is the categorical paste after those
normalizations. It has one `sorry`.

## No longer needed

Removed the unused proof import `Sheaf.Paper.IntegralResidueDerivedMonoidal` from the
item module. The direct naturality and reassociation declarations originally planned in
the item are supplied by the core statement, so no additional local declarations are
needed.

## Where the brief, the DAG or earlier work was wrong

The planned direct `rw` route is blocked by opaque derived-category aliases: rewriting
`c.model.T.map` around `tensorComparison` changes the elaborated derived category and
Lean rejects the otherwise definitionally equal morphism. The split core statement
records the categorical paste after the normalization equations, avoiding that
re-elaboration at the item boundary.

## New nodes

Added `lem-sfb-quotient-section-tensor-transport-internal-left-core` for
`section_tensor_transport_internal_left_core`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.QuotientSectionTensorTransportInternalLeft": "b7f0bf88f63eeb6cafc10d354aa2bcb2aed5433f", "Sheaf.Paper.QuotientSectionTensorTransportInternalLeftCore": "e71d4d82fb83288280501097e15343df8989c129"}, "results": {"Sheaf.Paper.QuotientSectionTensorTransportInternalCounit": {"hash": "b46dbc485f7ddea063001f3c35ccf110e0e0f5dc", "status": "OK"}}, "seconds": 25, "time": "2026-10-28T05:54:43+0800", "transitive": 0, "version": 1}
```

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
