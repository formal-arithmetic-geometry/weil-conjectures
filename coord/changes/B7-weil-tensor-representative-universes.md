# AlgebraicGeometry.Scheme.wfTensorRepresentative_exists

## Reason

Restore the quarantined module and repair four stuck universe constraints in
representative-comparison elaboration. The generic sheafification instance and
the specialized integral-operations site-size instance can introduce an auxiliary
universe when resolving the completed-coefficient total tensor. The fixed PBC
coefficient universe is already available. Temporarily exclude the generic
instances for this theorem command, as in the existing adic-reduction repairs.

The entire restored module compiles cleanly in 52.4 seconds. This is an
elaboration repair, with every existing signature, proof body, definition,
attribute and import preserved verbatim. No target interpretation changes.
The static interface checker conservatively requires a record for the new
attribute command, although its exclusion ends after the theorem.

## Old

```lean
set_option backward.isDefEq.respectTransparency false in
```

This was the sole elaboration wrapper immediately before the docstring of
`wfTensorRepresentative_exists`.

## New

```lean
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
set_option backward.isDefEq.respectTransparency false in
```

The theorem's docstring, signature and proof follow unchanged. Both instances
remain registered outside this command. No public instance or reducibility
attribute is removed or added.

## Users

`tools/downstream.py Sheaf.Paper.WeilTensorProduct --allow-missing
--uses wfTensorRepresentative_exists` finds no live downstream module while the
item is quarantined. A scan of both `lean/` and `quarantine/` finds only this
theorem and its use in `wfTensorModel`. That definition still selects the same
normalized representative comparison; the full module compile checks it.
Quarantined parent modules remain preserved. Importers receive the identical
public statements, definitions and instance environment, so need no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.WeilTensorProduct | B7 | The original theorem and wfTensorModel compile. |

## Status

landed 20261021T165754-L-2242243 2026-10-21 (merge of deliver/B7/Sheaf.Paper.WeilTensorProduct)
