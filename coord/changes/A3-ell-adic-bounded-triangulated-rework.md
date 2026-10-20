# isTriangulated_boundedConstructible_ellAdic compile repair

## Reason

Restore the module assigned in `coord/rework.tsv` from
`quarantine/Sheaf/AlgebraicGeometry/EllAdicBoundedTriangulated.lean`.
The recorded error at line 84 is an application type mismatch: the coefficient ring
is supplied where the public constructibility transport lemma expects an isomorphism.
The previous private helper is no longer exposed by the synchronized upstream module.
This is a proof repair with zero original or final holes; no signature, definition,
attribute or public import changes.

## Old

```lean
exact constructible_of_iso R (limit.isoLimitCone ⟨s, hs⟩) (hk _ _ f hf.1 hf.2).1
exact constructible_of_iso R (colimit.isoColimitCocone ⟨s, hs⟩) (hk _ _ f hf.1 hf.2).2
```

The helper ended with `infer_instance` and imported the upstream module's private names.

## New

```lean
exact _root_.constructible_of_iso (R := R) (limit.isoLimitCone ⟨s, hs⟩)
  (hk _ _ f hf.1 hf.2).1
exact _root_.constructible_of_iso (R := R) (colimit.isoColimitCocone ⟨s, hs⟩)
  (hk _ _ f hf.1 hf.2).2
```

The helper ends with `exact isTriangulated_boundedConstructible_of_serre R`.
Remove only the unused `import all` of the upstream derived-category module.
The existing ordinary public import remains. The public theorem, its type and
its four coefficient cases are unchanged. The original node attachment is preserved.

## Users

`tools/downstream.py` reports the item as unknown while it is quarantined.
A search of both `lean/` and `quarantine/` finds one direct importing module. It uses
only the unchanged public theorem, at its existing unchanged type. No adaptation is
necessary. A standalone consumer imports the repaired module alone and applies that
same public theorem with its full original signature, checked through `lcompile.py`.
There is no importer-visible interface change and no target statement is altered.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated | A3 | Assigned module: proof repair. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorPreservation | unclaimed | Public theorem type unchanged; no adaptation. |

## Status

landed 20261020T154033-L-3030057 2026-10-20 (merge of deliver/A3/Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated)
