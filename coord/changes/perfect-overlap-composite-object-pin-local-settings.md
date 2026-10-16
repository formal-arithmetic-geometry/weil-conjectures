# perfect_overlap_composite_object_pin

## Reason

The new proof compares dependent derived-functor object types. Local irreducibility
settings keep those comparisons within the compile limit.
The interface checker conservatively flags commands in a public section, although
no existing declaration signature, visibility or public import changed.

## Old

The original local attribute block is:

```lean
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
```

The theorem's old signature is identical to the delivered signature, verified with
the repository declaration parser. Its original body was `by sorry`.

## New

```lean
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory

attribute [local instance_reducible] TopologicalSpace.Opens.map
attribute [local instance_reducible] OrderHomClass.toOrderHom
attribute [local instance_reducible] TopCat.Hom.frameHom
attribute [local irreducible] derivedPullback perfectHomComposition
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
```

The existing theorem now combines the two named component equations by categorical
associativity. The two new proof imports are private imports. The mathematical
statement and all imported definitions stay unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeObjectPin | C1 | Claimed item; new proof and local elaboration settings. |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData | unmodified | Existing signature and visibility unchanged; no adaptation required. |

The changed commands are local elaboration controls, so every importer sees exactly
the same existing theorem and public imports. No target meaning changes and no
forced adaptation is required. Existing comparison and composite-transport API
modules have only new DAG attachments; their Lean files are untouched.

## Status

landed 20261016T020324-L-853953 2026-10-16 (merge of deliver/C1/Sheaf.AlgebraicGeometry.PerfectOverlapCompositeObjectPin)
