# AlgebraicGeometry.Scheme.pointSheafInsertionCalculus

## Reason

The complete proof requires the module pullback and section functors to retain their
standard zero-morphism instances while selected large constructions are locally
irreducible. Repeated unfolding exceeded the 60-second file limit. Private typed
constructions and a private graph-normalization predicate give the compiler a compact
API. Local reducibility attributes prevent unnecessary unfolding during this proof.
The delivery preflight requested this record for the added attribute commands.

## Old

There were no helper declarations `sectionFunctor_preservesZero` or
`pullbackFunctor_preservesZero`, and no local instance or irreducibility commands
for this proof. The existing theorem had its one `sorry`. Its statement and every
existing public definition remain verbatim in the delivery.

## New

The two helper statements are proved by the existing instances, before changing
reducibility. Their instance registration is explicitly local; no global instance
is added.

```lean
private theorem sectionFunctor_preservesZero (s : Scheme.{u})
    (A : Type u) [CommRing A] : (pointSheafSections s A).PreservesZeroMorphisms := by
  infer_instance

private theorem pullbackFunctor_preservesZero {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ) :
    (pointSheafPullback h A n).PreservesZeroMorphisms := by
  infer_instance

attribute [local instance] sectionFunctor_preservesZero pullbackFunctor_preservesZero

```

The complete irreducibility command groups used only in this file are:

```lean
attribute [local irreducible] proEtaleRingModulePullback
  proEtaleRingModulePullbackObj
  proEtaleRingModulePullbackMap proEtaleRingModuleAdjunction
  pointSheafCompositor
attribute [local irreducible] constantSheaf
attribute [local irreducible] sectionInsertionMap
attribute [local irreducible] pointSheafRestrictionCoefficients
  proEtaleConstantRingComparison
attribute [local irreducible] normalizedComparison
```

All new constructions are private. No existing declaration signature, public data
body, or public import changes. These local attributes do not change the meaning
of any target, so no target statement review is reopened.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus --uses
pointSheafInsertionCalculus` lists one downstream module and only the item's own
name in the identifier-use search. The direct importer was also inspected.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus | W8 | Existing public interface preserved; one proof completed with private helpers and local attributes. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Has a proof import of the item, with no current use of the theorem name. Public statements, definitions and instance environment are preserved; no adaptation is required. |

## Status

landed 20261022T020121-L-38279 2026-10-22 (merge of deliver/W8/Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus)
