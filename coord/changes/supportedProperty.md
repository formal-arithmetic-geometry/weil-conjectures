# supportedProperty

## Reason
Factor the unchanged target predicate into a transparent abbreviation for its three closure
obligations. No existing definition or statement changes meaning.

## Old
No declaration.

## New
```lean
abbrev supportedProperty (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) : ObjectProperty (schemeDerivedCategory X) := fun K ↦
  schemeDerivedQCohProperty X K ∧ ∀ (n : ℤ) (x : X), x ∉ T →
    Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x))
```

## Users
| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedQCohTriangulated | D2 | Defines the abbreviation and uses it in closure lemmas; the existing target signature stays byte for byte identical. |

The abbreviation is new, so no existing downstream module refers to its name. The target
continues to state the original predicate explicitly. No target semantics review is reopened.

## Status
landed 20261012T135224-L-1658455 2026-10-12 (merge of deliver/D2/Sheaf.AlgebraicGeometry.SupportedQCohTriangulated)
