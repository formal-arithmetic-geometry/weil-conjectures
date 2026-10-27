# CategoryTheory.adjunctionSquare

## Reason

Repair the return of delivery `765d418bde3`: the item copied this already proved
helper word for word from `ConstantScalarGeometricAdjunctions`. The existing
helper was private, so importers could not call it. Its module is unclaimed.
Expose this one existing theorem in place and remove the duplicate private proof
from the item. The existing proof and every binder remain verbatim. This is a
visibility repair; no mathematical statement, definition or target changes.
The newly exported helper is attached to its existing node
`lem-sfb-constant-scalar-geometric-adjunctions`, with a source docstring.

## Old

```lean
private theorem adjunctionSquare
    {A A' D D' : Type*} [Category A] [Category A'] [Category D] [Category D']
    (F : A ⥤ A') (G : D ⥤ D') [F.Full] [F.Faithful]
    [G.Full] [G.Faithful] [G.EssSurj]
    {L : A ⥤ D} {R : D ⥤ A} {L' : A' ⥤ D'} {R' : D' ⥤ A'}
    (a : L ⊣ R) (b : L' ⊣ R') (β : R ⋙ F ≅ G ⋙ R') :
    ∃ α : L ⋙ G ≅ F ⋙ L',
      (∀ M N (f : L.obj M ⟶ N),
        b.homEquiv _ _ (α.inv.app M ≫ G.map f) =
          F.map (a.homEquiv M N f) ≫ β.hom.app N) ∧
      (∀ M, F.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫
        R'.map (α.hom.app M) = b.unit.app (F.obj M)) ∧
      (∀ N, G.map (a.counit.app N) = α.hom.app (R.obj N) ≫
        L'.map (β.hom.app N) ≫ b.counit.app (G.obj N))
```

## New

```lean
theorem adjunctionSquare
    {A A' D D' : Type*} [Category A] [Category A'] [Category D] [Category D']
    (F : A ⥤ A') (G : D ⥤ D') [F.Full] [F.Faithful]
    [G.Full] [G.Faithful] [G.EssSurj]
    {L : A ⥤ D} {R : D ⥤ A} {L' : A' ⥤ D'} {R' : D' ⥤ A'}
    (a : L ⊣ R) (b : L' ⊣ R') (β : R ⋙ F ≅ G ⋙ R') :
    ∃ α : L ⋙ G ≅ F ⋙ L',
      (∀ M N (f : L.obj M ⟶ N),
        b.homEquiv _ _ (α.inv.app M ≫ G.map f) =
          F.map (a.homEquiv M N f) ≫ β.hom.app N) ∧
      (∀ M, F.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫
        R'.map (α.hom.app M) = b.unit.app (F.obj M)) ∧
      (∀ N, G.map (a.counit.app N) = α.hom.app (R.obj N) ≫
        L'.map (β.hom.app N) ≫ b.counit.app (G.obj N))
```

The proof is unchanged. The item calls this imported theorem twice, for the
ordinary left adjoint and the further left adjoint.

## Users

`tools/downstream.py Sheaf.CategoryTheory.ConstantScalarGeometricAdjunctions
--uses adjunctionSquare` reports five downstream modules, and only the defining
module currently mentions this helper. The repaired item becomes its new external
consumer. Widening visibility does not change any existing elaborated signature;
there are no existing public declarations named `CategoryTheory.adjunctionSquare`.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.CategoryTheory.ConstantScalarGeometricAdjunctions` | unclaimed | Existing helper exported; its two calls and proof stay unchanged. |
| `Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData` | T5 | Remove duplicate helper; its two calls use the imported theorem. |
| `Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData` | unclaimed | No helper reference, no adaptation needed. |
| `Sheaf.CategoryTheory.ConstantModuleDerivedProjectionIdentification` | A6 | No helper reference, no adaptation needed. |
| `Sheaf.CategoryTheory.ConstantModulePlusComparisonData` | unclaimed | No helper reference, no adaptation needed. |
| `Sheaf.Paper.FiniteCoefficientDerivedExchangeIdentification` | D8 | No helper reference, no adaptation needed. |

## Status

landed 20261023T152029-L-432828 2026-10-23 (merge of deliver/T5/Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData)
