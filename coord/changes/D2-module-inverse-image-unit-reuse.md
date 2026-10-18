# SheafOfModules.inverseImage_underlying_unit_of_actions

## Reason

Remove an unused private helper and its local generator variable after replacing the
public theorem's proof by the already proved, identical public statement
`SheafOfModules.inverseImage_underlying_of_ring_presentation`.
The static gate requests a change record because deleting `open` and `variable`
commands is conservatively classified as an interface change. These commands occur
inside this module's namespace; the removed theorem is private and neither its type
nor its value is used in a public definition. All public declarations, their
signatures, public imports and attributes are unchanged. No target meaning changes.

## Old

```lean
open MonoidalCategory
variable (hgen : ∀ (M : SheafOfModules.{u} A) (T : Sheaf K (Type u))
  (a b : (sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B ⊗
    (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
      ((sheafPullback F AddCommGrpCat.{u} J K).obj ((toSheaf A).obj M)) ⟶ T),
  (∀ (U : Cᵒᵖ) (r : A.obj.obj U) (m : M.val.obj U),
    a.hom.app (F.op.obj U)
        (φ.hom.app U r,
          ((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m) =
      b.hom.app (F.op.obj U)
        (φ.hom.app U r,
          ((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m)) → a = b)
include hgen in
private theorem inverseImage_underlying_unit_of_actions
    (actions : ∀ M : SheafOfModules.{u} A, InverseImageAction φ M) :
    ∃ e : pullback.{u} φ ⋙ toSheaf B ≅
        toSheaf A ⋙ sheafPullback F AddCommGrpCat.{u} J K,
      ∀ M, (toSheaf A).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).map (e.hom.app M) =
          (sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
            ((toSheaf A).obj M) := by
  sorry
```

## New

The entire block above is removed. The existing public theorem immediately follows
the unchanged structural-ring-map variable declaration, with unchanged signature and
with this proof:

```lean
  exact inverseImage_underlying_of_ring_presentation φ pr hr
```

The direct proof imports of `ModuleInverseImageAction` and the retired
`EtaleInverseImageModuleAdjunction` wrapper are also removed, and `import all` of
`ModuleInverseImageAdjunction` becomes an ordinary proof import. No public import
changes.

## Users

`tools/downstream.py Sheaf.CategoryTheory.ModuleInverseImageUnitComparison --uses
SheafOfModules.inverseImage_underlying_unit_of_actions` reports exactly the module
itself as a textual user (its declaration and its former application). No external
module uses the deleted private declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ModuleInverseImageUnitComparison | D2 | Remove the unused private helper and replace the public proof by the existing exact theorem. |

The direct consumer `Sheaf.AlgebraicGeometry.ProEtaleModuleSpecializationUnit` still
uses the same unchanged public theorem and requires no adaptation. There are no
adapted modules, changed public definitions, or target statements to review again.

## Status

landed 20261018T062721-L-639384 2026-10-18 (merge of deliver/D2/Sheaf.CategoryTheory.ModuleInverseImageUnitComparison)
