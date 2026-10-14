# standardSingle_union_ses_presentation

## Reason

The static interface detector flags local `open` and `variable` commands used for
private cylinder helpers. This record documents those commands and the removal of three redundant
direct Mathlib imports found in the second reading. They are scoped
inside namespace AlgebraicGeometry and a section that ends before the target.
All existing declaration signatures and visibility remain identical. No target
meaning, public definition, instance, notation or attribute is changed.

## Old

```lean
theorem standardSingle_union_ses_presentation
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let a := Arrow.mk (standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g)
    let aU := Arrow.mk (standardSingleBaseChangeMap (U.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_left) N) g)
    let aV := Arrow.mk (standardSingleBaseChangeMap (V.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_right) N) g)
    let aUV := Arrow.mk (standardSingleBaseChangeMap ((U ⊓ V).ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE (inf_le_left.trans le_sup_left)) N) g)
    ∃ (P P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings A.toRingedSpace)) ℤ))
      (m : P ⟶ P')
      (e₁ : DerivedCategory.Q.obj P.X₁ ≅ a.left)
      (e₂ : DerivedCategory.Q.obj P.X₂ ≅ aU.left ⊞ aV.left)
      (e₃ : DerivedCategory.Q.obj P.X₃ ≅ aUV.left)
      (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ aU.right ⊞ aV.right)
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ aUV.right),
      P.ShortExact ∧ P'.ShortExact ∧
      DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
      DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom = e₂.hom ≫ biprod.map aU.hom aV.hom ∧
      DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = e₃.hom ≫ aUV.hom
```

## New

The theorem has exactly the same signature as above. Its proof is now the concrete
mapping-cylinder construction from standardSingle_union_ses_chain_data.
The local commands added before the private helpers are:

```lean
open CochainComplex
noncomputable section
variable {C : Type u} [Category C] [Abelian C]
variable {A B A' B' : CochainComplex C ℤ}
section
variable [HasDerivedCategory.{w} C]
```

Removed direct imports of Mathlib.Algebra.Homology.DerivedCategory.ShortExact,
Mathlib.CategoryTheory.Comma.Arrow and
Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts from both delivered modules.
All three removed modules remain transitively publicly imported through
StandardSingleBaseChangeMap: Arrow through Localization.Adjunction, ShortExact
through DerivedCategory.TStructure, and BinaryBiproducts through
Limits.Preserves.Shapes.Biproducts. The source import graph and compilation
confirm this; exported declarations are preserved. No downstream
module is adapted.

Both sections end before the target declaration. Universe w is used only by
private helpers; the target still has exactly its original universe u.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StandardSingleUnionSESPresentation | Q4 | Local private-helper context; existing signature unchanged. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionTriangles | unclaimed | Uses the same target signature; no adaptation needed. |

`tools/downstream.py --uses AlgebraicGeometry.standardSingle_union_ses_presentation`
reports these two textual users. The local commands have no exported notation,
instances or declarations, so all transitive importers receive the same API.
No module beyond the item is adapted and no target semantic review is reopened.

## Status

landed 20261014T013044-L-3417182 2026-10-14 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.StandardSingleUnionSESPresentation)
