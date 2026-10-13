# ModuleCat.exists_kFlatLocalizedTensorComparison_natural

## Reason

The proof uses the generalized scalar-extension tensor notation and controlled
elaboration of scalar-adjunction and homology maps. The preflight conservatively
classifies file command changes as an interface change, requiring this record.
The added scope and options are local to this file and do not change the public
declaration's type, visibility, definitions, instances or the statement of any target.
The existing flatness and A-derived-category assumptions are unused in this proof;
their signatures remain identical, and only their lint checks are disabled locally.

## Old

The original command block was:
```lean
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat
```
The existing statement was:
```lean
theorem exists_kFlatLocalizedTensorComparison_natural
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (i : ℤ) :
    let m := fun U : CochainComplex.KFlat (ModuleCat.{u} A) ↦
      baseDerivedTensorCohomologyModel R A B (U.obj ⊗ Q) C
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let T := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ F ⋙ tensorRight N ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) i
    ∃ (S : CochainComplex.KFlat (ModuleCat.{u} A) ⥤ ModuleCat.{u} C)
      (η : S ⟶ T),
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).WKFlat.IsInvertedBy S ∧
      ∀ U : CochainComplex.KFlat (ModuleCat.{u} A),
        ∃ e : (extendScalars (algebraMap (A ⊗[R] B) C)).obj ((m U).cohomology i) ≅
          S.obj U,
          e.hom ≫ η.app U = (m U).localizedComparison i ≫
            HomologicalComplex.homologyMap
              ((Functor.Monoidal.μIso F U.obj Q).inv ≫ (F.obj U.obj ◁ t)) i
```

## New

The command block now is:
```lean
open scoped TensorProduct ChangeOfRings
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat
```
The existing theorem has these local lint settings:
```lean
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
```
Its public statement is identical:
```lean
theorem exists_kFlatLocalizedTensorComparison_natural
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (i : ℤ) :
    let m := fun U : CochainComplex.KFlat (ModuleCat.{u} A) ↦
      baseDerivedTensorCohomologyModel R A B (U.obj ⊗ Q) C
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let T := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ F ⋙ tensorRight N ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) i
    ∃ (S : CochainComplex.KFlat (ModuleCat.{u} A) ⥤ ModuleCat.{u} C)
      (η : S ⟶ T),
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).WKFlat.IsInvertedBy S ∧
      ∀ U : CochainComplex.KFlat (ModuleCat.{u} A),
        ∃ e : (extendScalars (algebraMap (A ⊗[R] B) C)).obj ((m U).cohomology i) ≅
          S.obj U,
          e.hom ≫ η.app U = (m U).localizedComparison i ≫
            HomologicalComplex.homologyMap
              ((Functor.Monoidal.μIso F U.obj Q).inv ≫ (F.obj U.obj ◁ t)) i
```
The proof is complete and invokes the new proved ordinary cohomology functor theorem,
coefficient transport by scalar adjunction, and the monoidal tensor naturality square.
No private helper is used in a public signature or definition body.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.KFlatLocalizedTensorComparisonNatural
--uses exists_kFlatLocalizedTensorComparison_natural` reports 429 transitive importers
and two declaration mentions: the item's own declaration and one external use.
The file-local elaboration options and scope do not propagate to those importers.
All existing signatures and definitions are unchanged, so their statements keep the
same meaning and no adaptation or renewed target-statement review is required.
No other module is edited or requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.KFlatLocalizedTensorComparisonNatural | U2 | Unchanged statement; completed proof and local proof settings. |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonDerivedArrow | unclaimed | Existing application uses the identical public statement; no edit needed. |

## Status

landed 20261013T211117-L-396248 2026-10-13 (merge of deliver/U2/Sheaf.Algebra.Homology.KFlatLocalizedTensorComparisonNatural)
