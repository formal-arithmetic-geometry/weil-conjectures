# CategoryTheory.module_abelian_evaluation_comparison_general

## Reason

The returned delivery overlapped a rollback which removed the general-site
interface entirely. The current node still lists this declaration. Restore it
with its complete proof, using the current source verbatim for every existing
declaration. The general topology and uniqueness clauses were already reviewed
in the node's `reviewed_lean` record; this restores that additive interface.

## Old

The declaration is absent from the current source after the rollback. The
existing Precoverage theorem and the three exact-composite helpers remain.

## New

```lean
theorem module_abelian_evaluation_comparison_general
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u})
    [EnoughInjectives (ringedSiteModules.{u} R)] (U : C) :
    ∃! e : ∀ q : ℕ,
      (SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).rightDerived q ≅
      SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q,
      ((SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).toRightDerivedZero ≫
          (e 0).hom =
        Functor.whiskerLeft (SheafOfModules.toSheaf R)
          ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).toRightDerivedZero)) ∧
      ∀ (M : ringedSiteModules.{u} R) (I : InjectiveResolution M)
        (K : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
        (φ : ((SheafOfModules.toSheaf R).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
          K.cocomplex)
        (_hφ : (SheafOfModules.toSheaf R).map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0) (q : ℕ),
        (e q).hom.app M ≫
            (K.isoRightDerivedObj
              (sheafToPresheaf J AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom =
          (I.isoRightDerivedObj
            (SheafOfModules.toSheaf R ⋙
              (sheafToPresheaf J AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))) q).hom ≫
            HomologicalComplex.homologyMap
              (((sheafToPresheaf J AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
                  (.up ℕ)).map φ) q
```

The proof uses the existing exact-composite helpers and injective acyclicity.
Uniqueness follows by applying both resolution-lift formulas to a standard lift
and cancelling the terminal resolution isomorphism. No existing signature,
attribute, import or definition changes; target statements and meanings do not change.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison | P3 | Restore the proved additive interface. |

The current source contains no consumer of the restored name. Direct importers
retain all existing declarations verbatim and need no adaptation. The archived
consumer, if restored separately, can use the already attached general interface.

## Status

landed 20261024T015351-L-2369259 2026-10-24 (merge of deliver/P3/Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison)
