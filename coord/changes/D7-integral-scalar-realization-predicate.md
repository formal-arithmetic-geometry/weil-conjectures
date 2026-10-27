# AlgebraicGeometry.ProEtale.IntegralQuotient.ScalarRealized

## Reason

The concrete generator and K-flat predicate made the kernel expand the completed
coefficient rings while comparing the generic normalized section family with its
integral specialization. Abstract the same equations over an arbitrary coefficient
map in ScalarComparisonRealized and specialize that predicate in ScalarRealized.
This preserves every argument and both clauses definitionally. The proved private
scalar_comparison_realized checks the interface conversion before specialization.
No target statement or mathematical predicate changes.

## Old

```lean
def ScalarRealized (T : Scheme.{u})
    (q : SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring (integral l E) T)
      (S := ModuleRingedComparison.ring (finite l E n) T) (sectionReduction l E T n))
    (e₀ : extension (reduction l E n) T ⋙
        (ModuleRingedComparison.equivalence (finite l E n) T).functor ≅
      (ModuleRingedComparison.equivalence (integral l E) T).functor ⋙ q.extension)
    (e : D (reduction l E n) T ⋙
        ModuleRingedComparison.derivedFunctor (finite l E n) T ≅
      ModuleRingedComparison.derivedFunctor (integral l E) T ⋙ q.derived) : Prop :=
  (∀ (M : Modules (integral l E) T) (U : T.ProEtᵒᵖ)
      (s : (condensedRingObj (finite l E n) T).obj.obj U) (m : M.X.obj.obj U),
    ((eqToHom (q.extension_obj
      ((ModuleRingedComparison.equivalence (integral l E) T).functor.obj M))).val.app U)
        ((e₀.hom.app M).val.app U
          (InternalAbelianSheafModule.internalScalarGenerator (Scheme.ProEt.topology T)
            (coefficientMap (reduction l E n) T) M U s m)) =
      (toSheafify (Scheme.ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf (sectionReduction l E T n)
          ((ModuleRingedComparison.equivalence (integral l E) T).functor.obj M)).presheaf).app U
        (s ⊗ₜ[(ModuleRingedComparison.ring (integral l E) T).obj.obj U,
            ((sectionReduction l E T n).hom.app U).hom] m)) ∧
  (∀ P : CochainComplex (Modules (integral l E) T) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients
        (R := ModuleRingedComparison.ring (integral l E) T)
        (((ModuleRingedComparison.equivalence (integral l E) T).functor.mapHomologicalComplex
          (.up ℤ)).obj P) →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring (integral l E) T)
      ((ModuleRingedComparison.equivalence (integral l E) T).functor.obj (P.X i))) →
    (ModuleRingedComparison.derivedFunctor (finite l E n) T).map
        (compute (reduction l E n) T P) ≫
        (Functor.mapDerivedCategoryFactors
          (ModuleRingedComparison.equivalence (finite l E n) T).functor).hom.app
            (((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e₀ (.up ℤ)).hom.app P) =
      e.hom.app (DerivedCategory.Q.obj P) ≫
        q.derived.map
          (ModuleRingedComparison.sectionLocalizationComparison (integral l E) T P).hom ≫
        SheafOfModules.scalarPairComplexComparison q.extension q.extension_additive
          q.derived q.counit
          (((ModuleRingedComparison.equivalence (integral l E) T).functor.mapHomologicalComplex
          (.up ℤ)).obj P))

```

## New

```lean
def ScalarRealized (T : Scheme.{u})
    (q : SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring (integral l E) T)
      (S := ModuleRingedComparison.ring (finite l E n) T) (sectionReduction l E T n))
    (e₀ : extension (reduction l E n) T ⋙
        (ModuleRingedComparison.equivalence (finite l E n) T).functor ≅
      (ModuleRingedComparison.equivalence (integral l E) T).functor ⋙ q.extension)
    (e : D (reduction l E n) T ⋙
        ModuleRingedComparison.derivedFunctor (finite l E n) T ≅
      ModuleRingedComparison.derivedFunctor (integral l E) T ⋙ q.derived) : Prop :=
  ScalarComparisonRealized (reduction l E n) T q e₀ e

```

ScalarComparisonRealized has the identical expanded body, replacing integral l E,
finite l E n and reduction l E n by arbitrary R, S and a : R ⟶ S. It retains the
actual sectionScalarMap, ordinary generator and derived computation counit.
Unfolding this single new definition and sectionReduction recovers Old verbatim.

## Users

The read-only downstream.py scan reports zero downstream modules. Its --uses scan
finds ScalarRealized only in this item. The existing DAG parents keep the unchanged
item attachment. No source-library declaration is edited. Target semantic review
should verify the definitional identification of these two presentations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralQuotientExchangeComparison | D7 | Identical predicate, factored before specialization. |

## Status

landed 20261025T162207-L-354963 2026-10-25 (merge of deliver/D7/Sheaf.Paper.IntegralQuotientExchangeComparison)
