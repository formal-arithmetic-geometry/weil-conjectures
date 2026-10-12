# AlgebraicGeometry.derivedPullback_monoidal_descent: shared local instance selection

## Reason

The first two dry runs timed out after 60 seconds while applying the new comparison
and coherence lemmas. Separate compiles passed in 40.7 and 38.6 seconds; structural
comparison of separately instantiated concrete monoidal structures was too expensive.
Register the comparison module's identical concrete instance wrappers locally before
elaborating the original theorem. The theorem and the three new lemmas then use the
same values directly. The next single-file compile passed in 27.2 seconds.

The comparison module becomes a public import because its concrete wrapper values
occur as implicit instance arguments in the public theorem type. Each original
wrapper keeps its name, complete type, universe parameters, visibility, registration
and definition body verbatim. The new wrappers are the same constructions under
new names. The original theorem's written signature is verbatim unchanged, and its
elaborated type is definitionally equal to the original one. No target statement or
meaning is changed. No adaptation of any other module is delivered.

The complete four-module set subsequently compiled, with the item in 35.9 seconds.
An original-signature test using only the original wrapper registrations compiled
in 32.2 seconds by applying the delivered theorem, verifying the definitional
interface equality. The unchanged direct consumer
`Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel` compiled against the delivered
output in 36.9 seconds. No consumer source is adapted or included in the delivery.

## Old

The original public dependency header, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

There was no additional instance registration between the existing instance
wrappers and the theorem's existing two transparency options.

The original theorem signature, verbatim:

```lean
theorem derivedPullback_monoidal_descent {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (mF : F.CoreMonoidal)
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    (φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _))
    (hφ : ∀ P N p q n (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
              (ComplexShape.up ℤ) p q n h) ≫ (φ P N).hom.f n =
            (mF.μIso (P.X p) (N.X q)).inv ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (curriedTensor _) (ComplexShape.up ℤ) p q n h)
    (hnatural : ∀ (P P' N N' : CochainComplex
              (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
            (a : P ⟶ P') (b : N ⟶ N'),
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (HomologicalComplex.mapBifunctorMap a b (curriedTensor _) (ComplexShape.up ℤ)) ≫
              (φ P' N').hom =
            (φ P N).hom ≫
              HomologicalComplex.mapBifunctorMap
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map b) (curriedTensor _)
                (ComplexShape.up ℤ))
    (hiso : ∀ P N : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlat (R := X.sheaf) P → CochainComplex.IsKFlat (R := X.sheaf) N →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
                (φ P N).hom)))
    : ∃ m : (derivedPullback g).CoreMonoidal,
        ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlat (R := X.sheaf) P →
          CochainComplex.IsKFlat (R := X.sheaf) N →
          (m.μIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
```

## New

```lean
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorAssociativity
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit
```

The following registration is added after the unchanged original instances and
before the theorem's unchanged transparency options:

```lean
attribute [local instance] tensorDescentPullbackDescentModuleTensor
  tensorDescentModuleSymmetric
  tensorDescentModulePreadditive
  tensorDescentModuleClosed
  tensorDescentModuleGrothendieck
  tensorDescentModuleResolutions
  tensorDescentModuleDerivedMonoidal
  tensorDescentPullbackDescentQLax
```

All eight existing instance declarations and their bodies remain verbatim unchanged.
The public theorem signature remains verbatim unchanged. The shared wrappers have
local registrations only and no new global instance is exported.

The theorem's new signature is verbatim the same signature shown under Old.
Its proof is changed, and the original eight local instance declarations are
unchanged. The original-signature scratch proof verifies the equality of the
elaborated interfaces with the different local instance selections.

## Users

The `tools/downstream.py --uses` searches for each of the eight original wrapper
names found only the item and the monoidal-model module as direct name users.
The import graph contains 358 transitive downstream modules; since the original
wrapper definitions and theorem signature are unchanged and the shared concrete
instances are definitionally identical, their statements retain the same meaning.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent | Y2 | Selects the identical comparison instance wrappers locally for the theorem and its proof. |
| Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel | unclaimed | Uses all eight original wrappers; all names, types and bodies stay identical. Source unchanged. |

## Status

landed 20261012T184400-L-4025866 2026-10-12 (merge of deliver/Y2/Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent)
