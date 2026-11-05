/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportBaseChange

/-!
# The base change map and the finite-coefficient comparison

Let `T` be a finite discrete commutative ring and `Φ_X = ProEtale.finiteCoefficientModEquivalence`
the equivalence between module objects over `Λ_X = p_X^* T̲` and pro-étale sheaves of
`T`-modules, with derived functor `D(Φ_X)`. For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

`D(Φ_{Y'})` of the base change map `Lg^* Rf_* M ⟶ Rf'_* Lg'^* M` of module objects over `T̲`
(`ProEtale.CondensedRing.baseChangeMap`) and the derived base change map
`ProEtale.derivedBaseChangeMap` of pro-étale sheaves of `T`-modules at `D(Φ_X) M` are isomorphic
arrows (`ProEtale.nonempty_arrowIso_map_baseChangeMap_finiteCoefficient`).

The proof follows the residue field case
(`ProEtale.nonempty_arrowIso_map_exchangeRight_residueField_derivedBaseChangeMap`): the derived
comparisons `ProEtale.finiteCoefficientDerivedUpperStarIso : Lh^* ⋙ D(Φ) ≅ D(Φ) ⋙ Lh^*` are
compatible with the composition of derived pullbacks
(`ProEtale.finiteCoefficientDerivedUpperStarIso_compCoherence`, from the underived
`ProEtale.upperStarFiniteCoefficientModEquivalenceIso_compCoherence`), hence with the pullback
square comparisons, and the cube law of mates
(`CategoryTheory.Adjunction.nonempty_arrowIso_map_exchangeRight_app`) applies, the comparisons of
the derived pushforwards being invertible since `D(Φ)` is an equivalence.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

section Iso

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived pullbacks commute with the derived comparisons `D(Φ)` between module objects over
`T̲` and pro-étale sheaves of `T`-modules: `Lf^* ⋙ D(Φ_X) ≅ D(Φ_Y) ⋙ Lf^*`, induced by
`upperStarFiniteCoefficientModEquivalenceIso`. This is
`leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso`, stated with `D(Φ)` rather than
`finiteCoefficientDerivedEquivalence`. -/
noncomputable def finiteCoefficientDerivedUpperStarIso :
    L((f)^*⟦Profinite.continuousMapRingObj.{u} T⟧) ⋙
        (finiteCoefficientModEquivalence X T).functor.mapDerivedCategory ≅
      (finiteCoefficientModEquivalence Y T).functor.mapDerivedCategory ⋙
        L((f)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)]) :=
  Functor.isoWhiskerRight (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    (Profinite.continuousMapRingObj.{u} T) f) _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarFiniteCoefficientModEquivalenceIso f T) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory _ f).symm

end Iso

/-- **The derived finite-coefficient comparison is compatible with composition**: the
isomorphisms `finiteCoefficientDerivedUpperStarIso` are compatible with the composition
isomorphisms `L(p ≫ q)^* ≅ Lq^* ⋙ Lp^*` of derived pullbacks. -/
theorem finiteCoefficientDerivedUpperStarIso_compCoherence {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (q : Y ⟶ Z) (M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) Z))) :
    (finiteCoefficientDerivedUpperStarIso T (p ≫ q)).hom.app M ≫
        (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} T)) p q).hom.app
          ((finiteCoefficientModEquivalence Z T).functor.mapDerivedCategory.obj M) =
      (finiteCoefficientModEquivalence X T).functor.mapDerivedCategory.map
          ((CondensedRing.leftDerivedUpperStarComp
            (Profinite.continuousMapRingObj.{u} T) p q).hom.app M) ≫
        (finiteCoefficientDerivedUpperStarIso T p).hom.app
          (L((q)^*⟦Profinite.continuousMapRingObj.{u} T⟧).obj M) ≫
        L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)]).map
          ((finiteCoefficientDerivedUpperStarIso T q).hom.app M) := by
  -- As in `residueFieldDerivedUpperStarIsoCompCoherenceAt`, the unifications below only need
  -- to unfold reducible constants.
  with_reducible
    refine compCoherence_of_isoConj
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} T) q)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} T) p)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} T) (p ≫ q))
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} T)) q)
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} T)) p)
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} T)) (p ≫ q))
      ((Functor.mapDerivedCategoryCompIso
          ((q)^*⟦Profinite.continuousMapRingObj.{u} T⟧)
          (finiteCoefficientModEquivalence Y T).functor).inv ≫
        (Functor.mapDerivedCategoryNatIso (upperStarFiniteCoefficientModEquivalenceIso q T)).hom ≫
        (Functor.mapDerivedCategoryCompIso (finiteCoefficientModEquivalence Z T).functor
          ((q)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)])).hom)
      ((Functor.mapDerivedCategoryCompIso
          ((p)^*⟦Profinite.continuousMapRingObj.{u} T⟧)
          (finiteCoefficientModEquivalence X T).functor).inv ≫
        (Functor.mapDerivedCategoryNatIso (upperStarFiniteCoefficientModEquivalenceIso p T)).hom ≫
        (Functor.mapDerivedCategoryCompIso (finiteCoefficientModEquivalence Y T).functor
          ((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)])).hom)
      ((Functor.mapDerivedCategoryCompIso
          ((p ≫ q)^*⟦Profinite.continuousMapRingObj.{u} T⟧)
          (finiteCoefficientModEquivalence X T).functor).inv ≫
        (Functor.mapDerivedCategoryNatIso
          (upperStarFiniteCoefficientModEquivalenceIso (p ≫ q) T)).hom ≫
        (Functor.mapDerivedCategoryCompIso (finiteCoefficientModEquivalence Z T).functor
          ((p ≫ q)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)])).hom)
      ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp
        (Profinite.continuousMapRingObj.{u} T) p q)).hom ≫
        (Functor.mapDerivedCategoryCompIso
          ((q)^*⟦Profinite.continuousMapRingObj.{u} T⟧)
          ((p)^*⟦Profinite.continuousMapRingObj.{u} T⟧)).hom)
      ((Functor.mapDerivedCategoryNatIso (ProEtale.upperStarComp
        (ModuleCat.{u + 1} (ULift.{u + 1} T)) p q)).hom ≫
        (Functor.mapDerivedCategoryCompIso
          ((q)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)])
          ((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)])).hom)
      ?_ (finiteCoefficientDerivedUpperStarIso T q) (finiteCoefficientDerivedUpperStarIso T p)
      (finiteCoefficientDerivedUpperStarIso T (p ≫ q)) ?_ ?_ ?_
      (CondensedRing.leftDerivedUpperStarComp (Profinite.continuousMapRingObj.{u} T) p q)
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} T)) p q)
      ?_ ?_ M
  · with_reducible
      exact Functor.mapDerivedCategory_compCoherence' _ _ _ _ _
        (upperStarFiniteCoefficientModEquivalenceIso_compCoherence T p q)
  · intro M
    delta finiteCoefficientDerivedUpperStarIso
    with_reducible exact isoWhiskerRight_trans_isoWhiskerLeft_hom_app _ _ _ _ _ M
  · intro M
    delta finiteCoefficientDerivedUpperStarIso
    with_reducible exact isoWhiskerRight_trans_isoWhiskerLeft_hom_app _ _ _ _ _ M
  · intro M
    delta finiteCoefficientDerivedUpperStarIso
    with_reducible exact isoWhiskerRight_trans_isoWhiskerLeft_hom_app _ _ _ _ _ M
  · intro M
    delta CondensedRing.leftDerivedUpperStarComp Functor.leftDerivedFunctorNatIso
      Functor.leftDerivedFunctorCompIso CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    with_reducible exact trans_trans_isoWhiskerLeft_hom_app _ _ _ _ _ _ M
  · intro M
    delta ProEtale.leftDerivedUpperStarComp Functor.leftDerivedFunctorNatIso
      Functor.leftDerivedFunctorCompIso ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    with_reducible exact trans_trans_isoWhiskerLeft_hom_app _ _ _ _ _ _ M

variable {T} {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

end AlgebraicGeometry.ProEtale
