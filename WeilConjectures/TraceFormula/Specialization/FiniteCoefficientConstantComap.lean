/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ChangeOfRings
public import WeilConjectures.TraceFormula.Specialization.ThickOriginFiniteModule

/-!
# Constant complexes and change of finite coefficient rings

Let `ρ : T →+* T'` be a homomorphism of finite discrete commutative rings and `Y` a scheme. The
constant complex functor `ProEtale.finiteCoefficientConstantFunctor` commutes with restriction of
scalars along `ρ`:

* on sheaves, the pro-étale pullback of the constant étale sheaf commutes with restriction of
  scalars (`ProEtale.constantSheafCompComparisonUpperStarRestrictScalarsIso`), both sides being
  left adjoint to the same functor `F ↦ coextend Γ(Y, F)`;
* on constant complexes, restriction of scalars of module objects along `T_Y ⟶ T'_Y` corresponds
  to restriction of scalars of modules
  (`ProEtale.finiteCoefficientConstantFunctorCompComapIso`); in particular the restriction of
  scalars of the unit is the constant complex of `T'` viewed as a `T`-module
  (`ProEtale.finiteCoefficientConstantFunctorObjComapIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {T T' : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
  [DiscreteTopology T'] [Finite T'] (ρ : T →+* T') (Y : Scheme.{u})

/-- The pro-étale pullback of the constant étale sheaf commutes with restriction of scalars along
`ρ`: both functors are left adjoint to `F ↦ coextend Γ(Y, F)`, the global sections over the
terminal étale scheme being computed in the same way on both sides. -/
noncomputable def constantSheafCompComparisonUpperStarRestrictScalarsIso :
    ModuleCat.restrictScalars ρ.ulift ⋙
        constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T)) ⋙
          ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)] ≅
      constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T')) ⋙
        ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T')] ⋙
          Sheaf.restrictScalars (Scheme.ProEt.topology Y) ρ.ulift :=
  (conjugateIsoEquiv
    ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T'))
      terminalIsTerminal).comp ((comparisonAdjunction _ Y).comp
        (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) ρ.ulift)))
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} ρ.ulift).comp
      ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T))
        terminalIsTerminal).comp (comparisonAdjunction _ Y)))).symm
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl)

/-- Restriction of scalars of module objects along `T_Y ⟶ T'_Y` after the inverse of the derived
comparison is the inverse of the derived comparison after restriction of scalars of sheaves. -/
noncomputable def finiteCoefficientDerivedEquivalenceInverseComapIso :
    (finiteCoefficientDerivedEquivalence Y T').inverse ⋙
        (Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) Y)).mapDerivedCategory ≅
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) ρ.ulift ⋙
        (finiteCoefficientDerivedEquivalence Y T).inverse :=
  Iso.inverseCompIso
    (Iso.isoCompInverse (finiteCoefficientDerivedEquivalenceComapIso Y ρ) ≪≫
      Functor.associator _ _ _)

/-- **Constant complexes and restriction of scalars**: restricting scalars of the constant complex
of a `T'`-module `N` along `T_Y ⟶ T'_Y` gives the constant complex of `N` viewed as a `T`-module.
-/
noncomputable def finiteCoefficientConstantFunctorCompComapIso :
    finiteCoefficientConstantFunctor T' Y ⋙
        (Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) Y)).mapDerivedCategory ≅
      ModuleCat.restrictScalars ρ.ulift ⋙ finiteCoefficientConstantFunctor T Y :=
  Functor.associator (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T')))
      _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (finiteCoefficientDerivedEquivalenceInverseComapIso ρ Y)) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T')]).mapDerivedCategorySingleFunctor 0) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight
              ((Sheaf.restrictScalars (Scheme.ProEt.topology Y)
                ρ.ulift).mapDerivedCategorySingleFunctor 0) _ ≪≫
            Functor.associator _ _ _) ≪≫
        (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constantSheafCompComparisonUpperStarRestrictScalarsIso ρ Y).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight
              ((ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).mapDerivedCategorySingleFunctor 0).symm
              _ ≪≫
            Functor.associator _ _ _))

/-- **The restriction of scalars of the unit**: restricting scalars of the unit along
`T_Y ⟶ T'_Y` gives the constant complex of `T'` viewed as a `T`-module. -/
noncomputable def finiteCoefficientConstantFunctorObjComapIso :
    (finiteCoefficientConstantFunctor T Y).obj ((ModuleCat.restrictScalars ρ.ulift).obj
        (ModuleCat.of (ULift.{u + 1} T') (ULift.{u + 1} T'))) ≅
      (Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
        continuous_of_discreteTopology) Y)).mapDerivedCategory.obj (𝟙_ _) :=
  ((finiteCoefficientConstantFunctorCompComapIso ρ Y).app _).symm ≪≫
    (Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
      continuous_of_discreteTopology) Y)).mapDerivedCategory.mapIso
      (finiteCoefficientConstantFunctorObjSelfIso T' Y)

end AlgebraicGeometry.ProEtale
