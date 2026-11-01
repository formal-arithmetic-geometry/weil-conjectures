/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPullComposition
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteDiscreteRingObj.FiniteDiscreteCoefficientBaseChange
import all WeilConjectures.ProperBaseChange.ContinuousIntegralExchangeTargetAdjunctPull

/-! # Coherence of integral localization and the specified exchange map: counit square

The counit square of the pull and push comparisons used by
`Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` (split from it for compile time). -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

open CategoryTheory

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section FiniteIntermediateField

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

private lemma integralPull_counit
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    (K : integralConstructible ℓ E T) :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (h.asOver (Spec (.of
      k)))).map
        (integralConstructiblePushHom ℓ E k h K) ≫
      (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
        (h.asOver (Spec (.of k)))).counit.app
          ((integralScalarConstructible ℓ E T).obj K) =
    (integralConstructiblePullIso ℓ E k h
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (h.asOver (Spec (.of k)))).obj K)).inv ≫
      scalarMap (integralScalarConstructible ℓ E T)
        ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (h.asOver (Spec
          (.of k)))).counit.app K) := by
  let : IsCommMonObj (condensedRingObj (integralCoeff ℓ E) T) :=
    ProEtale.isCommMonObj_condensedRingObj _ T
  let : IsCommMonObj (condensedRingObj (integralCoeff ℓ E) U) :=
    ProEtale.isCommMonObj_condensedRingObj _ U
  apply ObjectProperty.hom_ext
  simp only [scalarMap, ObjectProperty.FullSubcategory.comp_hom]
  simp only [bounded_counit_hom_continuousMap ℓ E k h, upperStar_map_hom ℓ E k h]
  simp only [integralScalarConstructible, integralConstructiblePushHom,
    integralConstructiblePullIso,
    ObjectProperty.lift_map, ObjectProperty.homMk_hom, ObjectProperty.isoMk_inv,
    Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_map, ObjectProperty.ι_obj]
  simp only [bounded_counit_hom_unitBall ℓ E k h]
  simp only [derivedPushHom, derivedPullIso, integralScalarExtension, OverClass.asOverHom_left,
    UnitBallRingObj.boundedConstructibleLowerStar, ObjectProperty.lift_obj_obj, Functor.comp_obj,
    ObjectProperty.ι_obj, Iso.app_inv]
  have hcc := push_pull_counit
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (integralScalarMap ℓ E) T))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (integralScalarMap ℓ E) U))
    (derivedUpperStarLowerStarAdjunction (integralCoeff ℓ E) h)
    (derivedUpperStarLowerStarAdjunction _ h)
    (derivedComapLowerStarIso (integralScalarMap ℓ E) h) K.obj
  with_reducible exact hcc

end FiniteIntermediateField

end AlgebraicGeometry.ProEtale.CondensedRing
