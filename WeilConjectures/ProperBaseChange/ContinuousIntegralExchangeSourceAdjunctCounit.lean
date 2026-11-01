/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ChangeOfCoefficients
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import all WeilConjectures.ProperBaseChange.ContinuousIntegralExchangeSourceAdjunctBounded

/-! # Coherence of integral localization and the specified exchange map: push counit

The counit square of the push comparison used by
`Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct` (split from it for compile time). -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

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

private lemma integral_push_counit (K : integralConstructible ℓ E X) :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (f.asOver (Spec (.of k)))).map
        (integralConstructiblePushHom ℓ E k f K) ≫
      (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
        (f.asOver (Spec (.of k)))).counit.app
          ((integralScalarConstructible ℓ E X).obj K) =
    (integralConstructiblePullIso ℓ E k f
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
        (f.asOver (Spec (.of k)))).obj K)).inv ≫
      (integralScalarConstructible ℓ E X).map
        ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ
          (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).counit.app K) := by
  let : IsCommMonObj (condensedRingObj (integralCoeff ℓ E) X) :=
    ProEtale.isCommMonObj_condensedRingObj _ X
  let : IsCommMonObj (condensedRingObj (integralCoeff ℓ E) Y) :=
    ProEtale.isCommMonObj_condensedRingObj _ Y
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  simp only [bounded_counit_hom_continuousMap ℓ E k f, upperStar_map_hom ℓ E k f]
  simp only [integralScalarConstructible, integralConstructiblePushHom,
    integralConstructiblePullIso,
    ObjectProperty.lift_map, ObjectProperty.homMk_hom, ObjectProperty.isoMk_inv,
    Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_map, ObjectProperty.ι_obj]
  simp only [bounded_counit_hom_unitBall ℓ E k f]
  simp only [derivedPushHom, derivedPullIso, integralScalarExtension, OverClass.asOverHom_left,
    UnitBallRingObj.boundedConstructibleLowerStar, ObjectProperty.lift_obj_obj, Functor.comp_obj,
    ObjectProperty.ι_obj, Iso.app_inv]
  have hcc := coefficient_counit
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (integralScalarMap ℓ E) X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (integralScalarMap ℓ E) Y))
    (derivedUpperStarLowerStarAdjunction (integralCoeff ℓ E) f)
    (derivedUpperStarLowerStarAdjunction _ f)
    (derivedComapLowerStarIso (integralScalarMap ℓ E) f) K.obj

  with_reducible exact hcc

end AlgebraicGeometry.ProEtale.CondensedRing
