/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
import all WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate

/-! # The derived scalar restriction square as a mate

Source: Stacks Project, Tag 0GL6; derived adjunction transposition.
(blueprint: lem-sf-etale-restriction-derived-mate).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The resolution-normalized proper comparison is the mate of the exact pullback square.
Source: Stacks Project, Tag 0GL6 and the derived-adjunction construction.
(blueprint: lem-sf-etale-restriction-derived-mate).

Proof: the ordinary pullback/restriction square is defined as the inverse mate of
lowerStarCompRestrictScalarsIso. Apply the exact derived mate identity: both derived
maps have the same factorization after the right-derived functor unit. This is the
universal property used in the definition of rightDerivedFunctorPlusBaseChange,
so the two transformations are equal. No properness or finiteness is required. -/
theorem rightDerivedLowerStarRestrictScalars_eq_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    rightDerivedLowerStarRestrictScalars φ f =
      (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).derivedPlus
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).derivedPlus
        (TwoSquare.mk _ _ _ _
          (((Functor.mapDerivedCategoryPlusCompIso
              (Sheaf.restrictScalars Y.smallEtaleTopology φ)
              (upperStar (ModuleCat.{u + 1} A) f)).symm ≪≫
            Functor.mapDerivedCategoryPlusNatIso (upperStarRestrictScalarsIso φ f) ≪≫
            Functor.mapDerivedCategoryPlusCompIso (upperStar (ModuleCat.{u + 1} B) f)
              (Sheaf.restrictScalars X.smallEtaleTopology φ)).hom))).natTrans := by
  have h := derived_mate_eq
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarRestrictScalarsIso φ f)
  have hm : (mateEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom)).natTrans =
      (lowerStarCompRestrictScalarsIso φ f).hom := by
    exact congrArg TwoSquare.natTrans ((mateEquiv _ _).apply_symm_apply _)
  rw [hm] at h
  exact h

end AlgebraicGeometry.Etale
