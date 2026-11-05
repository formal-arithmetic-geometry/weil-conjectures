/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueComparisonInterface

/-! # The scalar-adjunction normalization of the derived residue pull square

Source: Bhatt--Scholze, Remark 6.8.15, and associativity of derived scalar extension.
(blueprint: new-integral-residue-pull-square-data)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] Functor.leftDerivedFunctor

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The canonical restriction/pullback square, obtained by applying the levelwise
comparison and the exact-pullback identifications. Its data are constructed explicitly. -/
@[irreducible] noncomputable def residueExchangeRestrictPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeRestriction ℓ E Y ⋙ residueExchangeUpperStar (integralCoeff ℓ E) f ≅
      residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f ⋙
        residueExchangeRestriction ℓ E X := by
  unfold residueExchangeUpperStar
  exact Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (integralCoeff ℓ E) f) ≪≫
    (derivedComapUpperStarIso (integralReductionMap ℓ E) f).symm ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).symm _

/-- The scalar-extension/pullback comparison is constructed as the inverse mate of
exact restriction/pullback. Invertibility is a property, not chosen data. -/
@[irreducible] noncomputable def residueExchangePullHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeUpperStar (integralCoeff ℓ E) f ⋙ residueExchangeReduction ℓ E X ⟶
      residueExchangeReduction ℓ E Y ⋙
        residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f :=
  ((mateEquiv (residueExchangeReductionAdjunction ℓ E Y)
      (residueExchangeReductionAdjunction ℓ E X)).symm
    (TwoSquare.mk _ _ _ _ (residueExchangeRestrictPullIso ℓ E f).hom)).natTrans

/-- The derived reduction counit with its actual reduction functor exposed. -/
@[irreducible] noncomputable def residueExchangeReductionCounit (T : Scheme.{u}) :
    DerivedCategory.Qh ⋙ residueExchangeReduction ℓ E T ⟶
      (Mod.extendScalars
        (coefficientMap (integralReductionMap ℓ E) T)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh := by
  unfold residueExchangeReduction integralReduction
  exact (Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) T)).leftDerivedFunctorCounit

/-- The exact pullback counit with its typed derived pullback exposed. -/
@[irreducible] noncomputable def residueExchangeUpperStarCounit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙ residueExchangeUpperStar Λ f ⟶
      ((f)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
  unfold residueExchangeUpperStar
  exact ((f)^*⟦Λ⟧).leftDerivedFunctorCounit

end AlgebraicGeometry.ProEtale.CondensedRing
