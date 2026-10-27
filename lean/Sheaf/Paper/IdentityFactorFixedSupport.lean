/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.Paper.CompactSupportSiteCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk

/-! # Identity factors in fixed-scalar compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The actual open/proper pair, without introducing a chosen compactification.
Source: compactification formula, def-sf-operation-stages
(blueprint: lem-sf-identity-factor-fixed-support). -/
def identityFactorPair {X Z Y : Scheme.{u}} (i : X ⟶ Z) (p : Z ⟶ Y)
    [IsOpenImmersion i] [IsProper p] : Compactification (i ≫ p) where
  Z := Z
  i := i
  g := p
  comm := rfl
  isOpenImmersion := inferInstance
  isProper := inferInstance

/-- Remove the identity open extension in the proper compactification.
Source: adjunction identity law, def-sf-operation-stages
(blueprint: lem-sf-identity-factor-fixed-support). -/
def identityFactorFixedProper (Λ : Type (u + 1)) [CommRing Λ]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (Compactification.ofIsProper p) ≅
      (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekIdIso _ Z) ≪≫
      Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _

/-- Remove the identity direct image in the open compactification.
Source: adjunction identity law, def-sf-operation-stages
(blueprint: lem-sf-identity-factor-fixed-support). -/
def identityFactorFixedOpen (Λ : Type (u + 1)) [CommRing Λ]
    {X Z : Scheme.{u}} (i : X ⟶ Z) [IsOpenImmersion i] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (Compactification.ofIsOpenImmersion i) ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (rightDerivedLowerStarId (ModuleCat.{u + 1} Λ) Z) ≪≫
    Functor.rightUnitor _

/-- The two identity-factor unit maps, in their order of application.
Source: identity open extension followed by identity direct image
(blueprint: lem-sf-identity-factor-fixed-support). -/
def identityFactorFixedIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Z Y : Scheme.{u}} (i : X ⟶ Z) (p : Z ⟶ Y)
    [IsOpenImmersion i] [IsProper p] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (Compactification.ofIsOpenImmersion i) ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (Compactification.ofIsProper p) ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (identityFactorPair i p) :=
  Functor.isoWhiskerLeft _ (identityFactorFixedProper Λ p) ≪≫
    Functor.isoWhiskerRight (identityFactorFixedOpen Λ i) _

/-- The geometric compositor on an etale-origin input is the pair of identity unit maps.
This statement involves no intrinsic coefficient presentation or retained finite witness.

Source: lem-amb-etale-compact-comparisons, the arbitrary-triangle formula; and
lem-pur-compact-support-site-coherence, its composition square.
(blueprint: lem-sf-identity-factor-fixed-support).

Proof: take the triangle with open compactification of i, proper compactification of p,
and actual pair (i,p). Its middle square has four identity edges. The arbitrary-triangle
formula expresses the etale compositor by this triangle. Apply the identity exchange law,
the right unit for open composition and the left unit for proper composition. In the
normalized site-comparison square, the open and proper comparison maps respect these same
identity unit maps: this is the identity law of the extension comparison and the identity
law of the direct-image counit mate. Naturality moves the open comparison through proper
image. Cancel the invertible source boundary to obtain the equation. No nonzero or
nonempty hypothesis enters this calculation. -/
theorem identityFactorFixedCompositor (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z] [IsNoetherian Y]
    (i : X ⟶ Z) (p : Z ⟶ Y) [IsOpenImmersion i] [IsProper p] [QuasiCompact i]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    coherenceProEtaleCompositor Λ (Compactification.ofIsOpenImmersion i)
        (Compactification.ofIsProper p) (identityFactorPair i p) L =
      (identityFactorFixedIso Λ i p).hom.app ((coherenceBoundedSiteFunctor Λ X).obj L) := by sorry

end AlgebraicGeometry.ProEtale
