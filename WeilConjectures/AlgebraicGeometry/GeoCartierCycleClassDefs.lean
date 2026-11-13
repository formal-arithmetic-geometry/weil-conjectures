/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf

/-!
# The cycle class of an effective Cartier divisor

We use the fixed-scalar sheaf presentation of ordinary pro-etale modules, canonically
realized by `finiteCoefficientRealization` over the coefficient ring sheaf. `Ext.homEquiv`
identifies every degree-two Ext class below with the displayed morphism from the degree-zero
supported constant object to its finite Tate line shifted by two. No condensed or completed
coefficient category occurs. The auxiliary definitions only spell out this class and its
normalization diagrams.

## References

* Stacks, Tag 03PL
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Cached instance for the smallness of Ext in the sheaf category used by integral
pro-etale Ext classes. -/
instance (priority := 10000) geoCartierIntegralExt (Z : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1}) := by
  infer_instance

/-- Cached instance for the smallness of finite-coefficient pro-etale Ext. -/
instance (priority := 10000) geoCartierModuleExt
    (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) := by
  infer_instance

/-- The ordinary pro-etale constant module used in the Cartier class. -/
def geoCartierConstant (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) :=
  (constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

/-- The finite Tate line is exactly comparison inverse image of the etale roots tensor. -/
def geoCartierLine (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (Z : Scheme.{u}) : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj
    (Scheme.finiteEtaleTateLine Z N A hA)

/-- The supported cycle class, represented through the canonical degree-two Ext/Hom
bijection. Its source uses ordinary closed direct image, not an arbitrary support object. -/
abbrev GeoCartierClass (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) :=
  Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D))
    (geoCartierLine A N hA Z) 2

/-- The comparison on the ordinary supported constant, with its canonical mate and
constant-sheaf identification. Invertibility is asserted in the main statement. -/
@[irreducible]
def geoCartierSourceComparison (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D) :=
  (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)).app
      (Etale.ordinaryFiniteConstant A D) ≫
    (lowerStar (ModuleCat.{u + 1} A) i).map
      ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom

/-- The direct image of the constant-sheaf comparison, typed with the Cartier constant as
target, is invertible. -/
instance geoCartierSourceConstant_isIso (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) :
    IsIso ((lowerStar (ModuleCat.{u + 1} A) i).map
      ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom :
        _ ⟶ (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)) := by
  unfold geoCartierConstant
  infer_instance

end AlgebraicGeometry.ProEtale
