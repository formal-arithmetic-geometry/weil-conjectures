/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.AlgebraicGeometry.CartierReductionData
import all Sheaf.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import Sheaf.AlgebraicGeometry.CartierProIntegralResidueDerivedUnit
import Sheaf.AlgebraicGeometry.CartierProIntegralScalar
import Sheaf.AlgebraicGeometry.DerivedScalarExtUnitZero

/-! # Cartier reduction and site comparison
Source: blueprint main-20261015, Cartier comparison proof
(blueprint: lem-sp-cartier-reduction-site-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
attribute [local instance] AlgebraicGeometry.cartierEtaleAbSheafify
  AlgebraicGeometry.cartierProAbSheafify AlgebraicGeometry.cartierEtaleModuleSheafify
  AlgebraicGeometry.cartierProModuleSheafify AlgebraicGeometry.cartierEtaleAbHasExt
  AlgebraicGeometry.cartierProAbHasExt AlgebraicGeometry.cartierEtaleModuleHasExt
  AlgebraicGeometry.cartierProModuleHasExt
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] comparisonUpperStar cartierUnitsComparison
  cartierRootsComparison cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit
  cartierProIntegralGenerator cartierProRootMap cartierReducedEtale cartierReducedPro
  CartierEtaleReductionSpec CartierProReductionSpec cartierResidueReducedPro

/-- Let n>0, R=ULift(Z/n), A a commutative ring killed by n, i:D→Z a closed immersion and φ:R→A. If
Cartier classes cR,cA satisfy GeoCartierScalarCompatibility [sk-lem-geo-cartier], then the pro-etale
supported integral generator i_*Z_D→forget(i_*A_D) is a degree-zero unbounded scalar unit
[def-sfb-cartier-reduction-data, def-sp-derived-scalar-ext-unit].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-cartier-pro-integral-derived-unit).
Proof: Use the supported pro-etale residue quotient unit. Extract from coefficient compatibility the
derived unit on supported constants for extension R→A. Compose the ordinary derived-unit Hom
bijections. Composite coefficient forgetting is definitionally direct forgetting. The normalized
supported integral scalar identity identifies the composite map with the stated integral generator.
Finally the zero-shift comparison identifies its ordinary unit property with the degree-zero
Ext-unit property. -/
theorem pro_integral_derived_unit
    (A : Type (u + 1)) [CommRing A] (n : ℕ) (hn : 0 < n)
    (hA : (n : A) = 0) (hR : (n : ULift.{u + 1} (ZMod n)) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (φ : ULift.{u + 1} (ZMod n) →+* A)
    (cR : GeoCartierClass (ULift.{u + 1} (ZMod n)) n hR i)
    (cA : GeoCartierClass A n hA i)
    (hcompat : GeoCartierScalarCompatibility φ n hR hA i cR cA) :
    CartierScalarUnit (cartierForget A Z)
      ((lowerStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
      ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)) 0
      (Ext.mk₀.{u + 1} (cartierProIntegralGenerator A i)) := by
  let R := ULift.{u + 1} (ZMod n)
  unfold GeoCartierScalarCompatibility at hcompat
  obtain ⟨η, θ, hη, hθ, hηunit, hθunit, hsquare⟩ := hcompat
  let U := Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ
  let V := cartierForget R Z
  let F := (lowerStar AddCommGrpCat.{u + 1} i).obj
    ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let G := (lowerStar (ModuleCat.{u + 1} R) i).obj (geoCartierConstant R D)
  let H := (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)
  let η' : G ⟶ U.obj H := (lowerStar (ModuleCat.{u + 1} R) i).map η
  have hRu := pro_integral_residue_derived_unit n hn i
  unfold GeoCartierScalarUnit at hηunit
  have hηunit' : U.DerivedUnit G H η' := by
    simpa only [Functor.DerivedUnit, Sheaf.IsDerivedBaseChange,
      Sheaf.derivedRestrictScalars, Category.assoc] using hηunit
  have hcomp := Functor.scalar_unit_comp U V F G H
    (cartierProIntegralGenerator R i) η'
    hRu hηunit'
  have hγ := pro_supported_generator_scalar φ i η hη
  change (cartierForget A Z).DerivedUnit F H
    (cartierProIntegralGenerator R i ≫ V.map η') at hcomp
  rw [hγ] at hcomp
  exact hcomp.extUnit_zero
end AlgebraicGeometry.ProEtale
