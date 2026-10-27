/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleQuotientTensorProjectionProperFactor
public import Sheaf.Paper.EtaleSystemProjectionData
public import Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor

/-! # Open-factor pasting for the restricted coefficient projection

This assembly step pastes the proper mate projection square with the open
restriction and constant-tensor comparison. It is stated conditionally on the
proper mate square so that the unbounded mate calculation is an independent
intermediate result.
(blueprint: lem-pur-etale-quotient-tensor-projection-open-pasting)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules
namespace AlgebraicGeometry.Etale

/-- Paste the open restriction comparison and the constant tensor maps after a
proper mate projection identity.
Source: Zheng, Proposition 2.29(2), Construction 2.26; Stacks Tag 0GL6.
(blueprint: lem-pur-etale-quotient-tensor-projection-open-pasting).

Proof: use naturality of the open coefficient comparison and of the restriction
mate, then expand the two signed tensor symmetries. The resulting composite is
the defining `exceptionalConstantProjectionMap`.
-/
theorem etaleQuotientTensorProjection_of_proper_mate
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule C X)
    (hproper :
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).map
          ((scalarMate a c.g).app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) ≫
        (scalarRestrictionDirectImageMap a c.g).app
          ((scalarExtension a c.Z).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) =
      (scalarTensorIso a Y).hom.app
          ((lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor.obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} C) c.g).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)).app
          (scalarCoefficient a Y) ≫
        (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor.map
          (((derivedTensor (ModuleCat.{u + 1} C) c.Z).obj
              ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)).map
              (scalarCoefficientPullbackIso a c.g).hom ≫
            (scalarTensorIso a c.Z).inv.app
              ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K))) :
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))
  let e (W : Scheme.{u}) (L : DerivedCategoryModule C W) :=
    (scalarTensorIso a W).app L ≪≫
      ((derivedTensor (ModuleCat.{u + 1} C) W).obj L).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          ((constantCommuteCompose W.smallEtaleTopology
            (ModuleCat.restrictScalars a)).app (ModuleCat.of D D)) ≪≫
          (Functor.mapDerivedCategorySingleFunctor
            (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).symm.app
              ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))) ≪≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} C) W).app L).app
        ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V)
  (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).map
      ((compactScalarMap a c).app K) ≫
    (SystemProjection.singleRestriction (CommRingCat.ofHom a) c).app
      ((scalarExtension a X).obj K) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
      (e X K).hom =
  (e Y ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)).hom ≫
    exceptionalConstantProjectionMap C c V K := by
  sorry

end AlgebraicGeometry.Etale
