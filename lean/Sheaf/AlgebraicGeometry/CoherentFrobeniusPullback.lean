/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyCoefficientTransport
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison

/-! Frobenius naturality for the fixed coherent pullback. -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Structural coherent pullback commutes with the supplied additive power maps.
Source: Stacks Project, Tags 01FB, 03FD and 06XR.
(blueprint: new-coherent-frobenius-pullback).

Proof: Write E and E' for the fixed module/Ext resolution comparisons. Coefficient
transport, coefficient naturality of E and the fixed identity-edge comparison give
E' fmap = H(coeff) H.mapFunctor E for the structural module coefficient map.
The adjoint of coeff is the underlying structural map of regular functions.
Since j#(s^p) = j#(s)^p, adjunction turns this equality into
invImage.map FrZ followed by coeff = coeff followed by FrZK. The exact-functor
Ext naturality square, with the constant-integer-sheaf comparison, therefore
commutes with both powers. Ext universe transport commutes with coefficient
postcomposition, by the common derived-Hom description of Ext. Consequently the
same square holds for the large presentation used in coherentAdditiveEndomorphism.
Conjugate the square by E and E' and cancel E', which is injective. This proves
the displayed equality for every module cohomology class. Neither properness nor
flatness is required. The argument includes degree zero and empty schemes. -/
theorem coherentFrobenius_pullback
    {X Y : Scheme.{u}} (j : Y ⟶ X) (p q : ℕ)
      (FrZ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X) ⟶
        (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X))
      (FrZK : (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).obj (unit Y) ⟶
        (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).obj (unit Y))
      (hFrZ : ∀ (U : X.Opensᵒᵖ) (s : Γ(X, U.unop)), FrZ.hom.app U s = s ^ p)
      (hFrZK : ∀ (U : Y.Opensᵒᵖ) (s : Γ(Y, U.unop)), FrZK.hom.app U s = s ^ p)
      (v : (RingedSpace.moduleCohomology X.toRingedSpace q).obj (unit X)) :
      coherentAdditiveEndomorphism Y (unit Y) q FrZK
        (moduleCohomologyFMap j
          (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) q v) =
        moduleCohomologyFMap j
          (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) q
            (coherentAdditiveEndomorphism X (unit X) q FrZ v) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
