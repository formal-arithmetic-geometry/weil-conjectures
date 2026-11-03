/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalTateCoprojectionCoherence
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import Mathlib.FieldTheory.Perfect

/-! # Cancellation of oriented dualizing Tate twists

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/sk-thm-regular.proof.md,
Steps 1--2 (blueprint: lem-pur-regular-dualizing-twist-cancellation).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The co-projection with a coefficient-unit first factor, used to make the displayed `q`
and `Phi` land in the exact objects of the statement.
Source: Step 1 of the cited proof (blueprint: lem-pur-regular-dualizing-twist-cancellation). -/
noncomputable def regularCoprojectionIso
    (A : Type (u + 1)) [CommRing A] [Finite A] [HasTateTwist A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] [HasInvertibleExponent A X]
    [HasInvertibleExponent A Z] (r : ℤ) :
    (rightDerivedUpperShriek A i).obj (shiftedTateObject A X r) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
        ((rightDerivedUpperShriek A i).obj (constantComplex A X))).obj
        (shiftedTateObject A Z r) :=
  (rightDerivedUpperShriek A i).mapIso
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X
        (shiftedTateObject A X r)).symm ≪≫
    exceptionalTateCoprojection A i (constantComplex A X) r

/-- The first composite in the cancellation argument. It is the displayed `q`: the two
specified orientations, followed by the actual exceptional inverse image and co-projection.
Source: Step 1 of the cited proof (blueprint: lem-pur-regular-dualizing-twist-cancellation). -/
noncomputable def regularDualizingQIso
    (A : Type (u + 1)) [CommRing A] [Finite A] [HasTateTwist A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] [HasInvertibleExponent A X]
    [HasInvertibleExponent A Z] (m n : ℤ)
    (W_X : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (W_Z : _root_.DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (b : W_Z ≅ (rightDerivedUpperShriek A i).obj W_X)
    (P_X : W_X ≅ shiftedTateObject A X n)
    (P_Z : W_Z ≅ shiftedTateObject A Z m) :
    shiftedTateObject A Z m ≅
      ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
        ((rightDerivedUpperShriek A i).obj (constantComplex A X))).obj
        (shiftedTateObject A Z n) :=
  P_Z.symm ≪≫ b ≪≫ (rightDerivedUpperShriek A i).mapIso P_X ≪≫
    regularCoprojectionIso A i n

/-- Tensor the first composite by the inverse `m`-twist and use Tate additivity. This is the
specified `q'` from the node statement.
Source: Step 2 of the cited proof (blueprint: lem-pur-regular-dualizing-twist-cancellation). -/
noncomputable def regularDualizingQPrimeIso
    (A : Type (u + 1)) [CommRing A] [Finite A] [HasTateTwist A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] [HasInvertibleExponent A X]
    [HasInvertibleExponent A Z] (m n c : ℤ) (h : n = m + c)
    (W_X : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (W_Z : _root_.DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (b : W_Z ≅ (rightDerivedUpperShriek A i).obj W_X)
    (P_X : W_X ≅ shiftedTateObject A X n)
    (P_Z : W_Z ≅ shiftedTateObject A Z m) :
    constantComplex A Z ≅
      ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
        ((rightDerivedUpperShriek A i).obj (constantComplex A X))).obj
        (shiftedTateObject A Z c) :=
  by
    let q := regularDualizingQIso A i m n W_X W_Z b P_X P_Z
    let e₀ : constantComplex A Z ≅
        ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
          (shiftedTateObject A Z m)).obj (shiftedTateObject A Z (-m)) :=
      (shiftedTateZeroIso A Z).symm ≪≫
        eqToIso (by simp [shiftedTateObject]) ≪≫
        (shiftTateObjectAddIso A Z m (-m)).symm
    exact e₀ ≪≫
      ((derivedTensor (ModuleCat.{u + 1} A) Z).mapIso q).app _ ≪≫
      derivedTensorAssociator (ModuleCat.{u + 1} A) Z
        ((rightDerivedUpperShriek A i).obj (constantComplex A X))
        (shiftedTateObject A Z n) (shiftedTateObject A Z (-m)) ≪≫
      ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
        ((rightDerivedUpperShriek A i).obj (constantComplex A X))).mapIso
        (shiftTateObjectAddIso A Z n (-m)) ≪≫
      ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
        ((rightDerivedUpperShriek A i).obj (constantComplex A X))).mapIso
        (eqToIso (by rw [h]; simp [shiftedTateObject]))

end AlgebraicGeometry.Etale
