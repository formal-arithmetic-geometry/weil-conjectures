/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage

/-!
# Class-restricted cohomological dimension

Source: Weil blueprint, sk-prop-sf-existence, def-sf-fullcd-class
(blueprint: def-sf-fullcd-class).
The class is the recorded essential image of etale comparison on sheaves. Its members
are not assumed finite or constructible. Both the absolute and pro-etale-base-change
vanishing quantifiers are retained.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme

/-- FullCD with its all-sheaf quantifier restricted to the specified etale-origin class.
Inverse image on the base-changed source is the exact recorded constant-coefficient
inverse image, and the sheaf is placed in degree zero before deriving direct image.
Source: blueprint, def-sf-fullcd-class (blueprint: def-sf-fullcd-class). -/
def sfClassFullCohomologicalDimension {X Y : Scheme.{u}} (p : X ⟶ Y)
    (A : Type u) [CommRing A] (c : ℕ) : Prop :=
  (∀ (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
      (_hF : (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).essImage F)
      (r : ℤ), (c : ℤ) < r →
    IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F)))) ∧
  ∀ (V : Y.ProEt)
      (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
      (_hF : (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).essImage F)
      (r : ℤ), (c : ℤ) < r →
    IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (pullback.snd p V.hom)).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
              (pullback.fst p V.hom)).obj F))))

end AlgebraicGeometry.ProEtale
