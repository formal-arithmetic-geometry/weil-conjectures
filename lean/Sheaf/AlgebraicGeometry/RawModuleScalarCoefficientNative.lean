/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientFactors

/-! # The canonical module coefficient map at named raw-complex endpoints

Source: Stacks Project, Tag 03Q8; the existing canonical coefficient factor.
(blueprint: def-sbc-module-coefficient-native-endpoints).
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The existing coefficient morphism with its named raw-complex endpoints.
Source: Stacks Project, Tag 03Q8; `moduleCoefficientFactor`.

Construction: the canonical factor `moduleCoefficientFactor` itself, read at the
definitionally equal named raw-complex endpoints `higherDirectImageRawOverComplex`, so
that these endpoints stay shared. It is an abbreviation of the canonical factor, not a
second definition; the following computation rule unfolds it to the shift comparison
followed by the shifted fixed coefficient morphism, for every integer degree, including
zero, and every Over arrow.
(blueprint: def-sbc-module-coefficient-native-endpoints). -/
noncomputable abbrev moduleCoefficientFactorNative
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.obj
        ((higherDirectImageRawOverComplex Λ G B)⟦q⟧) ⟶
      (higherDirectImageRawOverComplex Λ G A)⟦q⟧ :=
  moduleCoefficientFactor Λ G q A B f

/-- The typed view is the canonical coefficient map itself.
Source: Stacks Project, Tag 03Q8; the preceding abbreviation.
Proof: the abbreviation unfolds to the canonical factor at definitionally equal endpoint
types, so heterogeneous reflexivity proves the equation.
(blueprint: def-sbc-module-coefficient-native-endpoints). -/
theorem moduleCoefficientFactorNative_heq
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    HEq (moduleCoefficientFactorNative Λ G q A B f)
      (moduleCoefficientFactor Λ G q A B f) := by
  rfl

/-- The explicit two-factor computation rule at the named raw-complex endpoints.
Source: Stacks Project, Tag 03Q8; the coefficient part of raw triangle pullback.
Proof: unfold the abbreviation, `moduleCoefficientFactor` and the moduleUpperStar
abbreviation; both sides are the identical composite.
(blueprint: def-sbc-module-coefficient-native-endpoints). -/
theorem moduleCoefficientFactorNative_eq
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    moduleCoefficientFactorNative Λ G q A B f =
  ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      (higherDirectImageRawOverComplex Λ G B) ≫
    (shiftFunctor _ q).map (higherDirectImageRawOverCoefficient Λ G f) := by
  rfl

end AlgebraicGeometry.Etale
