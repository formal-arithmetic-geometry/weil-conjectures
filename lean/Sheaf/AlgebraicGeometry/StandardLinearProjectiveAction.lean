/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # The standard linear action on projective space

Source: Milne, Algebraic Groups (2017), Section 7e, definition of a linear action;
Stacks, Constructions, Section 01ND, polynomial Proj.
(blueprint: def-sfb-standard-linear-projective-action).

The universal matrix substitution specifies the action on schemes, including nilpotents.
Both projections pin the affine base-change comparison uniquely.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory MvPolynomial

namespace AlgebraicGeometry.StandardLinearProjectiveAction

attribute [instance] MvPolynomial.gradedAlgebra

/-- The universal matrix substitution z_i ↦ ∑_j x_ij z_j, fixing base coefficients.
Source: Milne (2017), Section 7e, standard projective linear action.
(blueprint: def-sfb-standard-linear-projective-action). -/
def coaction (k : Type u) [CommRing k] (I : Type u) [Fintype I] [DecidableEq I] :
    MvPolynomial I k →+* MvPolynomial I (Matrix.GeneralLinearGroup.CoordinateRing I k) :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (algebraMap k (Matrix.GeneralLinearGroup.CoordinateRing I k)))
    (fun i ↦ ∑ j, MvPolynomial.C (Matrix.GeneralLinearGroup.coord I k i j) * MvPolynomial.X j)

/-- An action of GL on the polynomial Proj is standard when its action morphism, under
canonical affine base change, is Proj of the universal matrix substitution. The other
substitution fixes the variables and extends coefficients, hence specifies the second
projection. The first projection is the structure map to Spec k[GL]. This is the action
on lines in k^I, rather than the contragredient action on lines in its dual.
Source: Milne (2017), Section 7e; Stacks, Constructions, Section 01ND.
(blueprint: def-sfb-standard-linear-projective-action). -/
def IsStandard (k : Type u) [CommRing k] (I : Type u) [Fintype I] [DecidableEq I]
    (a : ModObj (GeneralLinearGroup I k)
      (Over.mk (Proj.projectiveSpaceOverAffineToSpec I k))) : Prop :=
  ∃ φ ψ : homogeneousSubmodule I k →+*ᵍ
      homogeneousSubmodule I (Matrix.GeneralLinearGroup.CoordinateRing I k),
    φ.toRingHom = coaction k I ∧
    ψ.toRingHom = MvPolynomial.map
      (algebraMap k (Matrix.GeneralLinearGroup.CoordinateRing I k)) ∧
    ∃ (hφ : HomogeneousIdeal.irrelevant
          (homogeneousSubmodule I (Matrix.GeneralLinearGroup.CoordinateRing I k)) ≤
        (HomogeneousIdeal.irrelevant (homogeneousSubmodule I k)).map φ)
      (hψ : HomogeneousIdeal.irrelevant
          (homogeneousSubmodule I (Matrix.GeneralLinearGroup.CoordinateRing I k)) ≤
        (HomogeneousIdeal.irrelevant (homogeneousSubmodule I k)).map ψ),
      ∃ e : Proj.projectiveSpaceOverAffine I (Matrix.GeneralLinearGroup.CoordinateRing I k) ≅
          ((GeneralLinearGroup I k) ⊗
            Over.mk (Proj.projectiveSpaceOverAffineToSpec I k)).left,
        e.hom ≫ (fst (GeneralLinearGroup I k)
            (Over.mk (Proj.projectiveSpaceOverAffineToSpec I k))).left =
          Proj.projectiveSpaceOverAffineToSpec I (Matrix.GeneralLinearGroup.CoordinateRing I k) ∧
        e.hom ≫ (snd (GeneralLinearGroup I k)
            (Over.mk (Proj.projectiveSpaceOverAffineToSpec I k))).left = Proj.map ψ hψ ∧
        e.hom ≫ a.smul.left = Proj.map φ hφ

end AlgebraicGeometry.StandardLinearProjectiveAction
