/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.DiagonalProjectiveAction
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Projectivization of a rational multiplicative-group representation

Source: Milne, Algebraic Groups (2017), 7.26 and Lemma 13.46, pp.145,272.
(blueprint: def-sfb-projectivized-gm-representation).

The coordinates parametrize lines, and the substitution is z_i ↦ Σ_j rho_ij z_j.
The comparison with the product is fixed by both projections. This specifies scheme
morphisms and therefore the action on all test algebras, including nonreduced ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MvPolynomial

namespace AlgebraicGeometry.ProjectivizedGmRepresentation

attribute [instance] MvPolynomial.gradedAlgebra

/-- The universal matrix of rho, evaluated on the universal Laurent-valued point of Gm.
Source: Milne 7.26 (blueprint: def-sfb-projectivized-gm-representation). -/
def matrix {F : Type u} [Field F] {n : ℕ}
    (rho : StandardGroupSchemes.multiplicative F ⟶
      GeneralLinearGroup (ULift.{u} (Fin (n + 1))) F) :
    Matrix.GeneralLinearGroup (ULift.{u} (Fin (n + 1))) (LaurentPolynomial F) :=
  GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin (n + 1))) F (LaurentPolynomial F) rho

/-- Actual homogeneous-coordinate substitution for the action on lines.
Source: Milne 7.26 and 13.46 (blueprint: def-sfb-projectivized-gm-representation). -/
def coaction {F : Type u} [Field F] {n : ℕ}
    (rho : StandardGroupSchemes.multiplicative F ⟶
      GeneralLinearGroup (ULift.{u} (Fin (n + 1))) F) :
    MvPolynomial (ULift.{u} (Fin (n + 1))) F →+*
      MvPolynomial (ULift.{u} (Fin (n + 1))) (LaurentPolynomial F) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap F (LaurentPolynomial F)))
    (fun i ↦ ∑ j, MvPolynomial.C (matrix rho i j) * MvPolynomial.X j)

/-- The projective action is induced by rho precisely when its map is Proj of the
specified coordinate substitution under the canonical affine-base-change comparison.
The representation's group-homomorphism condition is IsMonHom rho at the use site.
Source: Milne 7.26 and Lemma 13.46 (blueprint: def-sfb-projectivized-gm-representation). -/
def IsProjectivization {F : Type u} [Field F] {n : ℕ}
    (rho : StandardGroupSchemes.multiplicative F ⟶
      GeneralLinearGroup (ULift.{u} (Fin (n + 1))) F)
    (a : ModObj (StandardGroupSchemes.multiplicative F)
      (DiagonalProjectiveAction.space F n)) : Prop :=
  ∃ phi psi : homogeneousSubmodule (ULift.{u} (Fin (n + 1))) F →+*ᵍ
      homogeneousSubmodule (ULift.{u} (Fin (n + 1))) (LaurentPolynomial F),
    phi.toRingHom = coaction rho ∧
    psi.toRingHom = MvPolynomial.map (algebraMap F (LaurentPolynomial F)) ∧
    ∃ (hphi : HomogeneousIdeal.irrelevant
          (homogeneousSubmodule (ULift.{u} (Fin (n + 1))) (LaurentPolynomial F)) ≤
        (HomogeneousIdeal.irrelevant
          (homogeneousSubmodule (ULift.{u} (Fin (n + 1))) F)).map phi)
      (hpsi : HomogeneousIdeal.irrelevant
          (homogeneousSubmodule (ULift.{u} (Fin (n + 1))) (LaurentPolynomial F)) ≤
        (HomogeneousIdeal.irrelevant
          (homogeneousSubmodule (ULift.{u} (Fin (n + 1))) F)).map psi),
      ∃ e : Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1)))
          (LaurentPolynomial F) ≅
          (StandardGroupSchemes.multiplicative F ⊗
            DiagonalProjectiveAction.space F n).left,
        e.hom ≫ (fst (StandardGroupSchemes.multiplicative F)
            (DiagonalProjectiveAction.space F n)).left =
          Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1)))
            (LaurentPolynomial F) ∧
        e.hom ≫ (snd (StandardGroupSchemes.multiplicative F)
            (DiagonalProjectiveAction.space F n)).left =
          Proj.map psi hpsi ∧
        e.hom ≫ a.smul.left = Proj.map phi hphi

end AlgebraicGeometry.ProjectivizedGmRepresentation
