/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # The standard linear action on projective space

Source: Milne, Algebraic Groups (2017), Theorem 4.27 and Remark 4.30, pp.94--96;
Section 7g, pp.146--148; proof of Theorem 17.65, p.374.
(blueprint: def-sfb-standard-projective-linear-action)

The homogeneous substitution specifies the action on the whole scheme, including nilpotents.
Projective space parametrizes lines in the coordinate vector space.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MvPolynomial

namespace AlgebraicGeometry

attribute [instance] MvPolynomial.gradedAlgebra

/-- Polynomial Proj over the field, with homogeneous coordinates indexed by n.
It parametrizes lines in kⁿ, equivalently quotient lines of its dual.
Source: Milne, Section 7g, pp.146--148.
(blueprint: def-sfb-standard-projective-linear-action). -/
def linearProjectiveSpace (k : Type u) [Field k] (n : Type u) : Over (Spec (.of k)) :=
  Over.mk (Proj.projectiveSpaceOverAffineToSpec n k)

/-- Pullback of the homogeneous coordinates under matrix multiplication on column vectors.
Source: Milne, Theorem 4.27 and Remark 4.30, pp.94--96.
(blueprint: def-sfb-standard-projective-linear-action). -/
def projectiveLinearCoaction (k : Type u) [Field k] (n : Type u)
    [Fintype n] [DecidableEq n] :
    MvPolynomial n k →+* MvPolynomial n (Matrix.GeneralLinearGroup.CoordinateRing n k) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap k _))
    (fun i ↦ ∑ j, MvPolynomial.C (Matrix.GeneralLinearGroup.coord n k i j) * MvPolynomial.X j)

/-- The standard GL action is characterized by zᵢ ↦ ∑ⱼ xᵢⱼzⱼ.
Both projections fix the affine base-change comparison uniquely; the entire graded maps,
including coefficients, are prescribed. This is a predicate, with no chosen action or proof.
Source: Milne, Section 7g and proof of Theorem 17.65, pp.146--148, 374.
(blueprint: def-sfb-standard-projective-linear-action). -/
def IsStandardProjectiveLinearAction (k : Type u) [Field k] (n : Type u)
    [Fintype n] [DecidableEq n]
    (a : ModObj (GeneralLinearGroup n k) (linearProjectiveSpace k n)) : Prop :=
  ∃ φ ψ : homogeneousSubmodule n k →+*ᵍ
      homogeneousSubmodule n (Matrix.GeneralLinearGroup.CoordinateRing n k),
    φ.toRingHom = projectiveLinearCoaction k n ∧
    ψ.toRingHom = MvPolynomial.map (algebraMap k (Matrix.GeneralLinearGroup.CoordinateRing n k)) ∧
    ∃ (hφ : HomogeneousIdeal.irrelevant
          (homogeneousSubmodule n (Matrix.GeneralLinearGroup.CoordinateRing n k)) ≤
        (HomogeneousIdeal.irrelevant (homogeneousSubmodule n k)).map φ)
      (hψ : HomogeneousIdeal.irrelevant
          (homogeneousSubmodule n (Matrix.GeneralLinearGroup.CoordinateRing n k)) ≤
        (HomogeneousIdeal.irrelevant (homogeneousSubmodule n k)).map ψ),
      ∃ e : Proj.projectiveSpaceOverAffine n (Matrix.GeneralLinearGroup.CoordinateRing n k) ≅
          (GeneralLinearGroup n k ⊗ linearProjectiveSpace k n).left,
        e.hom ≫ (fst (GeneralLinearGroup n k) (linearProjectiveSpace k n)).left =
          Proj.projectiveSpaceOverAffineToSpec n (Matrix.GeneralLinearGroup.CoordinateRing n k) ∧
        e.hom ≫ (snd (GeneralLinearGroup n k) (linearProjectiveSpace k n)).left = Proj.map ψ hψ ∧
        e.hom ≫ a.smul.left = Proj.map φ hφ

end AlgebraicGeometry
