/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.AffineEtaleNaiveCotangentPresentation
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Projective space and its standard twist over an algebraic space

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 08AQ,
lemma-kill-by-twisting; Spaces, Tag 04T9; Descent, Tags 03DX and 03FH
(blueprint: def-sfb-space-projective-twist).

The construction is the sheaf product over the ambient scheme with its projective
space, hence the base change of integral projective space. The standard line module
is the pullback of the existing standard twist through canonical tensor extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme projective space over the ambient base, with n+1 homogeneous coordinates.
Source: Stacks, Tag 08AQ, projective space in the diagram
(blueprint: def-sfb-space-projective-twist). -/
def projectiveSpaceModel (S : Scheme.{u}) (n : ℕ) : Over S :=
  Over.mk (ProjectiveSpace (ULift.{u} (Fin (n + 1))) S ↘ S)

/-- The sheaf product over S is the base change of integral projective space to Y.
Source: Stacks, Spaces, Tag 04T9, and Tag 08AQ
(blueprint: def-sfb-space-projective-twist).
Proof: the product of two sheaves on Sch/S is their fibre product over the terminal
representable S. The two representable diagonals give a representable diagonal for
this product. The product over S of scheme atlases is a scheme and gives a
surjective etale atlas, by base change and composition of etale surjections.
Thus the product is an algebraic space, including when Y is empty. -/
theorem projectiveSpaceSheaf_isAlgebraicSpace {S : Scheme.{u}}
    (Y : AlgebraicSpace S) (n : ℕ) :
    IsAlgebraicSpace (Y.obj ⨯ (schemeSpace (projectiveSpaceModel S n)).obj) := by
  sorry

/-- Projective n-space over Y, as Y times_S projective n-space over S.
Since the latter is S times_Spec(Z) projective n-space over Z, this is precisely
Y times_Spec(Z) projective n-space over Z.
Source: Stacks, Tag 08AQ (blueprint: def-sfb-space-projective-twist). -/
def projectiveSpaceOver {S : Scheme.{u}} (Y : AlgebraicSpace S) (n : ℕ) :
    AlgebraicSpace S :=
  ⟨Y.obj ⨯ (schemeSpace (projectiveSpaceModel S n)).obj,
    projectiveSpaceSheaf_isAlgebraicSpace Y n⟩

/-- The structure projection of projective space over Y.
Source: Stacks, Tag 08AQ (blueprint: def-sfb-space-projective-twist). -/
def projectiveSpaceProjection {S : Scheme.{u}} (Y : AlgebraicSpace S) (n : ℕ) :
    projectiveSpaceOver Y n ⟶ Y :=
  ObjectProperty.homMk prod.fst

/-- The other projection, used to pull back the fixed standard twist.
Source: Stacks, Tag 08AQ (blueprint: def-sfb-space-projective-twist). -/
def projectiveSpaceModelProjection {S : Scheme.{u}} (Y : AlgebraicSpace S) (n : ℕ) :
    projectiveSpaceOver Y n ⟶ schemeSpace (projectiveSpaceModel S n) :=
  ObjectProperty.homMk prod.snd

/-- The standard O(1), first extended from Zariski to etale modules by the canonical
left adjoint to actual Zariski restriction, then pulled back along the second projection.
The scheme twist is itself the fixed pullback of the integral standard twist.
Source: Stacks, Tags 03DX, 03FH and 08AQ
(blueprint: def-sfb-space-projective-twist). -/
def projectiveSpaceTwistOne {S : Scheme.{u}} (Y : AlgebraicSpace S) (n : ℕ) :
    (projectiveSpaceOver Y n).Modules :=
  (moduleTensorPullback (projectiveSpaceModelProjection Y n)).obj
    ((schemeSpace (projectiveSpaceModel S n)).smallModuleEquivalence.inverse.obj
      ((representedSchemeModuleExtension (projectiveSpaceModel S n)).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) S 1)))

end AlgebraicGeometry.AlgebraicSpace
