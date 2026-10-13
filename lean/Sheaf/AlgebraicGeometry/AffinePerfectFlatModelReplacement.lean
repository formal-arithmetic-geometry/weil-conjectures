/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Affine perfect replacement with a chain-level comparison -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A bounded-above quasi-coherent complex representing a perfect object on an
affine scheme has a bounded finite-projective replacement mapping quasi-isomorphically
to it. Only the structural properties of the replacement and the comparison map
are asserted; no direct-image or universal cohomology conclusion is asserted.
Source: Stacks Project, Tags 08EB, 0656 and 0647.
(blueprint: lem-pc-affine-perfect-flat-model-replacement).

Proof: Identify Y with Spec Gamma(Y,O). Under the affine derived equivalence the
complex of sections of D corresponds to D, since its quasi-coherent terms are
acyclic for global sections. Tag 08EB transfers perfectness to that ring complex.
Tag 0656 gives a bounded complex P of finite projective modules representing it.
Such a complex is K-projective (Tag 0647), so the derived isomorphism from P to the
section complex is represented by a chain map. This map is a quasi-isomorphism
because its localization is invertible. Associate sheaves termwise and use the
quasi-coherent counit to obtain e : C -> D, still a quasi-isomorphism. The terms
of C are direct summands of finite free modules, hence flat, quasi-coherent and
finitely presented. Transfer P's bounds, enlarging the upper bound to a natural
number. For the empty scheme or a zero complex choose the zero complex and
zero map, which is a quasi-isomorphism in the trivial or acyclic case. The object
C is asserted existentially, never defined by choosing an unproved witness. -/
theorem exists_affine_perfect_flat_model_replacement
    (Y : Scheme.{u}) (hY : IsAffine Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    (D : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hDle : D.IsStrictlyLE d)
    (hDqc : ∀ n : ℤ, (D.X n).IsQuasicoherent)
    (hperfect : Y.IsPerfect ((DerivedCategory.Q
      (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))).obj D)) :
    ∃ (C : CochainComplex Y.Modules ℤ) (a : ℤ) (b : ℕ),
      C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 Y)) ∧
      (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧
      (∀ n : ℤ, (C.X n).IsFinitePresentation) ∧
      ∃ e : C ⟶ D, QuasiIso e := by sorry

end AlgebraicGeometry.Scheme.Modules
