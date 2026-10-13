/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage
import Sheaf.Algebra.Homology.BaseChangeRHomPerfect

/-! # Affine global Hom base change out of a proper flat direct image
Source: Stacks Project, Tag 0AA8, right-hand-side computation in case (1).
(blueprint: lem-sc-proper-flat-image-global-hom-base-change-isIso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Base change on affine global Hom out of a proper flat direct image is invertible.
This map only involves derived pullback on the base and scalar extension; there are
no right adjoints or right-adjoint base-change maps in its statement.
Source: Stacks Project, Tag 0AA8, right-hand-side computation, case (1);
Tags 0A1H, 0B91 and 0A6A.
(blueprint: lem-sc-proper-flat-image-global-hom-base-change-isIso).

Proof: compute with the standard K-injective localizations, and transport to the
supplied derived categories by localization equivalences. Apply proper-support
perfect direct image to M and O_X in degree zero. Flatness makes O_X relatively
flat, finite presentation gives its finite presentation, and properness gives proper
support; the tensor unitor identifies the resulting complex with Rf_*M. Thus Rf_*M
is perfect. On the affine bases identify it with a bounded finite-projective complex
P over the global ring A; identify K with an arbitrary complex Q. Derived scalar
extension of Hom(P,Q) is Hom(A' tensor P,A' tensor Q), by perfect RHom base change.
The affine equivalences identify pullback with derived scalar extension. The
K-flat tensorator equations, evaluation mate equation and Leray derived-unit equations
identify the transpose of this algebraic map with mixedGlobalHomPullbackComparison.
The displayed map is therefore this isomorphism. No flatness of g or boundedness
of K is needed. The argument applies to zero M and to empty schemes. -/
theorem properFlatImage_globalHomBaseChange_isIso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {X Y Y' : Scheme.{u}} [IsAffine Y] [IsAffine Y']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M : schemeDerivedQCohCategory X) (hM : Scheme.IsPerfect X M.obj)
    (K : schemeDerivedQCohCategory Y) :
    IsIso (((mixedGlobalExtensionAdjunction g).homEquiv _ _).symm
      (mixedGlobalHomPullbackComparison g ((schemeDerivedDirectImage f).obj M.obj) K.obj)) :=
  by sorry

end AlgebraicGeometry
