/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalSystemInterfaces

/-! # Scalar actions for exceptional pro-etale operations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (G : StrictEtaleExceptionalAdjoint O ell c S)
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)
  (P : ExceptionalProCompactSupport O ell c
    CX.proEvaluation CY.proEvaluation CZ.proEvaluation)

/-- Canonical scalar actions on the pro-etale compact-support and transported right
functors, together with their compatibility equations.
Source: Zheng Proposition 2.29(2), Construction 5.15 and Lemma 5.22.
(blueprint: lem-sf-exceptional-pro-origin-scalar-actions).

Proof: define multiplication by the image of each scalar on every quotient
coefficient sheaf and localize the resulting ordinary natural transformations.
The inverse-image, open-extension, proper-derived and etale right-adjoint
comparison equations transport these transformations through the two composites.
The localization universal property upgrades the representative equalities to
all derived objects, yielding both displayed linearity equations. -/
theorem exceptionalProScalarActions :
    ∃ (scalarX : ExceptionalProScalarAction X O ell)
      (scalarY : ExceptionalProScalarAction Y O ell),
      (∀ r M, (exceptionalProSupport P).map ((scalarX.derived r).app M) =
        (scalarY.derived r).app ((exceptionalProSupport P).obj M)) ∧
      (∀ r N, (exceptionalSystemRight G CX CY).map ((scalarY.derived r).app N) =
        (scalarX.derived r).app ((exceptionalSystemRight G CX CY).obj N)) := by
  sorry

end AlgebraicGeometry
