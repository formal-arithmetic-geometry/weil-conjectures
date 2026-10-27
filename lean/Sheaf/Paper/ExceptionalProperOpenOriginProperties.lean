/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.ExceptionalSystemInterfaces

/-! # Bounded-origin properties of a proper/open strict-system comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
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

/-- The canonical proper/open comparison has the bounded-origin properties.
Source: Zheng Construction 5.15 and Lemmas 4.10, 5.16 and 5.22; Stacks 0B65.
(blueprint: lem-sf-exceptional-proper-open-origin-properties).

Proof: the finite proper mate is invertible on bounded-below inputs, and exact
evaluation transports this fact to strict systems.  The site equivalence clauses
transport origins through the open and proper factors.  For a finite origin, the
right etale adjoint is bounded below by the uniform cohomological bound.  Finally,
substituting the proper mate and the open evaluation square into the mate word,
and cancelling the unit and counit identities, gives the displayed equality of
actual derived morphisms. -/
theorem exceptionalProperOpenOriginProperties
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (hX : ExceptionalSystemSiteEquivalence CX)
    (hY : ExceptionalSystemSiteEquivalence CY)
    (hZ : ExceptionalSystemSiteEquivalence CZ)
    (P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
    (R : ExceptionalSystemCompactificationComparison S CX CY CZ P) :
      (∀ M, (∃ a : ℤ, M.IsGE a) →
        IsIso ((exceptionalSystemComparison R).app M)) ∧
      (∀ M, CX.origin M → CY.origin ((exceptionalProSupport P).obj M)) ∧
      (∀ n M, CX.levelOrigin n M → CY.levelOrigin n
        ((P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).obj M)) ∧
      (∀ n M, CX.levelOrigin n M →
        IsIso ((exceptionalSystemLevelOriginComparison R n).app M)) ∧
      (∀ n N, CY.levelOrigin n N →
        ∃ a : ℤ, ((G.levelRight n).obj ((CY.image.level n).direct.obj N)).IsGE a) ∧
    (∀ n M,
    (CY.proEvaluation.evaluation n).map ((exceptionalSystemComparison R).app M) ≫
      (exceptionalProSupportEvaluation P n).hom.app (CX.image.system.inverse.obj M) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((CX.image.inverseEvaluation n).hom.app M) =
    (CY.image.inverseEvaluation n).hom.app (S.functor.obj M) ≫
      (CY.image.level n).inverse.map ((S.evaluation n).hom.app M) ≫
      (exceptionalSystemLevelComparison R n).app ((S.PX.evaluation n).obj M)) := by
  sorry

end AlgebraicGeometry
