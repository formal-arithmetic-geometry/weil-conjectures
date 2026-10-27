/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.ExceptionalSystemInterfaces

/-! # Evaluation of the origin adjunction -/

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

variable (P : ExceptionalProCompactSupport O ell c
    CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
  (R : ExceptionalSystemCompactificationComparison S CX CY CZ P)

/-- Evaluation of origin-adjunction Hom words and quotient transitions.
Source: Zheng Lemmas 4.10 and 5.22 and Proposition 5.24; Stacks 0B65.
(blueprint: lem-sf-exceptional-origin-adjunction-evaluation).

Proof: the transpose equations determine the system and finite Hom maps after
precomposition with the respective source site counits. Evaluate these equations,
substitute the comparison evaluation square, and use the three evaluated
adjunctions. The evaluated source counit is the finite counit composed with the
two inverse/direct evaluation comparisons; cancel it, using its invertibility on
origins. Hence evaluation intertwines the forward Hom maps. Apply this identity
to the identity of the left image for the unit, and to the counit for the counit,
using bijectivity of the finite Hom map. For quotient transitions use the actual
etale transition equation before evaluation, then apply the site inverse tensor
comparison. The scalar/site pullback cube identifies its derived tensor map and
the inverse-transition restriction comparison as scalar-adjunction mates. Moving
through this mate square gives exactly the displayed transpose. The intermediate
tensor object may be unbounded, so all transposes are taken in the unbounded
categories. No equality is inferred from agreement at every evaluation. -/
theorem exceptionalOriginAdjunctionEvaluation
    (record : ExceptionalSystemTransportData G CX CY CZ P R)
    (hfinite : ∀ n M, CX.levelOrigin n M →
      IsIso ((CX.image.level n).adjunction.counit.app M))
    (hcomparison :
    (∀ n M,
    (CY.proEvaluation.evaluation n).map ((exceptionalSystemComparison R).app M) ≫
      (exceptionalProSupportEvaluation P n).hom.app (CX.image.system.inverse.obj M) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((CX.image.inverseEvaluation n).hom.app M) =
    (CY.image.inverseEvaluation n).hom.app (S.functor.obj M) ≫
      (CY.image.level n).inverse.map ((S.evaluation n).hom.app M) ≫
      (exceptionalSystemLevelComparison R n).app ((S.PX.evaluation n).obj M))) :
    -- unitEvaluation
    (∀ n M,
    (CX.proEvaluation.evaluation n).map (record.systemAdjunction.adjunction.unit.app M).hom ≫
      (exceptionalSystemRightEvaluation G CX CY n).hom.app
        ((exceptionalProSupport P).obj M.obj) ≫
      ((CY.image.level n).direct ⋙ G.levelRight n ⋙ (CX.image.level n).inverse).map
        ((exceptionalProSupportEvaluation P n).hom.app M.obj) =
    ((record.finiteAdjunction n).adjunction.unit.app
      ⟨(CX.proEvaluation.evaluation n).obj M.obj,
        record.evaluationOriginX n M.obj M.property⟩).hom) ∧
    -- counitEvaluation
    (∀ n N,
    (exceptionalProSupportEvaluation P n).hom.app
        ((exceptionalSystemRight G CX CY).obj N.obj) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((exceptionalSystemRightEvaluation G CX CY n).hom.app N.obj) ≫
      ((record.finiteAdjunction n).adjunction.counit.app
        ⟨(CY.proEvaluation.evaluation n).obj N.obj,
          record.evaluationOriginY n N.obj N.property⟩).hom =
    (CY.proEvaluation.evaluation n).map (record.systemAdjunction.adjunction.counit.app N).hom) ∧
    -- quotientTransition
    (∀ {m n : ℕ} (h : n ≤ m) N,
    (CX.proEvaluation.scalar h).derived.map
        ((exceptionalSystemRightEtaleEvaluation G CX CY m).hom.app N) ≫
      (CX.image.derivedTensor h).inv.app
        ((G.levelRight m).obj ((S.PY.evaluation m).obj (CY.image.system.direct.obj N))) ≫
      (CX.image.level n).inverse.map
        ((G.quotientComparison h).hom.app
          ((S.PY.evaluation m).obj (CY.image.system.direct.obj N))) ≫
      (CX.image.level n).inverse.map ((G.levelRight n).map
        (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
          ((S.PY.transition h).app (CY.image.system.direct.obj N)))) =
    ((CX.proEvaluation.scalar h).derivedAdj.homEquiv _ _).symm
        ((CX.proEvaluation.transition h).app ((exceptionalSystemRight G CX CY).obj N)) ≫
      (exceptionalSystemRightEtaleEvaluation G CX CY n).hom.app N) := by
  sorry

end AlgebraicGeometry
