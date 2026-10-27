/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.Paper.FiniteTateSiteDescentDefinitions
public import Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-! # Transport of the first finite root line

Source: expanded DAG def-weil-frobenius-coefficient-twists, clause 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private instance (priority := 3000) rootSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleModuleInverseImage completedIntegralCoefficientSheafUnrestricted
  MorphismProperty.Over.pullback constantSheaf Padic
attribute [local instance_reducible] PurCompactSupport.completed


/-- The prescribed root-limit comparison extends to the first
finite coefficient line. This statement concerns only the first line,
without tensor powers, signed powers, or a uniqueness assertion.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-def-purity-conv/
def-weil-frobenius-coefficient-twists.md, natural Weil isomorphism;
expanded DAG clause 2; Stacks, Modules on Sites, Tag 03EL.
(blueprint: lem-weil-frobenius-finite-root-transport).
Proof: the finite root comparisons commute with the power transitions. Their inverse
limit is the displayed r; inverse image along the scheme isomorphism preserves this
limit. Its adjunct respects completed Z_l scalars because the scalar actions and r
are determined by their finite projections. Extend this semilinear map through the
constant O_E scalar tensor. The completed coefficient comparison respects both scalar
inclusions into the coefficient pushout, so the extended map respects the recorded
completed action. Apply ordinary finite coefficient extension to this map; its tensor unit sends a
  root to the displayed finite generator. Constant coefficients pull back to the same constants.
The inverse construction uses the inverse scheme isomorphism and the inverse root
and coefficient comparisons. The two composites are identities by tensor generation
and sheafification. No invertibility of l on the schemes is used: only invertibility
of g is needed to commute with the root limit. The same argument includes the empty
scheme and every ramification index. -/
theorem frobeniusFiniteRootTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ)
    (r : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (hr : r = limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
        (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
      lim.map (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose)) :
    ∃ e : (proEtaleRingModulePullback g (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) ((PurCompactSupport.finite l E (n + 1)
          (Nat.succ_pos n)).pull g)).obj (purTwistFiniteOne Y l E n) ≅ (purTwistFiniteOne X l E n),
      ∀ (V : Y.ProEt) (a : finiteTateCoefficient l E n)
        (x : (purTwistZlOne Y l).obj.obj (op V)),
        e.hom.val.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleRingModuleAdjunction g (integralCoefficientCommRingSheaf l E Y n)
            (integralCoefficientCommRingSheaf l E X n) ((PurCompactSupport.finite l E (n + 1)
              (Nat.succ_pos n)).pull g)).unit.app (purTwistFiniteOne Y l E n)).val.app (op V)
            (finiteTateProGenerator l E n Y (op V) a x)) =
      finiteTateProGenerator l E n X (op ((proEtaleBaseChange g).obj V)) a
        (r.hom.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
            (purTwistZlOne Y l)).hom.app (op V) x)) := by sorry

end WeilConjectures
