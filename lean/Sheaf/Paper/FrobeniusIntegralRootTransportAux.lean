/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.Paper.PurTwistSheaves
public import Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-! # Additive transport input for the first integral root line

This is the additive sheaf comparison used to construct the module comparison.
(blueprint: lem-weil-frobenius-integral-root-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
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

/-- The additive inverse-image transport of the first completed integral root line.

Source: literature/stacks-project/sites-modules.tex, Tags 03EK and 03EL; expanded DAG
clause 2 of `def-weil-frobenius-coefficient-twists`.
Proof: finite root comparisons commute with transitions, hence their inverse limit gives
an additive isomorphism. Tensor presentation transport extends it across the constant
integral coefficients and the completed coefficient pushout. The resulting additive map
is semilinear for the completed coefficient comparison and has the displayed formula on
pure root tensors. This is the additive part of the module transport; the parent theorem
performs the adjunction step turning it into a module isomorphism.
(blueprint: new-weil-frobenius-integral-root-transport-additive). -/
theorem frobeniusIntegralRootTransport_additive
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (r : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (hr : r = limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
        (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
      lim.map (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose)) :
    ∃ φ : (SheafOfModules.toSheaf _).obj (purTwistIntegralModule Y l E) ⟶
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj (purTwistIntegralModule X l E)),
      IsIso φ ∧
      (∀ (V : Y.ProEt) (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
          (op V)) (x : (purTwistZlOne Y l).obj.obj (op V)),
        φ.hom.app (op V)
          (@SMul.smul _ _ (purTwistIntegralAction Y l E (op V)).toSMul a
            (purTwistIntegralTensor Y l E (op V) 1 x)) =
        @SMul.smul _ _
          (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
          ((sfCompletedCoefficientMap l E g).hom.app (op V) a)
          (purTwistIntegralTensor X l E (op ((proEtaleBaseChange g).obj V)) 1
            (r.hom.app (op ((proEtaleBaseChange g).obj V))
            (((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
              (purTwistZlOne Y l)).hom.app (op V) x)))) ∧
      (∀ (V : Y.ProEt) (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
          (op V)) (t : (purTwistIntegralModule Y l E).val.obj (op V)),
        φ.hom.app (op V)
          (@SMul.smul _ _ (purTwistIntegralAction Y l E (op V)).toSMul a t) =
        @SMul.smul _ _
          (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
          ((sfCompletedCoefficientMap l E g).hom.app (op V) a)
          (φ.hom.app (op V) t)) := by
  sorry

end WeilConjectures
