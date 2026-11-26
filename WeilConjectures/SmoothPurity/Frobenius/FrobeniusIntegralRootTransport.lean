/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusIntegralRootTransportAux
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusIntegralRootTransportModuleGlue

/-! # Transport of the first integral root line

The root-limit comparison along an isomorphism of schemes extends to the first completed
integral coefficient line.

## Implementation details

The inverse limit of the finite root comparisons is preserved by inverse image along the
scheme isomorphism; its adjunct is extended through the constant `O_E` scalar tensor and the
completed coefficient pushout. The inverse is built from the inverse scheme isomorphism and the
inverse comparisons. Invertibility of `l` on the schemes is not used.

## References

* Stacks Project, Modules on Sites, Tag 03EL
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

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  completedIntegralCoefficientSheafUnrestricted
attribute [local implicit_reducible] purTwistZlOne proEtaleRootsOfUnityTower
  PurCompactSupport.completed completedIntegralCommRingSheafUnrestricted

/-- The prescribed root-limit comparison extends to the first completed integral coefficient
line, compatibly with completed scalars. This concerns only the first line, without tensor
powers, signed powers, or a uniqueness assertion. -/
theorem frobeniusIntegralRootTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (r : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (hr : r = limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
        (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
      lim.map (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose)) :
    ∃ e : (proEtaleRingModulePullback g (completedIntegralCommRingSheafUnrestricted l E Y)
        (completedIntegralCommRingSheafUnrestricted l E X) ((PurCompactSupport.completed l E).pull
          g)).obj (purTwistIntegralModule Y l E) ≅ (purTwistIntegralModule X l E),
      ∀ (V : Y.ProEt) (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
        (x : (purTwistZlOne Y l).obj.obj (op V)),
        e.hom.val.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleRingModuleAdjunction g (completedIntegralCommRingSheafUnrestricted l E Y)
            (completedIntegralCommRingSheafUnrestricted l E X) ((PurCompactSupport.completed l
              E).pull g)).unit.app (purTwistIntegralModule Y l E)).val.app (op V)
            (@SMul.smul _ _ (purTwistIntegralAction Y l E (op V)).toSMul a
              (purTwistIntegralTensor Y l E (op V) 1 x))) =
      @SMul.smul _ _
        (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
        ((sfCompletedCoefficientMap l E g).hom.app (op V) a)
        (purTwistIntegralTensor X l E (op ((proEtaleBaseChange g).obj V)) 1
          (r.hom.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
            (purTwistZlOne Y l)).hom.app (op V) x))) := by
  obtain ⟨φ, hφ, hs⟩ :=
    frobeniusIntegralRootTransport_additive l E g r hr
  rcases hs with ⟨hroot, hscalar⟩
  obtain ⟨e, he⟩ :=
    frobeniusIntegralRootTransport_moduleGlue l E g φ hφ hscalar
  refine ⟨e, ?_⟩
  intro V b x
  exact (he V (@SMul.smul _ _ (purTwistIntegralAction Y l E (op V)).toSMul b
    (purTwistIntegralTensor Y l E (op V) 1 x))).trans (hroot V b x)

end WeilConjectures
