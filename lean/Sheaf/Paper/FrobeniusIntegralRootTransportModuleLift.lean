/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.Paper.PurTwistSheaves
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-! # Semilinear lift for integral root transport

The semilinear additive map is lifted through the canonical module adjunction.
-/

@[expose] public section
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
attribute [local implicit_reducible] PurCompactSupport.completed
  completedIntegralCommRingSheafUnrestricted

/-- A completed-coefficient semilinear additive map lifts to a module morphism.
Source: Stacks Project, Modules on Sites, Tag 03EL.
Proof: use the sectionwise semilinearity hypothesis to define the map on the
module pullback through the tensor universal property and sheafification; its
adjunction transpose has the prescribed values on every site section. Naturality
follows from semilinearity and the tensor relations.
(blueprint: new-weil-frobenius-integral-root-transport-module-lift). -/
theorem frobeniusIntegralRootTransport_moduleLift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (φ : (SheafOfModules.toSheaf _).obj (purTwistIntegralModule Y l E) ⟶
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj (purTwistIntegralModule X l E)))
    (hscalar : ∀ (V : Y.ProEt)
      (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
      (t : (purTwistIntegralModule Y l E).val.obj (op V)),
      φ.hom.app (op V)
          (@SMul.smul _ _ (purTwistIntegralAction Y l E (op V)).toSMul a t) =
        @SMul.smul _ _
          (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
          ((sfCompletedCoefficientMap l E g).hom.app (op V) a)
          (φ.hom.app (op V) t)) :
    ∃ f : (proEtaleRingModulePullback g (completedIntegralCommRingSheafUnrestricted l E Y)
        (completedIntegralCommRingSheafUnrestricted l E X) ((PurCompactSupport.completed l E).pull
          g)).obj (purTwistIntegralModule Y l E) ⟶ (purTwistIntegralModule X l E),
      ∀ (V : Y.ProEt)
        (t : (purTwistIntegralModule Y l E).val.obj (op V)),
        f.val.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleRingModuleAdjunction g (completedIntegralCommRingSheafUnrestricted l E Y)
            (completedIntegralCommRingSheafUnrestricted l E X) ((PurCompactSupport.completed l
              E).pull g)).unit.app (purTwistIntegralModule Y l E)).val.app (op V) t) =
        φ.hom.app (op V) t := by
  sorry

end WeilConjectures
