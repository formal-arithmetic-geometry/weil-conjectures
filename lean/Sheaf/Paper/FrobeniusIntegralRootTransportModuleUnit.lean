/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.Paper.PurTwistSheaves
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-! # Invertibility of the module adjunction unit for an isomorphic scheme map
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

/-- The module adjunction unit is invertible along an isomorphism of schemes.
Source: Stacks Project, Modules on Sites, Tags 09A5 and 03EL.
Proof: inverse image of sheaves on the pro-etale site is an equivalence for an
isomorphism of schemes; transport this equivalence through scalar extension and
reflect its unit along the underlying sheaf functor.
(blueprint: new-weil-frobenius-integral-root-transport-module-unit). -/
theorem frobeniusIntegralRootTransport_moduleUnit_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    IsIso ((SheafOfModules.toSheaf _).map
      ((proEtaleRingModuleAdjunction g (completedIntegralCommRingSheafUnrestricted l E Y)
        (completedIntegralCommRingSheafUnrestricted l E X) ((PurCompactSupport.completed l E).pull
          g)).unit.app (purTwistIntegralModule Y l E))) := by
  sorry

end WeilConjectures
