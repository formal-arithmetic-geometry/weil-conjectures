/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Exactness of pullback of condensed-coefficient module objects

Source: Weil conjectures blueprint, main-20261015, `sec-proetale-coefficients`,
`sk-prop-sfb-module-pullback-exact`, detail `det-prop-sfb-module-pullback-exact-main`
(blueprint: det-prop-sfb-module-pullback-exact-main).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Pullback of module objects over a commutative condensed ring is additive and exact,
and its transport and scalar-extension factors are exact.

Source: main-20261015 blueprint, `sec-proetale-coefficients`,
`sk-prop-sfb-module-pullback-exact/det-prop-sfb-module-pullback-exact-main.md`
(blueprint: det-prop-sfb-module-pullback-exact-main).

Proof: the library already supplies exactness of transport on module objects and
additivity and exactness of the composite pullback. For the remaining scalar-extension
factor, the coefficient comparison is an isomorphism of ring objects. The canonical
`Mod.extendScalarsIsoComapInv` identifies extension along it with restriction along its
inverse. Restriction preserves finite limits; transfer that property along the natural
isomorphism. Extension preserves finite colimits as a left adjoint. Assemble these
instances to obtain all seven clauses. -/
theorem module_pullback_additive_exact
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar Λ f).Additive ∧
      PreservesFiniteLimits (upperStar Λ f) ∧
      PreservesFiniteColimits (upperStar Λ f) ∧
      PreservesFiniteLimits
        ((AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1} f).mapMod
          (condensedRingObj Λ Y)) ∧
      PreservesFiniteColimits
        ((AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1} f).mapMod
          (condensedRingObj Λ Y)) ∧
      PreservesFiniteLimits (Mod.extendScalars (condensedPullbackHom Λ f)) ∧
      PreservesFiniteColimits (Mod.extendScalars (condensedPullbackHom Λ f)) := by
  have : PreservesFiniteLimits (Mod.extendScalars (condensedPullbackHom Λ f)) :=
    preservesFiniteLimits_of_natIso
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).symm
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.ProEtale.CondensedRing
