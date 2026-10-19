/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

import Sheaf.CategoryTheory.SheafTensorClosed
import Sheaf.CategoryTheory.ModuleObjects.LiftExact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

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

Proof plan, following the six steps of the node:
1. By lem-weil-pbc-site-sheaves-enough-injectives and det-def-sfb-sheaf-tensor-closed,
   abelian sheaves on the two pro-etale sites form abelian closed symmetric monoidal
   categories with additive, colimit-preserving tensor. The rings are those of
   sk-def-sfb-pulled-back-coefficients. By def-sfb-finite-upper-star-monoidal and
   lem-sfb-finite-upper-star-braided the transported ring is commutative as well.
   Apply lem-sfb-modobj-abelian to the three rings. Equalizers and coequalizers exist
   by def-sp-abelian, as kernels and cokernels of differences.
2. The direct image of abelian sheaves is additive by the restriction formula of
   def-sfb-finite-lower-star. Under def-sfb-finite-upper-lower-star-adjunction, the
   transposes of F(u + v) and Fu + Fv coincide by naturality of the unit and
   bilinearity of composition. Injectivity of the adjunction bijection gives
   additivity of inverse image; cancellation gives preservation of zero and negatives.
3. By lem-sfb-finite-upper-star-exact the abelian inverse image is exact. Its mapMod
   commutes with forgetful functors by def-sfb-modobj-transport. Apply
   det-prop-sfb-module-pullback-exact-lifted to obtain exactness of transport.
4. By lem-sfb-alpha-ring-hom and lem-sfb-alpha-iso the coefficient comparison is an
   isomorphism of ring objects. Its inverse preserves unit and multiplication by
   cancellation. Restriction along that inverse leaves underlying objects and maps
   unchanged (def-sfb-modobj-restriction). Apply
   det-prop-sfb-module-pullback-exact-lifted with ambient identity to obtain exactness.
5. By def-sfb-modobj-restriction-equivalence and def-sfb-modobj-extension-along-iso,
   extension along the coefficient comparison is naturally isomorphic to this inverse
   restriction. Conjugate maps by the comparison to transfer additivity. Transfer a
   limiting cone by composing its legs with the comparison; unique factorizations
   transfer back using its inverse. The dual argument transfers colimiting cocones.
   This proves finite-limit and finite-colimit preservation by extension.
6. The upperStar of sk-def-sfb-module-pushforward-pullback is transport followed by
   that extension. Composing the additive maps on Hom groups gives additivity;
   composing the two preservation properties gives preservation of finite limits
   and finite colimits, the exactness of def-galois-exact-functor. -/
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
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
