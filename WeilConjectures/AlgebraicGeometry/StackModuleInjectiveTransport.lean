/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FibredEtaleModules
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

import WeilConjectures.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings
import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.CategoryTheory.FibredLimitCalculus
import WeilConjectures.CategoryTheory.LocalSliceModuleShriekExact

/-! # Injective transport for modules on algebraic stacks

Source: Stacks Project, stacks-sheaves.tex, Tags 06WX and 06X2
(blueprint: lem-sfb-stack-representable-module-injective-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Exact precomposition, its direct-image adjunction, and injective transport.
Source: Stacks 06WX and 06X2
(blueprint: lem-sfb-stack-representable-module-injective-transport).

Proof:
1. The fibred-site continuity and cocontinuity theorem
   lem-sfb-fibred-site-functor-continuity identifies inverse image with
   precomposition. The regular-function rings are unchanged on each scheme.
   Lemma lem-trf-ringed-site-restriction-generator-data gives exactness.
2. Compatible sections over pairs (x, a(x) -> y) identify with sections on
   the test 2-fibre by unique cartesian factorization. Thus the adjunction is
   the one in lem-weil-pbc-continuous-cocontinuous-topos-adjunction, with the
   identity structural ring map. Lemma lem-weil-pbc-ringed-topoi-module-adjunction
   gives the module adjunction already used to define direct image here.
3. The exact left adjoint makes direct image preserve injectives, by
   lem-sp-right-adjoint-preserves-injectives.
4. If a is representable, lem-sfb-faithful-stack-map-representable gives
   fibrewise faithfulness. Factoring parallel arrows through a cartesian lift
   gives faithfulness on total categories. Lemma lem-sfb-fibred-limit-calculus
   gives equalizers and fibre products, with preservation by a.
5. The ringed slice over x is the big etale scheme site of its base scheme,
   by lem-sfb-fibred-test-object-ringed-localization. The induced slice map
   is an equivalence with identity maps on the regular-function rings.
6. Lemma lem-sfb-local-slice-module-shriek-exact now supplies an exact left
   adjoint to precomposition. Applying lem-sp-right-adjoint-preserves-injectives
   again shows that precomposition preserves injectives. No finiteness or
   quasi-coherence assumption was used.
-/
theorem stack_module_injective_transport
    {S : AlgebraicGeometry.Scheme.{u}}
    {A B : BasedCategory.{v, max (u + 1) v w} (Over S)}
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (a : BasedFunctor A B) :
    PreservesFiniteLimits (moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} hA.1.1 hB.1.1 a) ∧
    PreservesFiniteColimits (moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} hA.1.1 hB.1.1 a) ∧
    Nonempty (moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} hA.1.1 hB.1.1 a ⊣
      moduliBigEtaleDirectImage.{u, v, max (u + 1) v w} hA.1.1 hB.1.1 a) ∧
    (moduliBigEtaleDirectImage.{u, v, max (u + 1) v w} hA.1.1 hB.1.1 a).PreservesInjectiveObjects ∧
    (IsRepresentableByAlgebraicSpaces a →
      (moduliBigEtalePrecomposition.{u, v, max (u + 1) v w}
        hA.1.1 hB.1.1 a).PreservesInjectiveObjects) := by
  sorry

end CategoryTheory
