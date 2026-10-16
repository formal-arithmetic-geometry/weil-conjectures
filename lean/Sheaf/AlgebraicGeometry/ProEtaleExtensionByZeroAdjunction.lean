/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleExtensionByZero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# The adjunction for pro-etale extension by zero

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-open-closed-triangle`,
order 1835; Stacks Project, Tags 03DI, 03CY and 09AE
(blueprint: lem-weil-extension-by-zero-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Extension by zero is left adjoint to restriction, in the localized-site presentation
used by `proEtaleExtensionByZero`. The localization theorem identifies this restriction
with restriction to `U.left.ProEt`, including the constant coefficient ring and module maps.

Source: Weil conjectures blueprint, order 1835; Stacks Project, Tags 03DI, 03CY and 09AE
(blueprint: lem-weil-extension-by-zero-adjunction).

Proof plan:
1. Use `ProEt.weaklyEtale_localization` (lem-weil-proetale-weakly-etale-localization)
   to identify the site over the open subscheme with the slice, its coefficient ring
   with the restricted constant ring, and restriction with `SheafOfModules.overFunctor`.
   The open immersion implies that each object has at most one arrow to `U`.
2. For a module map from `M` to the restriction of `N`, define a presheaf map from
   `P_M` to `N` by its given component on each object factoring through `U`, and the
   unique map from zero on all other objects. Naturality is that of the original map
   on the first objects and follows from the zero source on the others. The components
   are linear for the restricted coefficient actions (def-weil-extension-by-zero).
3. Conversely, take the components over `U` of a map `P_M` to `N`. These constructions
   are inverse, since the remaining components have zero source. Precomposition and
   postcomposition act componentwise, proving naturality in both variables.
4. Apply the universal property of `PresheafOfModules.sheafification` and its adjunction
   (def-weil-presheaf-modules-sheafification) to identify maps from `P_M` with maps from
   its sheafification, which is `proEtaleExtensionByZero`. Functoriality of sheafification
   makes this identification natural in `M`, and associativity makes it natural in `N`.
   The composite natural Hom equivalence gives the claimed adjunction. -/
theorem proEtaleExtensionByZero_adjunction (X : Scheme.{u}) (U : X.ProEt)
    [IsOpenImmersion U.hom] (A : CommRingCat.{u + 1}) [Finite A] :
    Nonempty (proEtaleExtensionByZero X U A ⊣
      SheafOfModules.overFunctor.{u + 1}
        ((constantSheaf (ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of A)) U) := by
  sorry

end AlgebraicGeometry.Scheme
