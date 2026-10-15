/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded

/-!
# Smooth base change with ring-order-invertible coefficients

Source: upstream-master-20261014, SixFunctors/Etale/BaseChangeTheorems/Smooth.lean,
`AlgebraicGeometry.Etale.isIso_baseChange_of_smooth_of_ring_order_invertible`
(blueprint: nt-target-etale-smooth-ring).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Smooth base change is an isomorphism of functors on bounded below derived categories of
etale sheaves of `Λ`-modules if every additive order in `Λ` is invertible on the base.
Source: upstream-master-20261014, SixFunctors/Etale/BaseChangeTheorems/Smooth.lean,
`Etale.isIso_baseChange_of_smooth_of_ring_order_invertible`
(blueprint: nt-target-etale-smooth-ring).

Proof plan:
1. Fix a bounded below complex K. The constant-ring module equivalence
   [lem-weil-pbc-etale-constant-ring-module-equivalence] is additive and exact, since it
   preserves the underlying abelian presheaves. Its termwise inverse descends to the derived
   categories [def-weil-pbc-derived-categories]. It preserves injectives and identifies direct
   images [def-weil-pbc-direct-image], inverse images [def-weil-pbc-inverse-image] and their
   derived versions [def-weil-pbc-derived-inverse-image], including units and counits. Thus it
   identifies the actual unit-square-counit exchange [def-weil-pbc-derived-exchange].
2. Forget coefficients using [lem-weil-pbc-exchange-forget-coefficients]. Set
   n = addOrderOf (1 : Λ). Since n kills 1, it kills every module element and every geometric
   stalk [def-weil-pbc-geometric-stalks]. The hypothesis at 1 makes n a unit on Y. If n = 0,
   a geometric point over X would give a ring map from the global sections of Y to a field
   taking that unit to zero, impossible. Otherwise every stalk has finite order dividing n;
   each prime divisor of n is invertible on Y. The forgotten complex therefore belongs to
   the allowable-torsion category [sbc-def-derived-categories-with-allowable-torsion].
3. Apply [sbc-thm-bounded-below-derived-smooth-base-change] to the forgotten complex, with
   its (S,T,X,Y;f,g,h,e) equal to (Y,X,Y',X';g,f,f',g'). Its smooth side is g and its qcqs
   side is f. The square in [sbc-thm-smooth-base-change] and the identification in
   [sbc-def-base-change-map] give precisely the abelian exchange arrow above.
4. The exchange comparison of [lem-weil-pbc-exchange-forget-coefficients] identifies the
   forgotten module exchange with that abelian exchange and reflects invertibility.
   Hence the component at K of the actual module exchange is an isomorphism.
5. Since K was arbitrary, invert each component. Naturality of the original transformation,
   multiplied by those inverses, gives naturality of the inverse. The two inverse identities
   hold componentwise, proving that the natural transformation itself is an isomorphism. -/
theorem Etale.isIso_baseChange_of_smooth_of_ring_order_invertible
    (Λ : Type (u + 1)) [CommRing Λ] {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    [QuasiCompact f] [QuasiSeparated f] [Smooth g]
    (sq : IsPullback g' f' f g) (htor : ∀ a : Λ, IsUnit (addOrderOf a : Γ(Y, ⊤))) :
    IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
  sorry

end AlgebraicGeometry
