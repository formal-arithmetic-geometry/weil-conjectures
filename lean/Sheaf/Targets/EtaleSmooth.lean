/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.BaseChange.Derived
import Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
import Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets

/-!
# Smooth base change for bounded-below etale abelian sheaves

Source: upstream-master-20261014, SixFunctors/Etale/BaseChangeTheorems/Smooth.lean,
`AlgebraicGeometry.Etale.isIso_baseChange_of_smooth`
(blueprint: nt-target-etale-smooth).

The invertible-order hypothesis is expanded stalkwise: the old upstream predicate
`orderInvertibleOnHomology` is absent from the published library. Abelian groups are
`AddCommGrpCat`, the current name of the source's `Ab` coefficient category.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Smooth base change for a bounded-below complex with invertible-order cohomology.
Source: upstream-master-20261014, SixFunctors/Etale/BaseChangeTheorems/Smooth.lean,
`Etale.isIso_baseChange_of_smooth` (blueprint: nt-target-etale-smooth).

Proof plan:
1. Put P = Y.invertiblePrimes. For each cohomology degree and geometric stalk element x,
   hK says that n = addOrderOf x is a unit in the global sections of Y. If n > 0, every
   prime divisor p of n is also a unit: writing n = p*r, multiply r by the inverse of n.
   Thus x is killed by an integer whose prime divisors lie in P, as required by
   sbc-def-derived-categories-with-allowable-torsion. If n = 0, a geometric point over X
   would induce a ring map from the global sections of Y to its separably closed field
   taking the unit zero to zero, a contradiction. This case therefore has no stalks.
   The stalks used here are those of def-weil-pbc-geometric-stalks, via pointSmallEtale.
2. Apply sbc-thm-bounded-below-derived-smooth-base-change with its
   (S,T,X,Y;f,g,h,e) relabelled as (Y,X,Y',X';g,f,f',g'). Smoothness and qcqs are the
   given assumptions; step 1 gives its allowable-torsion input. The square convention
   is that of sbc-thm-smooth-base-change. The canonical arrow of sbc-def-base-change-map
   agrees with def-weil-pbc-derived-exchange on this square. Indeed the component of
   baseChangeUnitStep is the unit for f'; baseChangeSquareStep is the direct image of
   the canonical comparison Lf'^* Lg^* = Lg'^* Lf^*; baseChangeCounitStep is the direct
   image of Lg'^* applied to the counit for f. The comparison is the inverse composition
   comparison for f' followed by g, the square equality, then the composition comparison
   for g' followed by f. Consequently this is the actual three-arrow composite
   Etale.baseChange.app K. The recorded derived-exchange interface expresses this same
   canonical map as derivedBaseChangeMapPlus: on injective resolutions it is the
   underived exchange followed by the derived-functor unit, and uniqueness of the right
   derived extension identifies it with the mate composite. Its invertibility is the
   required conclusion. -/
theorem Etale.isIso_baseChange_of_smooth
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    [QuasiCompact f] [QuasiSeparated f] [Smooth g]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : ∀ (q : ℤ) (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
      (x : ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj K)),
      IsUnit (addOrderOf x : Γ(Y, ⊤))) :
    IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K) :=
  sorry

end AlgebraicGeometry
