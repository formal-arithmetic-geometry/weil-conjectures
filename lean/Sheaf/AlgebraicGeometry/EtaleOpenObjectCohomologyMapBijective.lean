/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Sheaf.Paper.SiteRestrictionInjectives
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Bijectivity of the canonical open-object cohomology map

Source: Stacks Project, Cohomology on Sites, Tag 03F3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical identity-generator map is bijective on object cohomology.
Source: Stacks Project, Cohomology on Sites, Tag 03F3, proof of cohomology-of-open.
(blueprint: lem-weil-pbc-etale-open-object-cohomology-map-bijective)

Proof: Choose an injective resolution I of F. Extension by zero along the open is
exact and left adjoint to localization restriction, so restriction preserves injectives.
The inverse-image/restriction comparison identifies the pulled-back resolution with
that restricted resolution. The sheafification, free abelian group and Yoneda
adjunctions identify Hom from the free sheaf at U to I in each degree with I(U).
The constant-sheaf adjunction at the terminal object of U identifies Hom from the
constant integers to the restricted resolution with the same group I(U).
These are additive identifications commuting with the differentials. Their composite
is pullback followed by precomposition with etaleOpenFreeSheafUnit U: the chosen
identity generator is sent to the original section by the Yoneda adjunction.
The Ext/injective-resolution comparison identifies this map on cohomology classes
with etaleOpenObjectCohomologyMap. Hence that map is bijective in every degree.
The argument also applies to degree zero and to the empty open: it compares the
same section complexes, including the zero complex over the empty open. -/
theorem etaleOpenObjectCohomologyMap_bijective {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : X.Opens) :
    Function.Bijective (etaleOpenObjectCohomologyMap F q U) := by sorry

end AlgebraicGeometry
