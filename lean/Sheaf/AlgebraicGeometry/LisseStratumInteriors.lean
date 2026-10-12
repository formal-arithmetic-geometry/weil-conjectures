/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! Lissity on the union of the interiors of lisse strata. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Finite set-stalk lissity on each stratum implies lissity on the union of their interiors.
Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof paragraphs 1--3 of
`lem-weil-pbc-finite-pushforward-generic-constructible`; the Zariski gluing argument
is also written in `WeilConjectures/ConstructibleSheaf/GenericConstancy.lean`.
(blueprint: lem-weil-pbc-lisse-stratum-interiors).

Proof: Cover the union W of the interiors by the open subschemes V_i = interior(T_i).
For each i form P_i = V_i x_Z T.domain i. The first projection is an immersion
and is surjective because the image of V_i is contained in the i-th stratum.
A surjective immersion is a closed immersion, hence a universal homeomorphism.
Pull back the lisse restriction on T.domain i along the second projection.
Composition of inverse images identifies the result with the restriction of
E to P_i. Universal-homeomorphism invariance of the etale site then descends
lissity to V_i: the site equivalence transports etale trivializations, and its
geometric points identify the finite stalks. The comparison of set inverse image
and underlying abelian inverse image justifies each use of the displayed set
restriction. This fibre-product argument does not assume that the map V_i -> Z
factors through the chosen scheme structure on the stratum.
The trivializing etale covers on all V_i compose with the open cover of W to
trivialize the restriction on W. Every geometric point of W lifts to a member
of this open cover, and inverse image identifies its stalk with that finite
stalk. Thus both local constancy and finite geometric stalks hold. When W is
empty, the empty etale covering trivializes the sheaf and the stalk condition
is vacuous. -/
theorem lisse_on_stratum_interiors
    {Z : Scheme.{u}} (E : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (T : Stratification Z)
    (hT : ∀ i : Fin T.n, IsFiniteLocallyConstantEtaleSheafOfSets
      ((etaleSetPullback (T.immersion i)).obj
        ((sheafCompose Z.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E))) :
    IsLisseEtaleSheafOfSets
      ((sheafCompose T.interiorUnion.toScheme.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} T.interiorUnion.ι).obj E)) := by sorry

end AlgebraicGeometry.Scheme
