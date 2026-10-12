/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleOpenCohomologyComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Compatibility of the canonical comparison with smaller opens

Source: Stacks Project, Cohomology on Sites, Lemma 03F3.
(blueprint: lem-weil-pbc-etale-open-comparison-restriction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical open-object comparison commutes with inclusion of a smaller open.
Both maps are specified independently: the left map is precomposition with the free
abelian sheaf map induced by k, and the right map is inverse-image cohomology pullback,
transported along the canonical inverse-image/restriction and composition isomorphisms.
Source: Stacks Project, Cohomology on Sites, Lemma 03F3 (2), and Sites, Section 00XZ.
(blueprint: lem-weil-pbc-etale-open-comparison-restriction).

Proof: resolve G by injective sheaves on X. Exact restriction along j and k preserves
injectives because its left adjoint is exact extension by zero. The representing
sections adjunction identifies Hom(A_j,I) with I(j) and Hom(A_{k≫j},I) with I(k≫j),
and sends precomposition with the free sheaf map of k to I(k). The constant-sheaf
adjunction identifies these same complexes with global sections of the restrictions
on U and V. Under these identifications, the inverse-image pullback on global sections
is also I(k): the units and the composition isomorphism of inverse image give exactly
restriction of sections. Thus the square commutes degreewise, hence on cohomology.
The exact Ext adjunction used in etaleCohomologyOverOpenEquiv is this comparison:
in degree zero it is the sections adjunction, and in higher degrees dimension shifting
along the same injective resolution gives the unique extension of that map. This proves
commutativity for the specified comparison, not for an arbitrarily chosen equivalence.
Identity inclusions, empty opens, zero coefficients, and degree zero need no exceptions. -/
theorem etaleCohomologyOverOpenEquiv_restriction {X U V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) [IsOpenImmersion j] [IsOpenImmersion k]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Abelian.Ext
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk j) ⋙ AddCommGrpCat.free)) G q) :
    etaleCohomologyOverOpenEquiv (k ≫ j) G q
      ((Abelian.Ext.mk₀ ((EtaleOpenComparison.freeSheaf X).map
        (MorphismProperty.Over.homMk k rfl : Scheme.Etale.mk (k ≫ j) ⟶
          Scheme.Etale.mk j))).comp x (zero_add q)) =
      etaleCohomologyOverOpenRestriction j k G q
        (etaleCohomologyOverOpenEquiv j G q x) := by
  sorry

end AlgebraicGeometry
