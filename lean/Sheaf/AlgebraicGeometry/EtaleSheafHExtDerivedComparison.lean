/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Comparison of Ext sheaf cohomology with derived global sections

Source: Stacks Project, Derived Categories, Definition 015A and Lemma 05TI;
Etale Cohomology, the cohomology convention used in Lemma 03Q5.
(blueprint: lem-weil-pbc-sheafH-ext-derived-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Ext cohomology of abelian etale sheaves agrees naturally with the homology of
 derived global sections. No compactness, dimension, or torsion assumption is needed.
 Source: Stacks Project, Derived Categories, Definition 015A and Lemma 05TI;
 Etale Cohomology, Lemma 03Q5, using the same injective-resolution definition of cohomology.
 (blueprint: lem-weil-pbc-sheafH-ext-derived-comparison).

 Proof: Choose an injective resolution of each sheaf F. A bounded-below injective
 resolution is K-injective, so applying global sections computes the right-hand functor,
 by lem-sp-derived-functor-single-identification. On the left, Sheaf.H is Ext from the
 constant integer sheaf. Compute this Ext group with the same injective resolution;
 maps from the constant integer sheaf to each injective term identify with global
 sections by the constant-sheaf/global-sections adjunction and evaluation at 1 in Z.
 These identifications commute with the differentials, hence induce additive
 isomorphisms on cohomology. For a sheaf morphism, lift it to the injective resolutions;
 both constructions use the same lift. Lifts are unique up to homotopy, so the
 isomorphisms are independent of choices and natural. Package them as a natural
 isomorphism. This also handles degree zero and the empty scheme. -/
theorem nonempty_sheafH_extDerivedIso (X : Scheme.{u}) (q : ℕ) :
    Nonempty (Sheaf.functorH.{u + 1} X.smallEtaleTopology q ≅
      DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ)) := by sorry

end AlgebraicGeometry.Scheme
