/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorNormalization
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.QuotientPullbackTensorFlatModel

/-! # Tensor coherence of the normalized quotient pullback comparison

Source: blueprint latest (main-20261026), integral proper-base-change proof, paragraph (3);
Stacks Project, sites-cohomology.tex, Tags 0D6D and 07A4
(blueprint: lem-sfb-quotient-pullback-tensor-coherence).

The positive exponent is n + 1, including the residue-field quotient at n = 0.
The section comparison is specified by its ordinary ringed-square balancing map
and localization counits, rather than by an arbitrary isomorphism of functors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

open QuotientChange QuotientSectionTensor

/-- The existing tensor comparison with the recorded pullback functor type exposed.
This only shares the structural arguments of leftDerivedUpperStarTensor.
Source: Stacks 07A4 (blueprint: lem-sfb-quotient-pullback-tensor-coherence). -/
@[irreducible] def quotientTensorPull
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.postcompose₂.obj (L B f)).obj (CondensedRing.derivedTensor B Y) ⟶
      (((Functor.whiskeringLeft₂ _).obj (L B f)).obj (L B f)).obj
        (CondensedRing.derivedTensor B X) := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarTensor B f

end AlgebraicGeometry.ProEtale.IntegralQuotient
