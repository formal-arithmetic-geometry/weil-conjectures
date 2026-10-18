/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.CategoryTheory.SiteInjectiveCechAcyclic
import WeilConjectures.CategoryTheory.SiteCechVanishingCriterion

/-!
# Inverse images of injective abelian sheaves are evaluation-acyclic

Source: Stacks Project, Cohomology on Sites, Tag 0D6X,
`lemma-pullback-injective-pre-limp`, specialized to abelian sheaves
(blueprint: lem-trf-site-pullback-injective-evaluation-acyclic).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The inverse image of an injective abelian sheaf under the geometric morphism
associated to a continuous cocontinuous site functor has zero positive evaluation
cohomology. The inverse image is the canonical sheafification of precomposition;
by continuity, the precomposition is already a sheaf (Stacks Sites, Tag 00XR).
The displayed `rightDerived` is the ordinary derived functor of evaluation, not
an independently chosen cohomology theory. Positive integer degrees are encoded
by natural degrees with `0 < p`.

Source: Stacks Project, Cohomology on Sites, Tag 0D6X
(blueprint: lem-trf-site-pullback-injective-evaluation-acyclic).

Proof:
1. By lem-weil-pbc-continuous-cocontinuous-topos-adjunction, the inverse image
   is precomposition with `f.op`. Its abelian operations are the componentwise
   ones, since inverse image preserves finite products. Sheafification of this
   already sheaf presheaf gives the same abelian sheaf canonically.
2. For every source covering, continuity sends its arrows to a target covering.
   Inductively apply preservation of the pullback of a covering arrow to identify
   each iterated source fibre product after `f` with the target fibre product.
   The comparisons commute with the omitting-factor projections, by uniqueness
   in their universal properties (def-weil-pbc-site-cech-complex).
3. Thus restriction along these comparisons identifies the two Cech complexes,
   including their alternating restriction differentials. The target complex
   has zero positive cohomology by lem-weil-pbc-site-injective-cech-acyclic,
   because its coefficient sheaf is injective. The source complex does too.
4. Apply lem-weil-pbc-site-cech-vanishing-criterion with all source objects and
   all coverings. Every intersection lies in this collection, and every cover
   refines itself. It follows that every positive ordinary right derived
   evaluation group of the inverse image is zero. -/
theorem isZero_rightDerived_evaluation_pullback_injective
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    (_hJ : J.IsSiteForCoverings) (_hK : K.IsSiteForCoverings)
    (f : C ⥤ D)
    (_hcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map f ∈ K (f.obj X))
    (_hpullback : ∀ (X Y Z : C) (S : Presieve X), S ∈ J X →
      ∀ (a : Y ⟶ X) (b : Z ⟶ X), S a → PreservesLimit (cospan a b) f)
    [f.IsCocontinuous J.toGrothendieck K.toGrothendieck]
    (I : Sheaf K.toGrothendieck AddCommGrpCat.{u}) [Injective I]
    (U : C) (p : ℕ) (_hp : 0 < p) :
    IsZero (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived p).obj
        ((presheafToSheaf J.toGrothendieck AddCommGrpCat.{u}).obj (f.op ⋙ I.obj))) := by
  sorry

end CategoryTheory
