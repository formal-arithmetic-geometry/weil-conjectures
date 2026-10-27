/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.ModuliSchemeBaseChange
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Maximal smooth open of an algebraic stack

Source: Stacks Project, stacks-morphisms.tex, Tag 0DZR, lemma-where-smooth,
existence and clause (3) (blueprint: lem-sfb-stack-maximal-smooth-open).

Open substacks are the existing full substacks. Equality after scheme base change
is equality of their object predicates on the explicit iso-comma category, retaining
the base isomorphism and the compatible pairs of arrows.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- Every algebraic stack over a scheme has a largest smooth open. For a locally
finitely presented structural morphism, this open commutes with flat scheme base change.
Source: Stacks Project, stacks-morphisms.tex, Tag 0DZR, lemma-where-smooth,
existence and clause (3) (blueprint: lem-sfb-stack-maximal-smooth-open).

Proof:
1. Choose a smooth surjective scheme atlas P → F. Put h : P → S and
   R = P ×_F P. By lem-sfb-invariant-open-substack-descent this is an algebraic
   space; both projections s,t : R → P are smooth by
   lem-sfb-stack-chartwise-smooth-etale-calculus. Apply
   lem-sfb-space-maximal-smooth-open to h, obtaining its largest smooth open W.
   No finite-presentation or flatness hypothesis on h is needed here.
2. For r in R, lem-sfb-space-smooth-source-point-locality gives s(r) in W
   exactly when h s is smooth near r, and likewise for t. The atlas comparison
   identifies h s with h t, so s⁻¹(W) = t⁻¹(W). Apply
   lem-sfb-invariant-open-substack-descent to descend W to an open U of F.
3. W → U is a smooth surjective atlas by the chartwise calculus, with smooth
   composite to S. To compare any two smooth atlases, form their fibre product,
   smooth and surjective over both, and apply the two directions of
   lem-sfb-space-smooth-source-point-locality. Thus smoothness is atlas independent.
   Any other smooth open V pulls back to a smooth open of P, contained in W.
   The inclusion-preserving correspondence of
   lem-sfb-invariant-open-substack-descent gives V contained in U.
4. If F → S is locally of finite presentation, h is locally of finite presentation.
   For flat g : S' → S, the base-changed atlas P' → F' is smooth surjective by
   lem-sfb-stack-chartwise-smooth-etale-calculus. The flat-base-change clause of
   lem-sfb-space-maximal-smooth-open identifies its largest smooth open with
   W ×_S S'. Repeat steps 1--3 for F'. The resulting U' and U ×_S S' have the
   same pullback to P', hence agree by the injective atlas-open correspondence.
   In the iso-comma construction this says U'.property x iff U.property x.obj.left.
   No surjectivity or finite-presentation hypothesis on g is used. -/
theorem exists_maximal_smooth_open_moduliSubstack
    {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsAlgebraicModuliStack F) :
    ∃ U : OpenModuliSubstack F,
      IsSmoothModuliStack U.category ∧
      (∀ V : OpenModuliSubstack F,
        IsSmoothModuliStack V.category → V.IsContainedIn U) ∧
      ((∃ (P : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj P)) F),
          IsSmoothModuliAtlas F P a ∧ LocallyOfFinitePresentation P.hom) →
        ∀ (S' : Scheme.{u}) (g : S' ⟶ S), Flat g →
          ∃ U' : OpenModuliSubstack (moduliSchemeBaseChange F g),
            IsSmoothModuliStack U'.category ∧
            (∀ V' : OpenModuliSubstack (moduliSchemeBaseChange F g),
              IsSmoothModuliStack V'.category → V'.IsContainedIn U') ∧
            ∀ x : (moduliSchemeBaseChange F g).obj,
              U'.property x ↔ U.property x.obj.left) := by
  sorry

end CategoryTheory
