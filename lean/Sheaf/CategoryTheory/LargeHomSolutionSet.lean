/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-! A solution set for the universe-enlarged Hom functor. -/

@[expose] public section

universe w u vH

open CategoryTheory.Limits

namespace CategoryTheory

/-- A well-powered abelian category with sufficiently large coproducts gives
a small solution set for the lifted Hom functor of any object.

Source: Stacks Project Lemma 19.14.1 (Tag 0F5S), first proof, using images
of sums of the defining object. The quotient parametrization below is an
agent-written refinement of its cardinal-bound argument; it works for any G.

(blueprint: new-stage3-large-hom-solution-set)

Proof in words: fix a module M in Type max(w,vH). Form P, the coproduct of
copies of G indexed by the underlying set of M, with injections i_m.
In an abelian category, well-poweredness also gives co-well-poweredness:
quotients of P are parametrized by its subobjects, by taking cokernels.
Thus there is a Type w family of quotient maps q_N : P -> Q_N covering
every quotient up to isomorphism. Restrict this index set to the quotients
for which m |-> i_m q_N is an additive, End(G)^op-linear map to Hom(G,Q_N).
Lift its values to obtain f_N : M -> ULift Hom(G,Q_N).

Given h : M -> ULift Hom(G,X), unlift its values to form d : P -> X by
the coproduct universal property. Factor d as an epimorphism q : P -> Q
followed by the image monomorphism j : Q -> X. Because composition with j
is injective on Hom(G,Q), the values i_m q satisfy all additive and scalar
relations of M: they do so after composing with j, by linearity of h.
Consequently this quotient occurs among the restricted indices. Transport
it to its chosen quotient representative Q_N. The induced map g : Q_N -> X
satisfies f_N followed by the lifted Hom map of g equals h, elementwise.
This proves the solution-set condition with index universe w. No arbitrary
object is chosen from an unproved existence theorem: this is a proposition
about the explicitly specified functor. For G = 0 or M = 0 the same
construction gives the unique zero map; no separator assumption on G is used.
-/
theorem large_hom_solutionSetCondition
    {C : Type u} [Category.{w} C] [Abelian C] [WellPowered.{w} C]
    [HasCoproducts.{max w vH} C] (G : C) :
    SolutionSetCondition.{w} (preadditiveCoyonedaObj G ⋙
      ModuleCat.uliftFunctor.{vH, w} (End G)ᵐᵒᵖ) := by sorry

end CategoryTheory
