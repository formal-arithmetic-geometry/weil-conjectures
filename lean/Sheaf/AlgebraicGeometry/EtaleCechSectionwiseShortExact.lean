/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Sectionwise short exactness of étale Čech complexes

Source: Stacks Project, Cohomology on Sites, Lemma 03F9, proof.
(blueprint: lem-weil-pbc-etale-cech-sectionwise-short-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The categorical Čech functor preserves zero morphisms.
Source: Stacks 03AO, functoriality of the Čech complex.
(blueprint: lem-weil-pbc-etale-cech-sectionwise-short-exact). -/
instance etale_cech_preservesZero (X : Scheme.{u}) (U : X.Etale)
    {T : Type (u + 1)} (V : T → X.Etale) (f : ∀ t, V t ⟶ U) :
    (cechComplexFunctor (fun t ↦ Over.mk (f t)) :
      ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ _).PreservesZeroMorphisms where
  map_zero := by
    intro F G
    apply HomologicalComplex.Hom.ext
    funext p
    apply Pi.hom_ext
    intro a
    simp [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
      FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp]

/-- A short exact sheaf sequence which is surjective on all intersections of a family
induces a short exact sequence of Čech complexes.

Source: Stacks Project, Cohomology on Sites, Lemma 03F9, proof, the paragraph beginning
"Hence for any U in Cov we get a short exact sequence of Cech complexes".
(blueprint: lem-weil-pbc-etale-cech-sectionwise-short-exact).

Proof: Evaluation of abelian sheaves is left exact: the inclusion into presheaves and
object evaluation preserve finite limits. Thus at each iterated fibre product the
sequence is exact on the left. The assumed surjectivity makes it short exact there.
In degree p the Čech functor takes the product of these sequences over all tuples of
p+1 indices, and acts on morphisms by the product of their section maps. Arbitrary
products in abelian groups are exact, including an empty product, so the sequence in
each degree is short exact. The criterion for short exactness of homological complexes
then gives short exactness of the sequence of Čech complexes. No covering hypothesis
is required in this step: only exactness on the specified intersections is used. -/
theorem etale_cech_shortExact_of_sections
    (X : Scheme.{u})
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact) (U : X.Etale) (T : Type (u + 1))
    (V : T → X.Etale) (f : ∀ t, V t ⟶ U)
    (hsurj : ∀ (p : ℕ) (a : Fin (p + 1) → T),
      Function.Surjective (S.g.hom.app
        (op (piObj (fun j : Fin (p + 1) ↦ Over.mk (f (a j)))).left))) :
    (S.map (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringLeft _ _ _).obj (Over.forget U).op ⋙
      cechComplexFunctor (fun t ↦ Over.mk (f t)))).ShortExact := by sorry

end AlgebraicGeometry.Scheme
