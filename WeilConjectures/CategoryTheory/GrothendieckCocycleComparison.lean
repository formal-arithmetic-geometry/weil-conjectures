/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckComposablePair
import WeilConjectures.CategoryTheory.HypercohomologyEdgeCocycle
import WeilConjectures.CategoryTheory.GrothendieckHypercohomologyEdge

/-! # Comparing the Grothendieck edge with the cocycle quotient

Source: Stacks Project, Derived Categories, Tags 015N and 015J, with the
quotient/inclusion edge of the double-complex model.
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The fixed-degree comparison between the abstract left edge and the cocycle quotient.
The morphism c is given, and only its compatibility with the cycle inclusions is assumed.
This lemma asserts no existence of c, no filtration properties, and no collapse criterion.

Source: the Cartan--Eilenberg construction of Stacks Project, Derived Categories,
Tags 015N and 015J. -/
theorem grothendieck_cocycle_comparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (X : A) (I : InjectiveResolution X) (n : ℕ)
    (c : G.obj
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles n) ⟶
      (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles n)
    (hc : c ≫
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles n =
      G.map (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles n)) :
    c ≫ (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ n ≫
        (I.isoRightDerivedObj (F ⋙ G) n).inv ≫
        (F.grothendieckLeftEdgeMap G hFG n).app X ≫
        G.map (I.isoRightDerivedObj F n).hom =
      G.map (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ n) := by
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have h := G.cochainHypercohomologyLeftEdge_cocycle K n c hc
  have e := grothendieckLeftEdgeMap_eq_hypercohomology F G hFG X I n
  rw [← e] at h
  exact h

end CategoryTheory
