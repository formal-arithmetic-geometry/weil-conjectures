/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.RightDerivedSingleDegreeComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
import WeilConjectures.CategoryTheory.SupportedComplexSingleRealization
import WeilConjectures.CategoryTheory.RightDerivedCanonicalSingleUnit

/-! # Normalization of the derived unit on a single-degree complex

Source: Stacks Project, Tag 015J, computation by an injective resolution.
-/

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]

/-- The derived unit, under a normalized identification with a single-degree object,
is the ordinary coefficient comparison on cycles. This statement involves no spectral
object, truncation functor, or spectral edge.
Source: Stacks Project, Tag 015J. -/
theorem rightDerivedFunctorPlusUnit_single_degree
    (L : CochainComplex.Plus B) (n : ℕ)
    (hL : ∀ i : ℤ, i ≠ (n : ℤ) → IsZero (L.obj.X i)) :
    let T := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj
    let GL := G.mapCochainComplexPlus.obj L
    let X := (DerivedCategory.Plus.homologyFunctor B n).obj (DerivedCategory.Plus.Q.obj L)
    ∀ (f : DerivedCategory.Plus.Q.obj L ⟶ (DerivedCategory.Plus.singleFunctor B n).obj X),
      (DerivedCategory.Plus.homologyFunctor B n).map f ≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := B) n).hom.app X =
          𝟙 X →
      ∀ (a : G.obj (L.obj.cycles n) ⟶ T.cycles n),
        a ≫ T.iCycles n = G.map (L.obj.iCycles n) →
      a ≫ T.homologyπ n ≫
          (DerivedCategory.Plus.homologyFunctorObjQIso GL n).inv ≫
          (DerivedCategory.Plus.homologyFunctor C n).map
            (G.rightDerivedFunctorPlusUnit.app L) ≫
          (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map f) ≫
          (G.rightDerivedSingleDegreeComparison n).hom.app X =
        G.map (L.obj.homologyπ n ≫
          (DerivedCategory.Plus.homologyFunctorObjQIso L n).inv) := by
  dsimp only
  intro f hf a ha
  let X := (DerivedCategory.Plus.homologyFunctor B n).obj (DerivedCategory.Plus.Q.obj L)
  let S : CochainComplex.Plus B :=
    ⟨(CochainComplex.singleFunctor B (n : ℤ)).obj X, n, inferInstance⟩
  obtain ⟨t, ht, hc⟩ := DerivedCategory.Plus.supported_complex_single_realization L n hL f hf
  let GL := G.mapCochainComplexPlus.obj L
  let GS := G.mapCochainComplexPlus.obj S
  let gt := G.mapCochainComplexPlus.map t
  let H := DerivedCategory.Plus.homologyFunctor C n
  have hq :
      (DerivedCategory.Plus.homologyFunctorObjQIso GL n).inv ≫
          H.map (DerivedCategory.Plus.Q.map gt) =
        HomologicalComplex.homologyMap gt.hom n ≫
          (DerivedCategory.Plus.homologyFunctorObjQIso GS n).inv := by
    apply (cancel_mono (DerivedCategory.Plus.homologyFunctorObjQIso GS n).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hu := G.rightDerivedFunctorPlusUnit.naturality t
  have hu' := congrArg H.map hu
  simp only [Functor.map_comp] at hu'
  have hs := G.rightDerivedFunctorPlusUnit_canonical_single X n
  rw [← ht, Functor.map_comp, H.map_comp, Category.assoc]
  erw [← reassoc_of% hu']
  erw [reassoc_of% hq]
  erw [HomologicalComplex.homologyπ_naturality_assoc]
  erw [hs]
  rw [HomologicalComplex.cyclesMap_i_assoc]
  change a ≫ GL.obj.iCycles n ≫ G.map (t.hom.f n) ≫
      G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n X).hom = _
  erw [reassoc_of% ha]
  rw [← G.map_comp, ← G.map_comp]
  exact congrArg G.map hc

end CategoryTheory.Functor
