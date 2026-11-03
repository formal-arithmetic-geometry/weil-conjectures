/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverComplexPresentation
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! The ordinary derived tower open-cover boundary and its naturality.
Source: latest blueprint, sec-smooth-purity/sk-prop-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing paragraph.
(blueprint: lem-dla1-tower-open-cover-triangle-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard

universe u u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.TowerOpenCover

private theorem boundary_from_presentations
    {E : Type*} [Category* E]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (L N : E ⥤ DerivedCategory D) (M : E → DerivedCategory D)
    (m : ∀ {X Y : E}, (X ⟶ Y) → (M X ⟶ M Y))
    (T : E → ShortComplex (CochainComplex D ℤ)) (ht : ∀ X, (T X).ShortExact)
    (p : ∀ X, L.obj X ≅ DerivedCategory.Q.obj (T X).X₁)
    (q : ∀ X, M X ≅ DerivedCategory.Q.obj (T X).X₂)
    (r : ∀ X, N.obj X ≅ DerivedCategory.Q.obj (T X).X₃)
    (a : ∀ X, L.obj X ⟶ M X) (b : ∀ X, M X ⟶ N.obj X)
    (ha : ∀ X, a X = (p X).hom ≫ DerivedCategory.Q.map (T X).f ≫ (q X).inv)
    (hb : ∀ X, b X = (q X).hom ≫ DerivedCategory.Q.map (T X).g ≫ (r X).inv)
    (hn : ∀ {X Y} (f : X ⟶ Y), ∃ g : T X ⟶ T Y,
      L.map f ≫ (p Y).hom = (p X).hom ≫ DerivedCategory.Q.map g.τ₁ ∧
      m f ≫ (q Y).hom = (q X).hom ≫ DerivedCategory.Q.map g.τ₂ ∧
      N.map f ≫ (r Y).hom = (r X).hom ≫ DerivedCategory.Q.map g.τ₃) :
    ∃ δ : ∀ X, N.obj X ⟶ (L.obj X)⟦(1 : ℤ)⟧,
      (∀ X, Triangle.mk (a X) (b X) (δ X) ∈ distTriang (DerivedCategory D)) ∧
      (∀ (X Y : E) (f : X ⟶ Y), L.map f ≫ a Y = a X ≫ m f) ∧
      (∀ (X Y : E) (f : X ⟶ Y), m f ≫ b Y = b X ≫ N.map f) ∧
      (∀ (X Y : E) (f : X ⟶ Y), N.map f ≫ δ Y =
        δ X ≫ (shiftFunctor _ (1 : ℤ)).map (L.map f)) := by
  let δ : N ⟶ L ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ) :=
    { app := fun X ↦ (r X).hom ≫ DerivedCategory.triangleOfSESδ (ht X) ≫
        (shiftFunctor _ (1 : ℤ)).map (p X).inv
      naturality := by
        intro X Y f
        obtain ⟨g, hg₁, hg₂, hg₃⟩ := hn f
        apply (cancel_mono ((shiftFunctor _ (1 : ℤ)).map (p Y).hom)).1
        simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
        simp only [CategoryTheory.Functor.map_id, Category.comp_id]
        rw [← Category.assoc, hg₃]
        rw [Category.assoc, ← DerivedCategory.triangleOfSESδ_naturality (ht X) (ht Y) g]
        have hh : (p X).inv ≫ L.map f ≫ (p Y).hom =
            DerivedCategory.Q.map g.τ₁ := by
          rw [hg₁, Iso.inv_hom_id_assoc]
        rw [hh]
      }
  refine ⟨δ.app, ?_, ?_, ?_, fun X Y f ↦ δ.naturality f⟩
  · intro X
    rw [ha X, hb X]
    apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished (ht X)) _
    refine Triangle.isoMk _ _ (p X) (q X) (r X) ?_ ?_ ?_
    · change ((p X).hom ≫ DerivedCategory.Q.map (T X).f ≫ (q X).inv) ≫
          (q X).hom = (p X).hom ≫ DerivedCategory.Q.map (T X).f
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · change ((q X).hom ≫ DerivedCategory.Q.map (T X).g ≫ (r X).inv) ≫
          (r X).hom = (q X).hom ≫ DerivedCategory.Q.map (T X).g
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · change ((r X).hom ≫ DerivedCategory.triangleOfSESδ (ht X) ≫
          (shiftFunctor _ (1 : ℤ)).map (p X).inv) ≫
          (shiftFunctor _ (1 : ℤ)).map (p X).hom =
          (r X).hom ≫ DerivedCategory.triangleOfSESδ (ht X)
      simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
      simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  · intro X Y f
    rw [ha X, ha Y]
    obtain ⟨g, hg₁, hg₂, hg₃⟩ := hn f
    apply (cancel_mono (q Y).hom).1
    simp only [Category.assoc]
    rw [← Category.assoc, hg₂]
    simp only [Category.assoc]
    rw [← Category.assoc, hg₁]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id, ← Functor.map_comp] using
      congrArg (fun k ↦ (p X).hom ≫ DerivedCategory.Q.map k) g.comm₁₂
  · intro X Y f
    rw [hb X, hb Y]
    obtain ⟨g, hg₁, hg₂, hg₃⟩ := hn f
    apply (cancel_mono (r Y).hom).1
    simp only [Category.assoc]
    rw [← Category.assoc, hg₃]
    simp only [Category.assoc]
    rw [← Category.assoc, hg₂]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id, ← Functor.map_comp] using
      congrArg (fun k ↦ (q X).hom ≫ DerivedCategory.Q.map k) g.comm₂₃

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)

/-- The open-cover triangle on the unbounded derived tower category, together with
naturality of the three arrows. The compact-support and level-evaluation assertions
are intentionally handled by `tower_open_cover_tail`.

(blueprint: lem-dla1-tower-open-cover-triangle-core).

Source: latest blueprint, tower-geometric Gluing paragraph; Stacks Tag 0152.

Proof: take the short exact complex presentations and comparison equations from
tower_open_cover_complex_presentation. Define the boundary by conjugating the
short-exact-sequence boundary with r and the shifted inverse of p. Transport its
distinguished triangle along p,q,r. A derived morphism admits a morphism between
these short exact complexes. Its two chain-map squares give naturality of the
first and second arrows; triangleOfSESδ_naturality gives naturality of the
boundary after cancelling the shifted comparison. Choices of representatives
need not be coherent, because this argument proves each naturality equation.
-/
theorem tower_open_cover_core {W U V X : Scheme.{u}}
    (aU : W ⟶ U) (aV : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    [IsOpenImmersion aU] [IsOpenImmersion aV]
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    (_intersection : IsPullback aU aV jU jV)
    (wU : aU ≫ jU = jW) (wV : aV ≫ jV = jW)
    (_cover : Set.range jU ∪ Set.range jV = Set.univ) :
    ∃ delta : ∀ M : SpTowerShriek.D l E X, M ⟶
        ((support l E b o jW).obj M)⟦(1 : ℤ)⟧,
      (∀ M : SpTowerShriek.D l E X,
        Triangle.mk (first l E b o aU aV jU jV jW wU wV M)
          (second l E b o jU jV M) (delta M) ∈
            distTriang (SpTowerShriek.D l E X)) ∧
      (∀ (M N : SpTowerShriek.D l E X) (h : M ⟶ N),
        (support l E b o jW).map h ≫
            first l E b o aU aV jU jV jW wU wV N =
          first l E b o aU aV jU jV jW wU wV M ≫
            biprod.map ((support l E b o jU).map h)
              ((support l E b o jV).map h)) ∧
      (∀ (M N : SpTowerShriek.D l E X) (h : M ⟶ N),
        biprod.map ((support l E b o jU).map h)
            ((support l E b o jV).map h) ≫
            second l E b o jU jV N =
          second l E b o jU jV M ≫ h) ∧
      (∀ (M N : SpTowerShriek.D l E X) (h : M ⟶ N),
        h ≫ delta N = delta M ≫ (shiftFunctor _ (1 : ℤ)).map
          ((support l E b o jW).map h)) := by
  obtain ⟨T, ht, p, q, r, ha, hb, hn⟩ :=
    tower_open_cover_complex_presentation l E b o aU aV jU jV jW
      _intersection wU wV _cover
  exact boundary_from_presentations (support l E b o jW) (𝟭 _)
    (fun M ↦ (support l E b o jU).obj M ⊞ (support l E b o jV).obj M)
    (fun h ↦ biprod.map ((support l E b o jU).map h) ((support l E b o jV).map h))
    T ht p q r
    (first l E b o aU aV jU jV jW wU wV) (second l E b o jU jV) ha hb (fun {M N} h ↦ hn M N h)

end AlgebraicGeometry.ProEtale.TowerOpenCover
