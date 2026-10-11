/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.CategoryTheory.GrothendieckSSDoubleComplexModel

/-!
# Cocycle description of the Grothendieck left edge

Source: Stacks Project, Derived Categories, Lemma 015N and the second spectral sequence
of Lemma 015K (blueprint: lem-pc-grothendieck-edge-cocycle).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The left edge is induced by applying `G` to the cocycle quotient, and is an
isomorphism when the positive columns vanish. The equation is written after precomposition
with `G` of the cycles, identified with the cycles of the mapped complex by left exactness.
Source: Stacks Project, Derived Categories, Tags 015N and 015K
(blueprint: lem-pc-grothendieck-edge-cocycle).

Proof:
1. Apply F and GF to the injective resolution I. By def-sp-injective-resolutions,
   lem-sp-derived-well-defined and def-sp-left-exact-additive, the canonical isomorphisms
   I.isoRightDerivedObj identify their cohomology with the corresponding derived functors.
2. Choose a Cartan--Eilenberg resolution of F(I) by thm-sp-if-e1. By
   lem-pc-grothendieck-ss-double-complex-model and thm-sp-double-complex-spectral-sequences,
   the Grothendieck sequence has the total-complex image filtration. Acyclicity of F(I^q)
   makes the augmentation into each resolved row a quasi-isomorphism after applying G.
   Left exactness identifies G of the cycles with the cycles after G; the quotient map
   to horizontal cohomology is G applied to the cycles-to-cohomology quotient. Thus the
   quotient/inclusion left edge of lem-sp-grothendieck-edge-maps satisfies the displayed
   equation. The canonical resolution identifications remove dependence on I.
3. The first-quadrant total-complex filtration is finite, exhaustive and separated,
   by thm-sp-grothendieck and lem-pc-grothendieck-ss-double-complex-model. Its steps are
   transported to the abutment by the canonical spectral-object identification.
4. If all positive columns R^p G(R^q F(X)) vanish, the sequence is concentrated in
   column zero from page two. Apply lem-sp-edge-collapse to the exact couple
   def-sp-exact-couple and its convergence def-sp-convergence. The sole graded piece
   is the entire abutment, so its left edge is an isomorphism in every degree.
-/
theorem grothendieck_left_edge_cocycle
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (X : A) (I : InjectiveResolution X) :
    (∀ n : ℕ, ∃ c :
        G.obj (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles n) ⟶
          (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles n,
      c ≫ (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles n =
        G.map (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles n) ∧
      c ≫ (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ n ≫
          (I.isoRightDerivedObj (F ⋙ G) n).inv ≫
          (F.grothendieckLeftEdgeMap G hFG n).app X ≫
          G.map (I.isoRightDerivedObj F n).hom =
        G.map (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ n)) ∧
    (∃ HF : ∀ n : ℕ, DecreasingFiltration (((F ⋙ G).rightDerived n).obj X),
      (∀ (n : ℕ) (p : ℤ), (HF n).step p =
        (Subobject.«exists» ((F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app X)).obj
          ((F.grothendieckSpectralObject G X).imageFiltration (n : ℤ)
            ((n : ℤ) + 1 - p))) ∧
      (∀ n : ℕ, (HF n).IsFinite ∧ (HF n).IsExhaustive ∧ (HF n).IsSeparated)) ∧
    ((∀ p q : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived q).obj X))) →
      ∀ n : ℕ, IsIso ((F.grothendieckLeftEdgeMap G hFG n).app X)) := by
  sorry

end CategoryTheory
