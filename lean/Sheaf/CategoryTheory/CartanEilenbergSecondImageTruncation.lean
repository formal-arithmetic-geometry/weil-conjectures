/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.CategoryTheory.GrothendieckComposablePair
public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # CartanEilenbergSecondImageTruncation

Source: Stacks Project, Derived Categories, Tags 015N and 015K and 015X.
(blueprint: lem-sp-ce-second-image-truncation).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The second filtered-total image, normalized by the augmentation computation,
is the canonical derived truncation image in every integer filtration degree.
Source: Stacks Project, Derived Categories, Tags 015N and 015X.
(blueprint: lem-sp-ce-second-image-truncation).

Proof: Put q = n-p. In degree n the cycles of Dec(L)^(-q) are precisely total cycles
lying in L^p: the differential condition in the definition of Dec is automatic
on cycles. Thus their images in full total cohomology agree, even though their
boundary presentations differ. Before applying G, the Dec filtration of Tot(I)
resolves the canonical truncation filtration of F(J). Indeed the horizontal cycle,
boundary and homology augmentation maps in the presentation are quasi-isomorphisms;
they verify the graded comparison, and their injective terms split the degreewise
filtrations. Left exact additive G preserves the kernels and finite direct sums
defining Dec. The filtered injective computation of Tag 015X therefore identifies
the mapped Dec piece with RG(tau_{<=q} F(J)), compatibly with the map into RG(F(J)).
The augmentation normalization identifies this full-object comparison with the
canonical acyclic-composite isomorphism. Taking the image gives the asserted
transport of the spectral-object imageFiltration step. For p<0, first-quadrant
support makes L^p the whole total complex, and q>=n makes the truncation image
whole as well; the same equality holds. This includes n=0 and the zero steps p>n. -/
theorem cartanEilenberg_second_image_eq_truncation
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G))
    (hL : ∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
        (L P).complexStep p n =
          ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p))
    (h : ∀ (P : CartanEilenbergPresentation F) (n : ℕ),
        (P.total G).homology (n : ℤ) ≅ ((F ⋙ G).rightDerived n).obj P.X)
    (haug : (∀ P : CartanEilenbergPresentation F,
        ∃ a : (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex).extend
            ComplexShape.embeddingUpNat ⟶ P.total G,
          (∀ n : ℕ, a.f (n : ℤ) =
            (HomologicalComplex.extendXIso
              (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
              ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
            G.map (F.map (P.J.cocomplex.extendXIso ComplexShape.embeddingUpNat
              (rfl : (n : ℤ) = n)).inv ≫ (P.e.f (n : ℤ)).f 0) ≫
            (HomologicalComplex.extendXIso
              ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (P.I.X (n : ℤ)))
              ComplexShape.embeddingUpNat (rfl : (0 : ℤ) = 0)).inv ≫
            HomologicalComplex₂.ιTotalOrZero
              ((CartanEilenbergPresentation.mappedFunctor G).obj P.I)
              (ComplexShape.up ℤ) (n : ℤ) 0 (n : ℤ)) ∧
          (∀ n : ℕ, HomologicalComplex.homologyMap a (n : ℤ) ≫ (h P n).hom =
            (HomologicalComplex.extendHomologyIso
              (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
              ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
              (P.J.isoRightDerivedObj (F ⋙ G) n).inv))) :
    ∀ (P : CartanEilenbergPresentation F) (p : ℤ) (n : ℕ),
      imageSubobject
        (HomologicalComplex.homologyMap ((L P).step p).arrow (n : ℤ) ≫ (h P n).hom) =
      (Subobject.«exists» ((F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app P.X)).obj
        ((F.grothendieckSpectralObject G P.X).imageFiltration (n : ℤ)
          ((n : ℤ) + 1 - p)) := by
  sorry

end CategoryTheory
