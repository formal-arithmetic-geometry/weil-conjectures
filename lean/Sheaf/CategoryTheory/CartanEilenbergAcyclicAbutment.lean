/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.CategoryTheory.GrothendieckComposablePair
public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Sheaf.CategoryTheory.CartanEilenbergAugmentationComparison
import Sheaf.CategoryTheory.CartanEilenbergSecondImageTruncation
import Sheaf.CategoryTheory.GrothendieckCanonicalImageFiltration

/-! # CartanEilenbergAcyclicAbutment

Source: Stacks Project, Derived Categories, Tags 015J, 015K, 015N and 015X
(blueprint: lem-sp-ce-acyclic-abutment).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The acyclic column computation identifies total cohomology with the derived composite
and matches the second image filtration with the truncation image filtration.
Source: Stacks Project, Derived Categories, Tag 015N, collapsing first spectral sequence
and convergence of the second; Tag 015X, filtered comparison
(blueprint: lem-sp-ce-acyclic-abutment).

Proof:
1. Map the common augmentation into resolution-degree-zero total summands, using the
   extend isomorphisms and the total-complex inclusions. The augmentation is a bicomplex
   map, so its components commute with differentials, including the totalization sign.
2. Each column resolves F(J^p). Since J^p is injective and F sends injectives to
   G-acyclics, its mapped positive cohomology vanishes and its degree-zero cohomology
   is GF(J^p). Thus the augmentation is a quasi-isomorphism by the first-quadrant
   row-collapse argument. Invert its homology map and compose with the canonical
   injective-resolution computation of the right-derived composite to define h.
   Naturality of the augmentation and of that computation proves the comparison square.
3. Transport the images of the second filtered-subcomplex homology maps through h.
   For total degree n and filtration degree p put q = n-p. In the shifted cycle
   filtration Dec(L)^(-q), degree-n cycles are exactly the total cycles in L^p:
   the extra differential condition is automatic on cycles. Thus both filtered
   subcomplexes have the same image in total cohomology, irrespective of the different
   boundary presentations. Before applying G, the corresponding Dec filtration on
   Tot(I) is a filtered injective resolution of the canonical truncation filtration:
   the horizontal cycle and boundary resolutions verify the graded quasi-isomorphisms,
   and their injective terms split the degreewise filtrations. Since G is left exact
   and additive, it preserves the kernels and finite sums defining Dec, so its image
   is Dec(L). The filtered injective computation of Tag 015X therefore identifies
   Dec(L)^(-q) with RG(tau_{<=q} F(J)), compatibly with the maps into the full derived
   object. The image is the canonical truncation image. For negative steps
   the first-quadrant filtered complex
   is the whole total complex. Thus these steps are independent of presentation and
   define HF on X. The filtered comparison maps give naturality of every step.
4. In total degree n the filtration is whole at 0 and zero at n+1. The first-quadrant
   spectral-object computation identifies the graded truncation image with any page
   r at (p,q) for r > max(p,q+1): the first-quadrant vanishings allow the outer
   spectral-object indices to be replaced by bottom and top, and the short exact
   sequence of successive images computes the quotient. The step equality above
   transports that quotient to the graded piece of HF. Composing with the page-r
   component of the supplied c yields the assertion; no naturality of c is needed.
-/
theorem exists_cartanEilenberg_acyclic_abutment
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (E : A ⥤ E₂CohomologicalSpectralSequence C)
    (L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G))
    (c : ∀ X : A, E.obj X ≅ (F.grothendieckSpectralObject G X).E₂SpectralSequence)
    (hL : ∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
        (L P).complexStep p n =
          ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p)) :
    ∃ (h : ∀ (P : CartanEilenbergPresentation F) (n : ℕ),
        (P.total G).homology (n : ℤ) ≅ ((F ⋙ G).rightDerived n).obj P.X)
      (HF : ∀ (X : A) (n : ℕ), DecreasingFiltration (((F ⋙ G).rightDerived n).obj X)),
      (∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) (n : ℕ),
        HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c.α)
            (ComplexShape.up ℤ)) (n : ℤ) ≫ (h Q n).hom =
          (h P n).hom ≫ ((F ⋙ G).rightDerived n).map c.f) ∧
      (∀ P : CartanEilenbergPresentation F,
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
              (P.J.isoRightDerivedObj (F ⋙ G) n).inv)) ∧
      (∀ (P : CartanEilenbergPresentation F) (p : ℤ) (n : ℕ),
        (HF P.X n).step p = imageSubobject
          (HomologicalComplex.homologyMap ((L P).step p).arrow (n : ℤ) ≫ (h P n).hom)) ∧
      (∀ (X : A) (p q : ℕ) (r : ℤ) (hr : 2 ≤ r),
        max (p : ℤ) ((q : ℤ) + 1) < r →
          Nonempty (((E.obj X).page r hr).X ((p : ℤ), (q : ℤ)) ≅
            (HF X (p + q)).gradedPiece (p : ℤ))) ∧
      (∀ (X Y : A) (f : X ⟶ Y) (n : ℕ) (p : ℤ),
        ∃ a : ((HF X n).step p : C) ⟶ ((HF Y n).step p : C),
          a ≫ ((HF Y n).step p).arrow =
            ((HF X n).step p).arrow ≫ ((F ⋙ G).rightDerived n).map f) ∧
      (∀ (P : CartanEilenbergPresentation F) (n p : ℕ),
        (HF P.X n).step (p : ℤ) =
          (Subobject.«exists» ((F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app P.X)).obj
            ((F.grothendieckSpectralObject G P.X).imageFiltration (n : ℤ)
              ((n : ℤ) + 1 - (p : ℤ)))) := by
  obtain ⟨h, hnat, haug⟩ := exists_cartanEilenberg_augmentation_comparison F G hFG
  obtain ⟨HF, hstep, hstable, hfnat⟩ :=
    exists_grothendieck_canonical_image_filtration F G hFG E c
  have himage := cartanEilenberg_second_image_eq_truncation F G hFG L hL h haug
  refine ⟨h, HF, hnat, haug, ?_, hstable, hfnat, ?_⟩
  · intro P p n
    exact (hstep P.X n p).trans (himage P p n).symm
  · intro P n p
    exact hstep P.X n (p : ℤ)

end CategoryTheory
