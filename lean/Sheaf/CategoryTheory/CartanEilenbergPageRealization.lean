/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredPageTwoModel

/-! # CartanEilenbergPageRealization

Source: Stacks Project, Derived Categories, Tags 015J, 015K, 015N and 015X
(blueprint: lem-sp-ce-page-realization).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Realize the resolution-degree filtered total complexes functorially from page two,
with the derived page computation and its comparison to the truncation spectral object.
No acyclicity assumption is needed for this page construction.
Source: Stacks Project, Derived Categories, Tags 015H, 015J, 015K, 015N and 015X,
proof of the second spectral sequence (blueprint: lem-sp-ce-page-realization).

Proof:
1. Form the second degree filtration on each mapped total complex. The quotient-complex
   image construction gives a common FilteredPageTwoModel. Its pages vanish outside the
   first quadrant because both degrees of the mapped bicomplex are nonnegative.
2. Choose a presentation for each object, lift maps of objects to injective resolutions
   and then to Cartan--Eilenberg resolutions. Comparison independence identifies the
   induced page maps for any two lifts, including identity and composite lifts. These
   equations define the functor E and the presentation comparisons s.
3. Each horizontal row has injective cycles and boundaries, so the short exact sequences
   defining its cohomology split. The additive G preserves these splittings. Horizontal
   cohomology of G(I) is therefore G of horizontal cohomology of I. The latter complexes
   resolve the cohomology of F(J), giving R^p G(R^q F(X)) on page two, naturally in X.
   The induced resolution differential has sign (-1)^q; multiply its term of resolution
   degree j by (-1)^(q*j) to identify it with the usual injective-resolution differential.
4. Use the filtered injective-resolution comparison of Tag 015X. More explicitly, let
   V be the second filtration on Tot(I), before applying G, and use its shifted cycle
   filtration Dec(V)^a Tot(I)^n = {x in V^(a+n) : dx in V^(a+n+1)}. The augmentation
   of the canonical filtration tau_{<=q} F(J) lands in Dec(V)^(-q): in degree n <= q
   its image lies in resolution degree zero, and in degree q its differential is zero
   because tau_{<=q} uses the cycles of F(J) there. The horizontal cycle, boundary and
   homology resolutions give a quasi-isomorphism on each graded quotient. In each
   degree the Dec filtration splits: its terms and graded terms are finite sums of
   horizontal cycles, boundaries and injective terms, all injective. Thus this is a
   filtered injective resolution. Compare it with the filtered injective computation
   of the truncation spectral object before applying G. The comparison and its inverse
   are unique up to filtered homotopy; additivity of G preserves these homotopies,
   giving the same derived filtered object and the same spectral sequence.
   The cycle and boundary formulas for Dec shift the original filtered pages by one;
   after reindexing by the resolution degree this compares the original E2 sequence
   with the spectral sequence of the truncation triangles of RF(X). The connecting
   maps are induced by the same complex differential, so the comparison respects all
   differentials and page homology isomorphisms, giving c. At page two its single-degree
   quotient is H^q(F(J))[-q]; its derived homology is exactly the natural isomorphism
   grothendieckSpectralObjectHIso. Define k using the first-page comparison and c,
   and e by composition with this natural isomorphism. The split-row computation in
   step 3 identifies these with the CE comparisons, so enat and both equations hold.
-/
theorem exists_cartanEilenberg_page_realization
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    ∃ (M : FilteredPageTwoModel C)
      (E : A ⥤ E₂CohomologicalSpectralSequence C)
      (L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G))
      (s : ∀ P : CartanEilenbergPresentation F,
        E.obj P.X ≅ M.S.obj (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)))
      (e : ∀ (X : A) (p q : ℕ),
        ((E.obj X).page 2).X ((p : ℤ), (q : ℤ)) ≅
          (G.rightDerived p).obj ((F.rightDerived q).obj X))
      (c : ∀ X : A, E.obj X ≅ (F.grothendieckSpectralObject G X).E₂SpectralSequence)
      (k : ∀ (X : A) (p q : ℕ),
        ((E.obj X).page 2).X ((p : ℤ), (q : ℤ)) ≅
          ((F.grothendieckSpectralObject G X).H (p + q : ℕ)).obj
            (ComposableArrows.mk₁ (homOfLE
              (by simp : ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt))))),
      (∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
        (L P).complexStep p n =
          ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p)) ∧
      (∀ (X Y : A) (f : X ⟶ Y) (p q : ℕ),
        ((E.map f).hom 2).f ((p : ℤ), (q : ℤ)) ≫ (e Y p q).hom =
          (e X p q).hom ≫ (F.rightDerived q ⋙ G.rightDerived p).map f) ∧
      (∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q),
        ∃ t : (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) ⟶
            (⟨Q.total G, L Q⟩ : FilteredObject (CochainComplex C ℤ)),
          t.hom = HomologicalComplex₂.total.map
            ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ) ∧
          E.map c.f ≫ (s Q).hom = (s P).hom ≫ M.S.map t) ∧
      (∀ (X : A) (p q : ℕ),
        (k X p q).hom = ((c X).hom.hom 2).f ((p : ℤ), (q : ℤ)) ≫
          ((F.grothendieckSpectralObject G X).spectralSequenceFirstPageXIso
            Abelian.SpectralObject.coreE₂Cohomological
            ((p : ℤ), (q : ℤ)) _ _ rfl rfl (p + q : ℕ) (by push_cast; rfl)).hom ∧
        (e X p q).hom = (k X p q).hom ≫
          (F.grothendieckSpectralObjectHIso G p q (p + q : ℕ) q (q + 1)
            (by push_cast; rfl) rfl rfl).hom.app X) := by
  sorry

end CategoryTheory
