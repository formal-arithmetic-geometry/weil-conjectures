/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredPageTwoModel
public import Sheaf.CategoryTheory.SpectralObjectPageTwoFunctor
import Sheaf.Algebra.Homology.FilteredComplexZBDescription
import Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence
import Sheaf.Paper.CartanEilenbergLeftExactCohomology

/-! # Filtered Cartan--Eilenberg comparison with truncation

Source: Stacks Project, Tags 012K, 015K and 015X
(blueprint: lem-sp-ce-filtered-truncation-comparison).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Realize a fixed functorial truncation spectral sequence by the second filtration
of mapped Cartan--Eilenberg totals. Only the filtered comparison is asserted here;
there is no choice or computation of the derived page-two isomorphisms.
Source: Stacks Project, Tags 012K, 015K and 015X
(blueprint: lem-sp-ce-filtered-truncation-comparison).

Proof: construct the quotient-image spectral sequence on all filtered complexes by
kernels and images in the three adjacent total degrees. Use the complex differential
on cycle representatives for its differentials and the induced quotient identifications
for successor pages. These choices define a single coherent FilteredPageTwoModel M.
On each CE total take the second-degree subcomplex filtration V. Apply comparison
independence to obtain filtered lifts of all presentation comparisons. Before applying
G, set Dec(V)^a Tot(I)^n = V^(a+n) Tot(I)^n intersect
 d^{-1}(V^(a+n+1) Tot(I)^(n+1)). The augmentation of tau_{<=q} F(J) lies in
Dec(V)^(-q): below q its resolution degree is zero, while at q its differential is zero.
The resolutions of horizontal cycles, boundaries and homology identify the graded
augmentation as a quasi-isomorphism. Horizontal cycles and boundaries are injective,
so the degreewise short exact sequences split; hence the Dec steps and their graded
quotients are injective. This gives a filtered injective resolution of the truncation
filtration. Its comparison with any other filtered injective resolution is unique up
to filtered homotopy. Applying the additive G preserves these homotopies. The Dec cycle
and boundary formulas shift pages once and reindex them by (resolution degree,
horizontal degree), identifying the V spectral sequence from page two with the
truncation spectral sequence. The maps on representative differentials and the maps
on quotient homology are the same on both sides, so this identifies the entire
spectral sequences, not only their objects. At page two this comparison is natural
for every CE lift by the horizontal split-cohomology computation; the factor
(-1)^(q*j) removes the resolution differential sign. The assumed first-page naturality
identifies it with the maps of E. Spectral-sequence morphisms are determined by page two:
induction through their successor-page homology isomorphisms proves equality on all
later pages. Compose the truncation comparison with c to obtain s. The filtered lift
and the comparison equation follow, for each presentation comparison. -/
theorem exists_cartanEilenberg_filtered_truncation_comparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (E : A ⥤ E₂CohomologicalSpectralSequence C)
    (c : ∀ X : A, E.obj X ≅ (F.grothendieckSpectralObject G X).E₂SpectralSequence)
    (hc : ∀ (X Y : A) (f : X ⟶ Y) (p q : ℤ),
      ((E.map f).hom 2).f (p, q) ≫
          (Abelian.SpectralObject.pageTwoComparison
            (F.grothendieckSpectralObject G Y) (c Y) p q (p + q) rfl).hom =
        (Abelian.SpectralObject.pageTwoComparison
          (F.grothendieckSpectralObject G X) (c X) p q (p + q) rfl).hom ≫
          (((F.grothendieckSpectralObjectFunctor G).map f).hom (p + q)).app
            (ComposableArrows.mk₁
              (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt))))) :
    ∃ (M : FilteredPageTwoModel C)
      (L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G))
      (s : ∀ P : CartanEilenbergPresentation F,
        E.obj P.X ≅ M.S.obj (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ))),
      (∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
        (L P).complexStep p n =
          ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p)) ∧
      (∀ (P Q : CartanEilenbergPresentation F) (d : P.Comparison Q),
        ∃ t : (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) ⟶
            (⟨Q.total G, L Q⟩ : FilteredObject (CochainComplex C ℤ)),
          t.hom = HomologicalComplex₂.total.map
            ((CartanEilenbergPresentation.mappedFunctor G).map d.α) (ComplexShape.up ℤ) ∧
          E.map d.f ≫ (s Q).hom = (s P).hom ≫ M.S.map t) := by sorry

end CategoryTheory
