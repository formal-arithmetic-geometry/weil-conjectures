/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.CategoryTheory.FilteredComplexCanonicalModel
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.SpectralObjectPageTwoFunctor
import Sheaf.Paper.CartanEilenbergLeftExactCohomology
import Sheaf.CategoryTheory.CartanEilenbergTruncationResolution
import Sheaf.CategoryTheory.LeftExactTruncationIso
import Sheaf.CategoryTheory.CartanEilenbergMappedTotal
import Sheaf.CategoryTheory.CartanEilenbergDerivedTruncationCohomology
import Sheaf.CategoryTheory.FilteredComplexDecalage

/-! # The canonical CE quotient sequence and truncation

Source: Stacks Project, Tags 015X, 015K and 012K.
(blueprint: lem-sp-ce-canonical-truncation-comparison).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Compare the explicit, normalized quotient sequence of a CE second filtration
with the truncation spectral object; only the first-page square is required here.
Source: Stacks Project, Tag 015X, Remark 13.26.15, and Tags 015K and 012K.
(blueprint: lem-sp-ce-canonical-truncation-comparison).

Proof. Before applying G, use DecreasingFiltration.exists_decalage to form
the unique functorial decalage of the second filtration V by
Dec(V)^a Tot(I)^n = V^(a+n) intersect d^{-1}(V^(a+n+1)). The augmentation from
F(J) restricts from its upper smart truncation in degree q to Dec(V)^(-q).
The proved cartanEilenberg_truncation_resolution supplies the unique
augmentation and a bounded-below K-injective total for every horizontal smart
truncation, with its original total sign convention. The CE augmentations on
horizontal cycles, boundaries and cohomology show that
the induced graded maps are quasi-isomorphisms. The injective horizontal cycle
and boundary terms split their short exact sequences, so the Dec graded terms
are injective and the step inclusions split degreewise. Thus these maps give a
filtered injective resolution of the smart truncation filtration of F(J).
The proved leftExact_truncation_iso identifies the cycles after applying G,
and cartanEilenberg_mapped_total_iso commutes G with the finite diagonals.
The proved cartanEilenberg_derived_truncation_cohomology computes the
objectwise derived cohomology of these upper truncations. Compare this
resolution to the derived truncation diagram by the injective
comparison theorem. Its comparison maps are unique up to filtered homotopy,
and additive G preserves the homotopies. On quotient cycles and boundaries,
decalage shifts the spectral-sequence page by one. Reindexing its bidegrees
therefore identifies the CE quotient sequence starting at page two with the
truncation spectral sequence. The representative differential formula and the
normalized homology quotient formula used in the canonical model are precisely
the formulas of that comparison. Consequently it commutes with differentials
and successor-page isomorphisms and gives an isomorphism of entire sequences.
The split horizontal cohomology calculation, with the sign (-1)^(q*j) on the
resolution direction, identifies its first-page map with interval cohomology
of the truncation spectral object. Every map of CE presentations commutes with
these augmented cycle and boundary diagrams. Passing through kernels and
cokernels gives the displayed first-page naturality square for every filtered
lift of the mapped total map. Equality of the specified filtration in each
degree suffices throughout: subcomplexes and their inclusions are determined
by their degreewise subobjects. No acyclicity assumption on F(J) for G is used. -/
theorem cartanEilenberg_canonical_truncation_comparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G))
    (hL : ∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
      (L P).complexStep p n =
        ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p)) :
    ∃ e : ∀ P : CartanEilenbergPresentation F,
      (filteredComplexCanonicalModel C).S.obj
          (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) ≅
        (F.grothendieckSpectralObject G P.X).E₂SpectralSequence,
      ∀ (P Q : CartanEilenbergPresentation F) (d : P.Comparison Q)
        (t : (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) ⟶
          (⟨Q.total G, L Q⟩ : FilteredObject (CochainComplex C ℤ))),
        t.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map d.α) (ComplexShape.up ℤ) →
        ∀ p q : ℤ,
          (((filteredComplexCanonicalModel C).S.map t).hom 2).f (p, q) ≫
              (Abelian.SpectralObject.pageTwoComparison
                (F.grothendieckSpectralObject G Q.X) (e Q) p q (p + q) rfl).hom =
            (Abelian.SpectralObject.pageTwoComparison
              (F.grothendieckSpectralObject G P.X) (e P) p q (p + q) rfl).hom ≫
              (((F.grothendieckSpectralObjectFunctor G).map d.f).hom (p + q)).app
                (ComposableArrows.mk₁
                  (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))) := by sorry

end CategoryTheory
