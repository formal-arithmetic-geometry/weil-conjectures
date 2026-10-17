/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalageTower
public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
import Sheaf.CategoryTheory.CartanEilenbergTruncationResolution
import Sheaf.CategoryTheory.CartanEilenbergMappedTotal
import Sheaf.CategoryTheory.LeftExactTruncationIso
import Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality
import Sheaf.CategoryTheory.DoubleComplexTruncationDecalage
import Sheaf.CategoryTheory.DerivedUpperTruncationComparison

/-! Existence part of the CE decalage spectral object comparison.
Source: Stacks Project, Tags 015X and 015K.
(blueprint: lem-sp-ce-decalage-spectral-object-iso-exists).
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A natural comparison morphism, known to be invertible only on intervals starting at
minus infinity.
Source: Stacks Project, Tag 015X, Remark 13.26.15; Tag 015K, Remark 13.21.4.
(blueprint: lem-sp-ce-decalage-spectral-object-iso-exists).

Proof. At finite cutoff b, identify the decalage step with the total of the horizontal
smart truncation at b-1. The CE augmentation gives a quasi-isomorphism from the
truncation of F(J) into a bounded-below complex of injectives. Compare its mapped
resolution with RG of that truncation using the inverse derived unit. The unique
augmentation square commutes for cutoff inclusions and for presentation maps. At
minus infinity use zero; at plus infinity use the full CE resolution. For interval
morphisms compare their mapping-cone triangles with the truncation triangles, using
the normalized first two maps and t-structure orthogonality to fix the third map.
The resulting comparison morphism commutes with the connecting arrows. Apply
cohomology to these triangle squares. For bottom intervals its map is invertible:
it is the composite of the resolution comparison, the cochain/derived truncation
comparison, and the resolution identification of F(J) with RF(X). The normalized
augmentation squares give presentation naturality, and cancellation of the monic
step inclusions extends it to every filtered lift of the specified total map.
No invertibility on general interval cohomology is claimed here; that follows
separately by the five lemma. -/
theorem cartanEilenberg_decalage_spectralObject_iso_exists
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
      (filteredComplexDecalageSpectralObjectFunctor C).obj
          (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) ⟶
        F.grothendieckSpectralObject G P.X,
      (∀ (P : CartanEilenbergPresentation F) (n : ℤ) (b : EInt),
        IsIso (((e P).hom n).app (ComposableArrows.mk₁
          (homOfLE (bot_le : (⊥ : EInt) ≤ b))))) ∧
      ∀ (P Q : CartanEilenbergPresentation F) (d : P.Comparison Q)
        (t : (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) ⟶
          (⟨Q.total G, L Q⟩ : FilteredObject (CochainComplex C ℤ))),
        t.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map d.α) (ComplexShape.up ℤ) →
        (filteredComplexDecalageSpectralObjectFunctor C).map t ≫ e Q =
          e P ≫ (F.grothendieckSpectralObjectFunctor G).map d.f := by
  sorry

end CategoryTheory
