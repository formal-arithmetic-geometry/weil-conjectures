/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.CategoryTheory.FilteredComplexCanonicalModel
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.SpectralObjectPageTwoFunctor
import Sheaf.CategoryTheory.FilteredComplexDecalageComparison
import Sheaf.CategoryTheory.CartanEilenbergDecalageSpectralObject

/-! # The canonical CE quotient sequence and truncation

Source: Stacks Project, Tags 015X, 015K and 012K.
(blueprint: lem-sp-ce-canonical-truncation-comparison).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem exists_spectralObject_sequence_iso
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {X Y : Abelian.SpectralObject C EInt} (i : X ≅ Y) :
    ∃ e : X.E₂SpectralSequence ≅ Y.E₂SpectralSequence,
      ∀ p q : ℤ,
        (Abelian.SpectralObject.pageTwoComparison Y e p q (p + q) rfl).hom =
          (Abelian.SpectralObject.pageTwoComparison X (Iso.refl _) p q (p + q) rfl).hom ≫
            (i.hom.hom (p + q)).app (ComposableArrows.mk₁
              (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))) := by
  obtain ⟨E, c, hc⟩ := Abelian.SpectralObject.exists_pageTwo_functor
    (𝟭 (Abelian.SpectralObject C EInt))
  let e := (c X).symm ≪≫ E.mapIso i ≪≫ c Y
  refine ⟨e, ?_⟩
  intro p q
  have hi := hc X Y i.hom p q
  dsimp only [Abelian.SpectralObject.pageTwoComparison, Iso.trans_hom,
    Functor.mapIso_hom, e, Iso.symm_hom, SpectralSequence.comp_hom,
    HomologicalComplex.comp_f] at hi ⊢
  simp only [HomologicalComplex.eval, SpectralSequence.pageFunctor, Category.assoc] at hi ⊢
  simp only [SpectralSequence.comp_hom, HomologicalComplex.comp_f, Iso.refl_hom,
    SpectralSequence.id_hom, HomologicalComplex.id_f, Category.id_comp, Category.assoc] at *
  erw [hi]
  have hX := congrArg (fun k ↦ (k.hom 2).f (p, q)) (c X).inv_hom_id
  simp only [SpectralSequence.comp_hom, HomologicalComplex.comp_f,
    SpectralSequence.id_hom, HomologicalComplex.id_f] at hX
  rw [reassoc_of% hX]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Compare the explicit, normalized quotient sequence of a CE second filtration
with the truncation spectral object; only the first-page square is required here.
Source: Stacks Project, Tag 015X, Remark 13.26.15, and Tags 015K and 012K.
(blueprint: lem-sp-ce-canonical-truncation-comparison).

Proof. Form the concrete decalage tower, whose step at q is Dec(L)^(1-q),
with zero and the full total at the infinite endpoints. Its mapping-cone
spectral object gives an intermediate sequence. The universal theorem
filteredComplex_decalage_comparison compares the canonical quotient sequence
with this intermediate sequence. It identifies quotient representatives and
normalizes the first-page map for every filtered chain map.
The theorem cartanEilenberg_decalage_spectralObject compares the intermediate
spectral object with the derived truncation spectral object, naturally for every
CE presentation comparison and every filtered lift of its mapped total map.
Its argument identifies horizontal smart truncations with decalage steps, uses
the normalized CE augmentations to compute the derived truncation tower, and
compares the interval cones and their connecting maps before taking cohomology.
Apply exists_pageTwo_functor to the identity functor on spectral objects. The
resulting functor maps the spectral-object isomorphisms to sequence isomorphisms;
conjugating by its object comparisons gives the desired normalized sequence
isomorphisms. Compose them with the universal quotient comparison. The first
comparison's page-two naturality equation and the cohomology component of the
second comparison's naturality equation compose, by associativity, to the
stated square. No arbitrary cohomology isomorphism or filtered homotopy choice
is used in this assembly. -/
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
                  (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))) := by
  classical
  obtain ⟨a, ha⟩ := filteredComplex_decalage_comparison C
  obtain ⟨b, hb⟩ := cartanEilenberg_decalage_spectralObject F G L hL
  choose c hc using fun (P : CartanEilenbergPresentation F) ↦
    exists_spectralObject_sequence_iso (b P)
  let e := fun (P : CartanEilenbergPresentation F) ↦
    a (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) ≪≫ c P
  refine ⟨e, ?_⟩
  intro P Q d t ht p q
  have ha' := ha t p q
  have hb' := congrArg (fun k ↦ (k.hom (p + q)).app (ComposableArrows.mk₁
    (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt))))) (hb P Q d t ht)
  have he (R : CartanEilenbergPresentation F) :
      (Abelian.SpectralObject.pageTwoComparison
        (F.grothendieckSpectralObject G R.X) (e R) p q (p + q) rfl).hom =
      (Abelian.SpectralObject.pageTwoComparison
        ((filteredComplexDecalageSpectralObjectFunctor C).obj
          (⟨R.total G, L R⟩ : FilteredObject (CochainComplex C ℤ)))
        (a _) p q (p + q) rfl).hom ≫
          ((b R).hom.hom (p + q)).app (ComposableArrows.mk₁
            (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))) := by
    have h := hc R p q
    dsimp only [e, Abelian.SpectralObject.pageTwoComparison, Iso.trans_hom,
      Functor.mapIso_hom] at h ⊢
    simp only [HomologicalComplex.eval, SpectralSequence.pageFunctor,
      SpectralSequence.comp_hom, HomologicalComplex.comp_f, Category.assoc,
      Iso.refl_hom, SpectralSequence.id_hom, HomologicalComplex.id_f,
      Category.id_comp] at h ⊢
    rw [h]
  simp only [Abelian.SpectralObject.comp_hom, NatTrans.comp_app] at hb'
  rw [he P, he Q, ← Category.assoc, ha', Category.assoc, hb', ← Category.assoc]

end CategoryTheory
