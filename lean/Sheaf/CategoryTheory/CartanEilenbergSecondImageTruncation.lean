/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckComposablePair
public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Sheaf.CategoryTheory.CartanEilenbergDecalageTruncationDiagram
import Sheaf.CategoryTheory.FilteredComplexDecalageImage
import all Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries
import all Sheaf.CategoryTheory.GrothendieckCanonicalImageFiltration
import Sheaf.CategoryTheory.DoubleComplexTotal

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

Proof. If p<=0 the first-quadrant filtration step and the canonical spectral
image filtration are both top. If n<p the degree-n term of the filtration step
vanishes and the spectral image filtration is bottom. In the remaining range
put q=n-p. The cycles of Dec(L)^(-q) are precisely the total cycles lying in
L^p, so their ambient cohomology images agree. The horizontal good cut of the
Cartan--Eilenberg resolution represents the canonical derived truncation:
its augmentation is a quasi-isomorphism on columns, using the horizontal cycle
augmentation at the cut boundary. Its full and cut totals have injective terms.
The mapped cut total identifies with Dec(L)^(-q) by the degreewise boundary-kernel
identity, functor/truncation compatibility and naturality of the total-flip signs.
Naturality of the derived-functor unit gives the resulting cohomology square with
the canonical spectral-object map. The resolution-unit comparison and the given
augmentation normalization identify its full comparison with h after canonical
transport. Push the equality of decalage and step images through this comparison,
use the commuting square, and cancel the cut isomorphism. The spectral-object
imageFiltration is the image of this same bottom-to-truncation-to-top map. -/
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
  change F.IsAcyclicComposablePair G at hFG
  intro P p n
  by_cases hp : p ≤ 0
  · let T := (CartanEilenbergPresentation.mappedFunctor G).obj P.I
    have hT (i j : ℤ) (hij : i < 0 ∨ j < 0) : IsZero ((T.X i).X j) := by
      rcases hij with hi | hj
      · exact (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero
          ((ComplexShape.embeddingUpNat.extendFunctor C).map_isZero
            ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map_isZero (P.zero_neg i hi)))
      · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat j
          (fun m hm ↦ by change (m : ℤ) = j at hm; omega)
    have htop (m : ℤ) : (L P).complexStep p m = ⊤ := by
      rw [hL P p m]
      apply top_unique
      rw [← T.secondFiltration_zero hT m]
      exact (T.secondFiltration m).antitone_step hp
    have hi (m : ℤ) : IsIso (((L P).step p).arrow.f m) := by
      apply (Subobject.isIso_iff_mk_eq_top _).mpr
      rw [← imageSubobject_mono]
      exact htop m
    have : IsIso ((L P).step p).arrow := HomologicalComplex.Hom.isIso_of_components _
    have : IsIso (HomologicalComplex.homologyMap ((L P).step p).arrow (n : ℤ)) :=
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (n : ℤ)).map_isIso _
    rw [imageSubobject_mono, Subobject.mk_eq_top_of_isIso,
      Abelian.SpectralObject.imageFiltration_eq_top _ _ _ (by omega)]
    rw [Subobject.exists_obj_top, imageSubobject_mono, Subobject.mk_eq_top_of_isIso]
  by_cases hpn : (n : ℤ) < p
  · have hbot : (L P).complexStep p (n : ℤ) = ⊥ := by
      rw [hL P p (n : ℤ)]
      simp [HomologicalComplex₂.secondFiltration, Finset.Icc_eq_empty_of_lt hpn]
    have hz : (((L P).step p).arrow.f (n : ℤ)) = 0 := by
      apply Subobject.mk_eq_bot_iff_zero.mp
      rwa [← imageSubobject_mono, ← DecreasingFiltration.complexStep]
    have hx := IsZero.of_mono_eq_zero _ hz
    have hh := (HomologicalComplex.ExactAt.of_isZero hx).isZero_homology
    have hzero : HomologicalComplex.homologyMap ((L P).step p).arrow (n : ℤ) = 0 :=
      hh.eq_of_src _ _
    simp only [hzero, zero_comp, imageSubobject_zero]
    rw [Abelian.SpectralObject.imageFiltration_eq_bot _ _ _ (by omega),
      Subobject.exists_iso_map, Subobject.map_bot]
  obtain ⟨a, ha, hnorm⟩ := haug P
  obtain ⟨e, d, hcomm, henorm⟩ := cartanEilenberg_decalage_truncation_diagram
    F G hFG P (L P) (hL P) a ha ((n : ℤ) - p) n (by omega)
  have hAugIso : IsIso
      (HomologicalComplex.homologyMap a (n : ℤ) ≫ (h P n).hom) := by
    rw [hnorm n]
    infer_instance
  have : IsIso (HomologicalComplex.homologyMap a (n : ℤ)) :=
    IsIso.of_isIso_comp_right _ (h P n).hom
  have he : e.hom ≫ (F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app P.X =
      (h P n).hom := by
    apply (cancel_epi (HomologicalComplex.homologyMap a (n : ℤ))).mp
    exact henorm.trans (hnorm n).symm
  have himage := congrArg (fun S ↦ (Subobject.«exists» (h P n).hom).obj S)
    (DecreasingFiltration.decalage_image (P.total G) (L P) (-((n : ℤ) - p)) (n : ℤ))
  rw [DecreasingFiltration.exists_image, DecreasingFiltration.exists_image] at himage
  rw [show -((n : ℤ) - p) + (n : ℤ) = p by omega] at himage
  rw [← himage, ← he, ← Category.assoc, hcomm, Category.assoc,
    imageSubobject_iso_comp]
  have ht := transported_imageFiltration_eq (F.grothendieckSpectralObject G P.X)
    (n : ℤ) ((n : ℤ) - p + 1)
    ((F.grothendieckSpectralObjectHBotTopIso G hFG n).app P.X)
  rw [show (n : ℤ) - p + 1 = (n : ℤ) + 1 - p by omega] at ht
  rw [show (n : ℤ) - p + 1 = (n : ℤ) + 1 - p by omega]
  exact ht.symm

end CategoryTheory
