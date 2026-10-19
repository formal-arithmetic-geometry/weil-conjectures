/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.CategoryTheory.GrothendieckComposablePair
public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredPageTwoModel
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Sheaf.CategoryTheory.CartanEilenbergPageRealization
import Sheaf.CategoryTheory.CartanEilenbergAcyclicAbutment

/-! # The Cartan--Eilenberg construction of the Grothendieck spectral sequence

Source: Stacks Project, Derived Categories, Tags 015N, 015J and 015K
(blueprint: thm-sp-grothendieck).

The integer indexing extends the first quadrant by zero. The comparison with the
existing truncation spectral object fixes the usual edge maps, while the filtered
page model specifies the Cartan--Eilenberg construction from page two onward.
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The functorial Grothendieck spectral sequence, with its Cartan--Eilenberg model.
Source: Stacks Project, Tags 015N, 015J and 015K (blueprint: thm-sp-grothendieck).

Proof:
1. Choose an injective resolution of each object (def-sp-injective-resolutions and
   lem-sp-grothendieck-enough-injectives). Apply the additive F; by
   lem-sp-derived-well-defined its cohomology is R^q F. Choose a Cartan--Eilenberg
   resolution by lem-sp-cartan-eilenberg-exists. CartanEilenbergPresentation records
   the common augmentation and all five resolution properties.
2. Apply G and totalize (def-sp-double-complex-total). The two filtrations give the
   two spectral sequences of thm-sp-double-complex-spectral-sequences, both with
   total cohomology as abutment and its finite image filtration.
3. The first sequence has E1 = R^q G(F(J^p)). Acyclicity makes all positive rows zero.
   Its degree-zero row is GF(J), by lem-sp-derived-well-defined. Apply
   lem-weil-pbc-first-quadrant-row-collapse to identify total cohomology with
   R^n(G composed with F). The augmentation into the resolution-degree-zero
   summands gives the total comparison map; its cohomology followed by h is the
   canonical injective-resolution computation P.J.isoRightDerivedObj inverse.
4. The second filtration is by resolution degree. Its E1 is horizontal cohomology
   of G(I). Injective horizontal cycles and boundaries allow
   lem-sp-cart-eilenberg-left-exact-cohomology to identify this with G applied to
   horizontal cohomology. The latter forms an injective resolution of H^q(F(J));
   hence the second page is R^p G(R^q F(X)). These are the identifications induced
   by this construction, using lem-sp-derived-well-defined.
5. The finite image filtration converges. The bottom edge is the quotient from E2
   to the stable bottom term followed by its inclusion in the abutment; the left
   edge is the abutment quotient followed by inclusion in the E2 left term. R^0 F
   and R^0 G identify their endpoints as stated. The equivalent truncation spectral
   object has exactly these edge maps and filtration. The comparison c and its
   first-page isomorphism k identify e with the canonical derived E2 computation.
   Transport the bottom and left edges through k and the canonical abutment iso;
   the equations for b and l fix these maps on the chosen E, and R^0 identifies
   their endpoints with the natural transformations bottom and left.
6. Lift maps to injective resolutions (lem-weil-pbc-injective-resolution-lift-exists)
   and then to Cartan--Eilenberg resolutions
   (lem-weil-pbc-cartesian-eilenberg-functorial). These preserve both filtrations.
   Lemma lem-sp-cartan-eilenberg-comparison-independence makes the page maps
   independent of lifts from page two, preserving identities and composition.
   The E2, abutment and edge identifications are natural in the original object.
-/
theorem exists_grothendieck_spectralSequence_cartanEilenberg
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics) :
    ∃ (M : FilteredPageTwoModel C)
      (E : A ⥤ E₂CohomologicalSpectralSequence C)
      (L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G))
      (s : ∀ P : CartanEilenbergPresentation F,
        E.obj P.X ≅ M.S.obj (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)))
      (e : ∀ (X : A) (p q : ℕ),
        ((E.obj X).page 2).X ((p : ℤ), (q : ℤ)) ≅
          (G.rightDerived p).obj ((F.rightDerived q).obj X))
      (h : ∀ (P : CartanEilenbergPresentation F) (n : ℕ),
        (P.total G).homology (n : ℤ) ≅ ((F ⋙ G).rightDerived n).obj P.X)
      (HF : ∀ (X : A) (n : ℕ), DecreasingFiltration (((F ⋙ G).rightDerived n).obj X))
      (c : ∀ X : A, E.obj X ≅ (F.grothendieckSpectralObject G X).E₂SpectralSequence)
      (k : ∀ (X : A) (p q : ℕ),
        ((E.obj X).page 2).X ((p : ℤ), (q : ℤ)) ≅
          ((F.grothendieckSpectralObject G X).H (p + q : ℕ)).obj
            (ComposableArrows.mk₁ (homOfLE
              (by simp : ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt))))),
      (∀ X : A, ∃ P : CartanEilenbergPresentation F, P.X = X) ∧
      (∀ (X : A) (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
        p < 0 ∨ q < 0 → IsZero (((E.obj X).page r hr).X (p, q))) ∧
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
      (∀ (X : A) (n : ℕ), (HF X n).step 0 = ⊤ ∧ (HF X n).step (n + 1) = ⊥) ∧
      (∀ (X : A) (p q : ℕ) (r : ℤ) (hr : 2 ≤ r),
        max (p : ℤ) ((q : ℤ) + 1) < r →
          Nonempty (((E.obj X).page r hr).X ((p : ℤ), (q : ℤ)) ≅
            (HF X (p + q)).gradedPiece (p : ℤ))) ∧
      (∀ (X Y : A) (f : X ⟶ Y) (n : ℕ) (p : ℤ),
        ∃ a : ((HF X n).step p : C) ⟶ ((HF Y n).step p : C),
          a ≫ ((HF Y n).step p).arrow =
            ((HF X n).step p).arrow ≫ ((F ⋙ G).rightDerived n).map f) ∧
      (∀ (X : A) (p q : ℕ),
        (k X p q).hom = ((c X).hom.hom 2).f ((p : ℤ), (q : ℤ)) ≫
          ((F.grothendieckSpectralObject G X).spectralSequenceFirstPageXIso
            Abelian.SpectralObject.coreE₂Cohomological
            ((p : ℤ), (q : ℤ)) _ _ rfl rfl (p + q : ℕ) (by push_cast; rfl)).hom ∧
        (e X p q).hom = (k X p q).hom ≫
          (F.grothendieckSpectralObjectHIso G p q (p + q : ℕ) q (q + 1)
            (by push_cast; rfl) rfl rfl).hom.app X) ∧
      (∀ (P : CartanEilenbergPresentation F) (n p : ℕ),
        (HF P.X n).step (p : ℤ) =
          (Subobject.«exists» ((F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app P.X)).obj
            ((F.grothendieckSpectralObject G P.X).imageFiltration (n : ℤ)
              ((n : ℤ) + 1 - (p : ℤ)))) ∧
      (∃ (bottom : ∀ n : ℕ, F ⋙ G.rightDerived n ⟶ (F ⋙ G).rightDerived n)
        (left : ∀ n : ℕ, (F ⋙ G).rightDerived n ⟶ F.rightDerived n ⋙ G)
        (b : ∀ (X : A) (n : ℕ),
          ((E.obj X).page 2).X ((n : ℤ), 0) ⟶ ((F ⋙ G).rightDerived n).obj X)
        (l : ∀ (X : A) (n : ℕ),
          ((F ⋙ G).rightDerived n).obj X ⟶ ((E.obj X).page 2).X (0, (n : ℤ))),
        (∀ (X : A) (n : ℕ),
          b X n = (k X n 0).hom ≫ (F.grothendieckBottomEdge G n).app X ≫
            (F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app X ∧
          l X n = (F.grothendieckSpectralObjectHBotTopIso G hFG n).inv.app X ≫
            (F.grothendieckLeftEdge G n).app X ≫ eqToHom (by simp) ≫ (k X 0 n).inv ∧
          (bottom n).app X =
            (G.rightDerived n).map (F.rightDerivedZeroIsoSelf.inv.app X) ≫
              (e X n 0).inv ≫ b X n ∧
          (left n).app X = l X n ≫ (e X 0 n).hom ≫
            G.rightDerivedZeroIsoSelf.hom.app ((F.rightDerived n).obj X)) ∧
        (∀ n : ℕ, bottom n = F.grothendieckBottomEdgeMap G hFG n) ∧
        (∀ n : ℕ, left n = F.grothendieckLeftEdgeMap G hFG n)) := by
  classical
  change F.IsAcyclicComposablePair G at hFG
  obtain ⟨M, E, L, s, e, c, k, degree, enat, smap, ek⟩ :=
    exists_cartanEilenberg_page_realization F G
  obtain ⟨h, HF, hnat, aug, image, stable, fnat, trunc⟩ :=
    exists_cartanEilenberg_acyclic_abutment F G hFG E L c degree
  have presents : ∀ X : A, ∃ P : CartanEilenbergPresentation F, P.X = X := by
    intro X
    let J := injectiveResolution X
    let K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (J.cocomplex.extend ComplexShape.embeddingUpNat)
    have neg (p : ℤ) (hp : p < 0) : IsZero (K.X p) := by
      apply F.map_isZero
      exact J.cocomplex.isZero_extend_X ComplexShape.embeddingUpNat p (by
        intro n hn
        change (n : ℤ) = p at hn
        omega)
    obtain ⟨I, a, iz, cq, ti, hi, hq⟩ := exists_cartanEilenberg_resolution B K neg
    exact ⟨⟨X, J, I, a, iz, cq, ti, hi, hq⟩, rfl⟩
  refine ⟨M, E, L, s, e, h, HF, c, k, presents, ?_, degree, enat, smap,
    hnat, aug, image, ?_, stable, fnat, ek, trunc, ?_⟩
  · intro X r hr p q hpq
    let Y := F.grothendieckSpectralObject G X
    let i := (HomologicalComplex.eval C _ (p, q)).mapIso
      ((SpectralSequence.pageFunctor C _ 2 r hr).mapIso (c X))
    apply i.isZero_iff.mpr
    rcases hpq with hp | hq
    · exact Y.isZero_spectralSequence_page_X_of_isZero_H'
        Abelian.SpectralObject.coreE₂Cohomological r hr (p, q)
        (Y.isZero₂_of_isFirstQuadrant _ _ _ _ (by simp; omega))
    · exact Y.isZero_spectralSequence_page_X_of_isZero_H'
        Abelian.SpectralObject.coreE₂Cohomological r hr (p, q)
        (Y.isZero₁_of_isFirstQuadrant _ _ _ (by simp; omega) _)
  · intro X n
    obtain ⟨P, hP⟩ := presents X
    subst X
    constructor
    · have hz := trunc P n 0
      simp only [Nat.cast_zero, sub_zero] at hz
      rw [hz]
      rw [(F.grothendieckSpectralObject G P.X).imageFiltration_eq_top _ _ (by omega)]
      rw [Subobject.exists_iso_map, Subobject.map_top, Subobject.mk_eq_top_of_isIso]
    · have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by simp
      rw [hn, trunc P n (n + 1)]
      rw [(F.grothendieckSpectralObject G P.X).imageFiltration_eq_bot _ _ (by omega)]
      rw [Subobject.exists_iso_map, Subobject.map_bot]
  · refine ⟨F.grothendieckBottomEdgeMap G hFG, F.grothendieckLeftEdgeMap G hFG,
      (fun X n ↦ (k X n 0).hom ≫ (F.grothendieckBottomEdge G n).app X ≫
        (F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app X),
      (fun X n ↦ (F.grothendieckSpectralObjectHBotTopIso G hFG n).inv.app X ≫
        (F.grothendieckLeftEdge G n).app X ≫ eqToHom (by simp) ≫ (k X 0 n).inv),
      ?_, (fun _ ↦ rfl), (fun _ ↦ rfl)⟩
    intro X n
    refine ⟨rfl, rfl, ?_, ?_⟩
    · have ei : e X n 0 = k X n 0 ≪≫
          (F.grothendieckSpectralObjectHIso G n 0 (n + 0 : ℕ) 0 (0 + 1)
            (by push_cast; rfl) rfl rfl).app X := Iso.ext (ek X n 0).2
      rw [ei]
      simp [Functor.grothendieckBottomEdgeMap, Functor.grothendieckBottomEdgeSourceIso]
    · rw [(ek X 0 n).2]
      have hi (m : ℤ) (hm : m = (n : ℤ)) :
          eqToHom (show
            ((F.grothendieckSpectralObject G X).H (n : ℤ)).obj
                (ComposableArrows.mk₁ (homOfLE
                  (by simp : ((n : ℤ) : EInt) ≤ ((n + 1 : ℤ) : EInt)))) =
              ((F.grothendieckSpectralObject G X).H m).obj
                (ComposableArrows.mk₁ (homOfLE
                  (by simp : ((n : ℤ) : EInt) ≤ ((n + 1 : ℤ) : EInt)))) by rw [hm]) ≫
            (F.grothendieckSpectralObjectHIso G 0 n m n (n + 1)
              (by omega) rfl rfl).hom.app X =
            (F.grothendieckSpectralObjectHIso G 0 n n n (n + 1)
              (by omega) rfl rfl).hom.app X := by
        subst m
        simp only [eqToHom_refl, Category.id_comp]
      simp only [Functor.grothendieckLeftEdgeMap, NatTrans.comp_app,
        Functor.grothendieckLeftEdgeTargetIso, Iso.trans_hom,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
        Iso.inv_hom_id_assoc]
      simpa only [Category.assoc] using (congrArg (fun z ↦
        (F.grothendieckSpectralObjectHBotTopIso G hFG n).inv.app X ≫
          (F.grothendieckLeftEdge G n).app X ≫ z ≫
            G.rightDerivedZeroIsoSelf.hom.app ((F.rightDerived n).obj X))
        (hi (0 + n : ℕ) (by simp))).symm

end CategoryTheory
