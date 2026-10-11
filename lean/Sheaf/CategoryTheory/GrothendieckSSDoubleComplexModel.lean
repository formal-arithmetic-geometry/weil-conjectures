/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.GrothendieckSpectralSequence
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # The filtered double-complex model and its left edge

Source: Stacks Project, Derived Categories, Lemma 015N (proof), Lemma 015J,
and Homology, the first-quadrant image filtration
(blueprint: lem-pc-grothendieck-ss-double-complex-model).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The Grothendieck sequence is the filtered Cartan--Eilenberg total-complex sequence,
with its image filtration and quotient/inclusion left edge. `P.X` is the given object,
`P.J` its given injective resolution, and `P.I` the given Cartan--Eilenberg resolution.
The first filtration of the transpose is the second filtration in `P.I`'s convention.
Source: Stacks Project, Derived Categories, Lemma 015N (proof), Lemma 015J
(blueprint: lem-pc-grothendieck-ss-double-complex-model).

Proof:
1. Use the construction of thm-sp-grothendieck and thm-sp-if-e1. Transpose the
   bicomplex; multiplication of the (p,q) summand by (-1)^(pq) identifies its total
   complex and first filtration with the original total and second filtration
   (def-sp-double-complex-total, thm-sp-double-complex-spectral-sequences).
2. The first-filtration E1 page is vertical cohomology. The injective cycles,
   boundaries and cohomology in lem-sp-cartan-eilenberg-properties split the column
   differentials, so G commutes with this cohomology. The cohomology rows resolve
   R^q F(P.X); applying G gives R^p G(R^q F(P.X)) (def-sp-left-exact-additive).
3. Apply thm-sp-if-e1 to G and F(P.J). Positive derived rows vanish by
   def-sp-composite-acyclicity; the surviving row is GF(P.J). The other sequence
   collapses, identifying total cohomology through the augmentation with the
   injective-resolution computation of R^n(G composed with F).
4. By thm-sp-double-complex-spectral-sequences the image filtration starts at the
   whole abutment and ends at zero in degree n+1. Stable terms are its graded pieces.
   The left edge is the cokernel quotient by step 1, followed by the stable-term
   inclusion into E2: `j r` is the canonical inclusion of E_{n+2}^{0,n} into E_r^{0,n},
   built down from `j (n+2) = 𝟙` through the cycle inclusion E_{r+1} = ker d_r ⊆ E_r
   (at (0,n) the incoming differential is zero, so `pOpcycles` is an isomorphism).
   Through the canonical E2 and abutment identifications this is
   lem-sp-grothendieck-edge-maps's grothendieckLeftEdgeMap.
-/
theorem grothendieckSSDoubleComplexModel
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (P : CartanEilenbergPresentation F) :
    ∃ (M : FilteredPageTwoModel C) (E : E₂CohomologicalSpectralSequence C)
      (L : DecreasingFiltration (P.total G))
      (s : E ≅ M.S.obj (⟨P.total G, L⟩ : FilteredObject (CochainComplex C ℤ)))
      (c : E ≅ (F.grothendieckSpectralObject G P.X).E₂SpectralSequence)
      (e : ∀ p q : ℕ, (E.page 2).X ((p : ℤ), (q : ℤ)) ≅
        (G.rightDerived p).obj ((F.rightDerived q).obj P.X))
      (h : ∀ n : ℕ, (P.total G).homology (n : ℤ) ≅
        ((F ⋙ G).rightDerived n).obj P.X)
      (HF : ∀ n : ℕ, DecreasingFiltration (((F ⋙ G).rightDerived n).obj P.X)),
      (∀ p n : ℤ, L.complexStep p n =
        ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p)) ∧
      (∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), p < 0 ∨ q < 0 →
        IsZero ((E.page r hr).X (p, q))) ∧
      (∀ p q : ℕ, (e p q).hom = ((c.hom.hom 2).f ((p : ℤ), (q : ℤ))) ≫
        ((F.grothendieckSpectralObject G P.X).spectralSequenceFirstPageXIso
          Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), (q : ℤ)) _ _ rfl rfl
          (p + q : ℕ) (by push_cast; rfl)).hom ≫
        (F.grothendieckSpectralObjectHIso G p q (p + q : ℕ) q (q + 1)
          (by push_cast; rfl) rfl rfl).hom.app P.X) ∧
      (∃ a : (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex).extend
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
        (∀ n : ℕ, HomologicalComplex.homologyMap a (n : ℤ) ≫ (h n).hom =
          (HomologicalComplex.extendHomologyIso
            (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
            ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
            (P.J.isoRightDerivedObj (F ⋙ G) n).inv)) ∧
      (∀ (p : ℤ) (n : ℕ), (HF n).step p = imageSubobject
        (HomologicalComplex.homologyMap (L.step p).arrow (n : ℤ) ≫ (h n).hom)) ∧
      (∀ n p : ℕ, (HF n).step (p : ℤ) =
        (Subobject.«exists» ((F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app P.X)).obj
          ((F.grothendieckSpectralObject G P.X).imageFiltration (n : ℤ)
            ((n : ℤ) + 1 - (p : ℤ)))) ∧
      (∀ n : ℕ, (HF n).step 0 = ⊤ ∧ (HF n).step (n + 1) = ⊥) ∧
      (∀ (p q : ℕ) (r : ℤ) (hr : 2 ≤ r), max (p : ℤ) ((q : ℤ) + 1) < r →
        Nonempty ((E.page r hr).X ((p : ℤ), (q : ℤ)) ≅ (HF (p + q)).gradedPiece (p : ℤ))) ∧
      (∀ n : ℕ, ∃
        (π : ((F ⋙ G).rightDerived n).obj P.X ⟶ (HF n).gradedPiece 0)
        (t : (HF n).gradedPiece 0 ≅ (E.page (n + 2 : ℤ) (by omega)).X (0, (n : ℤ)))
        (j : ∀ (r : ℤ) (hr : 2 ≤ r), r ≤ (n : ℤ) + 2 →
          ((E.page ((n : ℤ) + 2) (by omega)).X (0, (n : ℤ)) ⟶ (E.page r hr).X (0, (n : ℤ)))),
        Epi π ∧
        j ((n : ℤ) + 2) (by omega) le_rfl = 𝟙 _ ∧
        (∀ (r : ℤ) (hr : 2 ≤ r) (hrn : r + 1 ≤ (n : ℤ) + 2),
          j r hr (by omega) ≫ (E.page r hr).pOpcycles (0, (n : ℤ)) =
            j (r + 1) (by omega) hrn ≫ (E.iso r (r + 1) (0, (n : ℤ))).inv ≫
              (E.page r hr).homologyι (0, (n : ℤ))) ∧
        ((HF n).step 0).arrow ≫ π =
          cokernel.π (Subobject.ofLE ((HF n).step 1) ((HF n).step 0)
            ((HF n).antitone_step (by decide))) ∧
        π ≫ t.hom ≫ j 2 le_rfl (by omega) ≫ (e 0 n).hom ≫
          G.rightDerivedZeroIsoSelf.hom.app ((F.rightDerived n).obj P.X) =
            (F.grothendieckLeftEdgeMap G hFG n).app P.X) := by
  sorry

end CategoryTheory
