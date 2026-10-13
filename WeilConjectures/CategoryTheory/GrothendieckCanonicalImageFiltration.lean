/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckComposablePair
public import WeilConjectures.CategoryTheory.Filtration
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-! # Canonical image filtration of the Grothendieck spectral object

Source: Stacks Project, Derived Categories, Tag 015N; Homology, Tag 0132.
(blueprint: lem-sp-grothendieck-canonical-image-filtration).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

open ComposableArrows

private noncomputable def cokernel_ofLE_congr
    {C : Type uC} [Category.{vC} C] [Abelian C] {Z : C}
    (S T S' T' : Subobject Z) (h : S ≤ T) (h' : S' ≤ T')
    (hs : S = S') (ht : T = T') :
    cokernel (Subobject.ofLE S T h) ≅ cokernel (Subobject.ofLE S' T' h') := by
  subst S' T'
  exact Iso.refl _

private lemma transported_subobject_eq
    {C : Type uC} [Category.{vC} C] [Abelian C] {Z Z' : C}
    (e : Z ≅ Z') (S : Subobject Z) :
    (Subobject.«exists» e.hom).obj S = Subobject.mk (S.arrow ≫ e.hom) := by
  rw [Subobject.exists_iso_map]
  conv_lhs => rw [← Subobject.mk_arrow S, Subobject.map_mk]

private noncomputable def cokernel_ofLE_transport
    {C : Type uC} [Category.{vC} C] [Abelian C] {Z Z' : C}
    (e : Z ≅ Z') (S T : Subobject Z) (h : S ≤ T) :
    cokernel (Subobject.ofLE
      (Subobject.mk (S.arrow ≫ e.hom)) (Subobject.mk (T.arrow ≫ e.hom))
      (Subobject.mk_le_mk_of_comm (Subobject.ofLE S T h) (by simp))) ≅
      cokernel (Subobject.ofLE S T h) := by
  refine cokernel.mapIso _ _ (Subobject.underlyingIso _) (Subobject.underlyingIso _) ?_
  simp [← cancel_mono (T.arrow ≫ e.hom)]

private lemma transported_imageFiltration_eq
    {C : Type uC} [Category.{vC} C] [Abelian C]
    (Y : Abelian.SpectralObject C EInt) (n a : ℤ) {Z : C}
    (e : (Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≅ Z) :
    (Subobject.«exists» e.hom).obj (Y.imageFiltration n a) =
      imageSubobject ((Y.H n).map
        (twoδ₂Toδ₁' (⊥ : EInt) (a : EInt) ⊤ bot_le le_top) ≫ e.hom) := by
  rw [Abelian.SpectralObject.imageFiltration, Subobject.exists_iso_map, Subobject.map_mk,
    ← imageSubobject_mono, ← imageSubobject_comp_of_epi (Y.pOpcycles
      (homOfLE (bot_le : (⊥ : EInt) ≤ a))
      (homOfLE (le_top : (a : EInt) ≤ ⊤)) n)]
  simp only [Abelian.SpectralObject.p_fromOpcycles_assoc]
  rfl

/-- The canonical truncation images form a natural decreasing filtration of the
derived composite; its graded pieces compute every stable spectral-sequence page.
Source: Stacks Project, Derived Categories, Tag 015N, and Homology, Tag 0132.
(blueprint: lem-sp-grothendieck-canonical-image-filtration).

Proof: Define the p-th step by transporting imageFiltration(n,n+1-p) through the
canonical acyclic-composite isomorphism. This is an actual construction, with no
choice of a presentation. Monotonicity of imageFiltration and order preservation of
Subobject.exists prove antitonicity. Naturality of the spectral-object morphisms
and of the acyclic-composite isomorphism induces morphisms on these images,
including negative steps, which are the whole object. For r>max(p,q+1), the page
formula identifies E_r^(p,q) with the spectral-object term for the four indices
q-r+2, q, q+1, q+r-1. First-quadrant vanishing replaces the outer indices by
bottom and top. The short exact sequence of consecutive opcycle images identifies
this term with the cokernel of the inclusion of imageFiltration(n,q) into
imageFiltration(n,q+1), where n=p+q. Transport along the abutment isomorphism
identifies this cokernel with the p-th graded piece. Finally compose with the
page-r component of c_X. Only objectwise isomorphisms c_X are used. -/
theorem exists_grothendieck_canonical_image_filtration
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (E : A ⥤ E₂CohomologicalSpectralSequence C)
    (c : ∀ X : A, E.obj X ≅ (F.grothendieckSpectralObject G X).E₂SpectralSequence) :
    ∃ (HF : ∀ (X : A) (n : ℕ), DecreasingFiltration (((F ⋙ G).rightDerived n).obj X)),
      (∀ (X : A) (n : ℕ) (p : ℤ),
        (HF X n).step p =
          (Subobject.«exists» ((F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app X)).obj
            ((F.grothendieckSpectralObject G X).imageFiltration (n : ℤ)
              ((n : ℤ) + 1 - p))) ∧
      (∀ (X : A) (p q : ℕ) (r : ℤ) (hr : 2 ≤ r),
        max (p : ℤ) (q + 1 : ℤ) < r →
          Nonempty (((E.obj X).page r hr).X ((p : ℤ), (q : ℤ)) ≅
            (HF X (p + q)).gradedPiece (p : ℤ))) ∧
      (∀ (X Y : A) (f : X ⟶ Y) (n : ℕ) (p : ℤ),
        ∃ a : ((HF X n).step p : C) ⟶ ((HF Y n).step p : C),
          a ≫ ((HF Y n).step p).arrow =
            ((HF X n).step p).arrow ≫ ((F ⋙ G).rightDerived n).map f) := by
  classical
  change F.IsAcyclicComposablePair G at hFG
  let HF : ∀ (X : A) (n : ℕ), DecreasingFiltration (((F ⋙ G).rightDerived n).obj X) :=
    fun X n ↦
      { F := fun p ↦
          (Subobject.«exists»
            ((F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app X)).obj
            ((F.grothendieckSpectralObject G X).imageFiltration (n : ℤ)
              ((n : ℤ) + 1 - p))
        F_succ_le p := by
          exact leOfHom ((Subobject.«exists»
            ((F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app X)).map
            (homOfLE ((F.grothendieckSpectralObject G X).imageFiltration_mono
              (n : ℤ) (by omega)))) }
  refine ⟨HF, fun X n p ↦ rfl, ?_, ?_⟩
  · intro X p q r hr hbound
    let Y := F.grothendieckSpectralObject G X
    let n : ℤ := (p + q : ℕ)
    let raw : DecreasingFiltration
        ((Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) :=
      { F := fun i ↦ Y.imageFiltration n (n + 1 - i)
        F_succ_le i := Y.imageFiltration_mono n (by omega) }
    have hquot := Y.nonempty_cokernel_ofLE_imageFiltration_iso n (q : ℤ)
      (q + 1 : ℤ) rfl (Y.imageFiltration_mono n (by omega))
    let page := Y.spectralSequencePageXIso Abelian.SpectralObject.coreE₂Cohomological
      r hr ((p : ℤ), (q : ℤ)) (q - r + 2 : ℤ) (q : ℤ) (q + 1 : ℤ)
      (q + r - 1 : ℤ) rfl rfl rfl rfl (n - 1) n (n + 1) (by dsimp [n]; rfl)
    let left := Y.isoMapFourδ₁Toδ₀' ⊥ ((q - r + 2 : ℤ) : EInt)
      (q : ℤ) (q + 1 : ℤ) (q + r - 1 : ℤ) bot_le
      (WithBotTop.coe_le_coe.2 (by omega))
      (WithBotTop.coe_le_coe.2 (by omega))
      (WithBotTop.coe_le_coe.2 (by omega)) (n - 1) n (n + 1)
      (Y.isZero₁_of_isFirstQuadrant _ _ _
        (WithBotTop.coe_le_coe.2 (by omega)) _)
    let right := Y.isoMapFourδ₄Toδ₃' ⊥ (q : ℤ) (q + 1 : ℤ)
      (q + r - 1 : ℤ) ⊤ bot_le
      (WithBotTop.coe_le_coe.2 (by omega))
      (WithBotTop.coe_le_coe.2 (by omega)) le_top (n - 1) n (n + 1)
      (Y.isZero₂_of_isFirstQuadrant _ _ _ _
        (WithBotTop.coe_lt_coe.2 (by dsimp [n]; omega)))
    have rawiso : Nonempty (raw.gradedPiece (p : ℤ) ≅
        ((Y.E₂SpectralSequence).page r hr).X ((p : ℤ), (q : ℤ))) := by
      refine ⟨?_ ≪≫ hquot.some ≪≫ right.symm ≪≫ left ≪≫ page.symm⟩
      have hs : raw.step (p : ℤ) = Y.imageFiltration n ((q : ℤ) + 1) := by
        dsimp [raw, n, DecreasingFiltration.step]
        congr 1
        omega
      have ht : raw.step ((p : ℤ) + 1) = Y.imageFiltration n (q : ℤ) := by
        dsimp [raw, n, DecreasingFiltration.step]
        congr 1
        omega
      exact cokernel_ofLE_congr _ _ _ _ _ _ ht hs
    let e := (F.grothendieckSpectralObjectHBotTopIso G hFG (p + q)).app X
    have hs (i : ℤ) : (HF X (p + q)).step i =
        Subobject.mk ((raw.step i).arrow ≫ e.hom) := by
      dsimp only [HF, raw, DecreasingFiltration.step]
      have he := transported_subobject_eq e
        (Y.imageFiltration n (n + 1 - i))
      dsimp only [e, Iso.app_hom] at he
      simpa only [Y, n, e, Iso.app_hom, Nat.cast_add] using he
    have transiso : raw.gradedPiece (p : ℤ) ≅ (HF X (p + q)).gradedPiece (p : ℤ) := by
      refine (cokernel_ofLE_transport e (raw.step ((p : ℤ) + 1)) (raw.step (p : ℤ))
        (raw.antitone_step (by omega))).symm ≪≫ ?_
      exact cokernel_ofLE_congr _ _ _ _ _ _ (hs ((p : ℤ) + 1)).symm (hs (p : ℤ)).symm
    let ep := (SpectralSequence.pageFunctor C _ 2 r hr ⋙
      HomologicalComplex.eval C _ ((p : ℤ), (q : ℤ))).mapIso (c X)
    exact ⟨ep ≪≫ rawiso.some.symm ≪≫ transiso⟩
  · intro X Y f n p
    dsimp only [HF, DecreasingFiltration.step]
    have hx := transported_imageFiltration_eq (F.grothendieckSpectralObject G X) (n : ℤ)
      ((n : ℤ) + 1 - p) ((F.grothendieckSpectralObjectHBotTopIso G hFG n).app X)
    have hy := transported_imageFiltration_eq (F.grothendieckSpectralObject G Y) (n : ℤ)
      ((n : ℤ) + 1 - p) ((F.grothendieckSpectralObjectHBotTopIso G hFG n).app Y)
    dsimp only [Iso.app_hom] at hx hy
    rw [hx, hy]
    let φ := (F.grothendieckSpectralObjectFunctor G).map f
    let e := F.grothendieckSpectralObjectHBotTopIso G hFG n
    let i := twoδ₂Toδ₁' (⊥ : EInt) (((n : ℤ) + 1 - p) : EInt) ⊤ bot_le le_top
    have w : (φ.hom (n : ℤ)).app _ ≫
        ((F.grothendieckSpectralObject G Y).H (n : ℤ)).map i ≫ e.hom.app Y =
        (((F.grothendieckSpectralObject G X).H (n : ℤ)).map i ≫ e.hom.app X) ≫
          ((F ⋙ G).rightDerived n).map f := by
      rw [← NatTrans.naturality_assoc]
      rw [Category.assoc]
      congr 1
      exact e.hom.naturality f
    exact ⟨imageSubobjectMap (Arrow.homMk' _ _ w), imageSubobjectMap_arrow _⟩

end CategoryTheory
