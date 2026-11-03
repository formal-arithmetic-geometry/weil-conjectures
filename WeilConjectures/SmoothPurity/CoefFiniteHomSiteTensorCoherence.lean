/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CoefFiniteHom
public import WeilConjectures.SmoothPurity.CoefFiniteHomRhoMonoidal
public import WeilConjectures.SmoothPurity.CoefFiniteHomRhoScalarCoherence

/-! # Finite coefficient tensor and internal-Hom site coherence

Source: latest blueprint, `thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence).
All categories are ordinary derived categories of constant-ring module sheaves.
The scalar, tensor, evaluation-transpose and scalar/site maps are constructions in
`CoefFiniteHom`; none is supplied as a field. The equations below express monoidality,
the site square, and its pasting for a genuine chain A → B → C.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures

/-- The original small pro-etale site has the ordinary coefficient universe size.
Source: finite coefficient size convention in thm-coef-finite-hom, statement
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
local instance siteComparisonProEtSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private theorem monoidal_delta
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D]
    {E : Type u₂} [Category.{v₂} E] [MonoidalCategory E]
    {F G : D ⥤ E} [F.Monoidal] [G.Monoidal]
    (τ : F ⟶ G) (hτ : NatTrans.IsMonoidal τ) (K M : D) :
    τ.app (K ⊗ M) ≫ Functor.OplaxMonoidal.δ G K M =
      Functor.OplaxMonoidal.δ F K M ≫ (τ.app K ⊗ₘ τ.app M) := by
  have := hτ
  apply (cancel_epi (Functor.LaxMonoidal.μ F K M)).1
  simp only [← Category.assoc, NatTrans.IsMonoidal.tensor]
  simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id,
    Category.id_comp]

private theorem monoidal_eta
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D]
    {E : Type u₂} [Category.{v₂} E] [MonoidalCategory E]
    {F G : D ⥤ E} [F.Monoidal] [G.Monoidal]
    (τ : F ⟶ G) (hτ : NatTrans.IsMonoidal τ) :
    τ.app (𝟙_ D) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F := by
  have := hτ
  apply (cancel_epi (Functor.LaxMonoidal.ε F)).1
  simp only [← Category.assoc, NatTrans.IsMonoidal.unit, Functor.Monoidal.ε_η]

private theorem closedSquare_of_monoidal
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [MonoidalClosed D]
    {E : Type u₂} [Category.{v₂} E] [MonoidalCategory E] [MonoidalClosed E]
    {P : Type u₃} [Category.{v₃} P] [MonoidalCategory P] [MonoidalClosed P]
    {Q : Type u₄} [Category.{v₄} Q] [MonoidalCategory Q] [MonoidalClosed Q]
    (F : D ⥤ E) (G : P ⥤ Q) (U : D ⥤ P) (V : E ⥤ Q)
    [F.Monoidal] [G.Monoidal] [U.Monoidal] [V.Monoidal]
    (h : F ⋙ V ≅ U ⋙ G) (hh : NatTrans.IsMonoidal h.hom) (K M : D) :
    V.map ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app M) ≫
        (Functor.LaxMonoidal.ihomComparison V (F.obj K)).natTrans.app (F.obj M) ≫
        (MonoidalClosed.pre (h.inv.app K)).app (V.obj (F.obj M)) ≫
        (ihom (G.obj (U.obj K))).map (h.hom.app M) =
      h.hom.app ((ihom K).obj M) ≫
        G.map ((Functor.LaxMonoidal.ihomComparison U K).natTrans.app M) ≫
        (Functor.LaxMonoidal.ihomComparison G (U.obj K)).natTrans.app (U.obj M) := by
  have := hh
  have q := Functor.LaxMonoidal.ihomComparison_app_comp_map_app h.inv K M
  have q' := congrArg (fun f ↦ h.hom.app ((ihom K).obj M) ≫ f ≫
    (ihom ((U ⋙ G).obj K)).map (h.hom.app M)) q
  simp only [← Functor.map_comp, Iso.inv_hom_id_app,
    Category.assoc, Iso.hom_inv_id_app_assoc] at q'
  have hi := (ihom ((U ⋙ G).obj K)).map_id ((U ⋙ G).obj M)
  rw [hi] at q'
  simpa only [Functor.LaxMonoidal.ihomComparison_comp_app, Functor.comp_obj,
    Category.comp_id, Category.assoc] using q'.symm

private theorem closedPastedSquare_of_monoidal
    {D₀ D₁ D₂ P₀ P₁ P₂ : Type*}
    [Category D₀] [MonoidalCategory D₀] [MonoidalClosed D₀]
    [Category D₁] [MonoidalCategory D₁] [MonoidalClosed D₁]
    [Category D₂] [MonoidalCategory D₂] [MonoidalClosed D₂]
    [Category P₀] [MonoidalCategory P₀] [MonoidalClosed P₀]
    [Category P₁] [MonoidalCategory P₁] [MonoidalClosed P₁]
    [Category P₂] [MonoidalCategory P₂] [MonoidalClosed P₂]
    (F : D₀ ⥤ D₁) (F' : D₁ ⥤ D₂) (G : P₀ ⥤ P₁) (G' : P₁ ⥤ P₂)
    (U : D₀ ⥤ P₀) (V : D₁ ⥤ P₁) (W : D₂ ⥤ P₂)
    [F.Monoidal] [F'.Monoidal] [G.Monoidal] [G'.Monoidal]
    [U.Monoidal] [V.Monoidal] [W.Monoidal]
    (h : F ⋙ V ≅ U ⋙ G) (h' : F' ⋙ W ≅ V ⋙ G')
    (hh : NatTrans.IsMonoidal h.hom) (hh' : NatTrans.IsMonoidal h'.hom) (K M : D₀) :
    W.map (F'.map ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app M) ≫
        (Functor.LaxMonoidal.ihomComparison F' (F.obj K)).natTrans.app (F.obj M)) ≫
        (Functor.LaxMonoidal.ihomComparison W (F'.obj (F.obj K))).natTrans.app
          (F'.obj (F.obj M)) ≫
        (MonoidalClosed.pre (G'.map (h.inv.app K) ≫ h'.inv.app (F.obj K))).app
          (W.obj (F'.obj (F.obj M))) ≫
        (ihom (G'.obj (G.obj (U.obj K)))).map
          (h'.hom.app (F.obj M) ≫ G'.map (h.hom.app M)) =
      (h'.hom.app (F.obj ((ihom K).obj M)) ≫ G'.map (h.hom.app ((ihom K).obj M))) ≫
        G'.map (G.map ((Functor.LaxMonoidal.ihomComparison U K).natTrans.app M)) ≫
        G'.map ((Functor.LaxMonoidal.ihomComparison G (U.obj K)).natTrans.app (U.obj M)) ≫
        (Functor.LaxMonoidal.ihomComparison G' (G.obj (U.obj K))).natTrans.app
          (G.obj (U.obj M)) := by
  have := hh
  have := hh'
  let e : (F ⋙ F') ⋙ W ≅ U ⋙ (G ⋙ G') :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ h' ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight h _ ≪≫
      Functor.associator _ _ _
  have he : NatTrans.IsMonoidal e.hom := by
    simp only [e, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Iso.symm_hom]
    infer_instance
  simpa only [e, Functor.LaxMonoidal.ihomComparison_comp_app,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.comp_obj, Functor.comp_map]
    using closedSquare_of_monoidal (F ⋙ F') (G ⋙ G') U W e he K M

/-- The unit component of the canonical derived comparison inverse image.
Source: thm-coef-finite-hom proof, final paragraph; Stacks 03EL, 08J7
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
def finiteHomSiteUnit
    (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u}) :
    (comparisonNu (R := R) X).obj (𝟙_ (EtaleDerived R X)) ⟶
      𝟙_ (ProEtaleDerived R X) := by
  letI : (comparisonNu (R := R) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat R) X
  exact (Functor.Monoidal.εIso (comparisonNu (R := R) X)).inv

/-- The specified beta/rho/v site square, including the contravariant rho inverse.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
def finiteHomSiteSquare
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (X : Scheme.{u}) (φ : A →+* B) (K M : EtaleDerived A X) : Prop :=
  (comparisonNu X).map (etaleHom X φ K M) ≫
      comparisonBeta X ((etaleScalar X φ).obj K) ((etaleScalar X φ).obj M) ≫
      (MonoidalClosed.pre (canonicalRho X φ K)).app
        ((comparisonNu X).obj ((etaleScalar X φ).obj M)) ≫
      (ihom ((proEtaleScalar X φ).obj ((comparisonNu X).obj K))).map
        (canonicalRhoInv X φ M) =
    canonicalRhoInv X φ ((ihom K).obj M) ≫
      (proEtaleScalar X φ).map (comparisonBeta X K M) ≫
      proHom X φ ((comparisonNu X).obj K) ((comparisonNu X).obj M)

private theorem nativeEtaleHom_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u}) (φ : A →+* B)
    (K M : EtaleDerived A X) :
    let : (etaleScalar X φ).Monoidal := (etaleCore X φ).toMonoidal
    etaleHom X φ K M =
      (Functor.LaxMonoidal.ihomComparison (etaleScalar X φ) K).natTrans.app M := by
  unfold etaleHom
  rfl

private theorem nativeProHom_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u}) (φ : A →+* B)
    (K M : ProEtaleDerived A X) :
    let : (proEtaleScalar X φ).Monoidal := (proCore X φ).toMonoidal
    proHom X φ K M =
      (Functor.LaxMonoidal.ihomComparison (proEtaleScalar X φ) K).natTrans.app M := by
  unfold proHom
  rfl

private theorem nativeComparisonBeta_eq
    {A : Type (u + 1)} [CommRing A] [Finite A] (X : Scheme.{u})
    (K M : EtaleDerived A X) :
    let : (comparisonNu (R := A) X).Monoidal :=
      AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat A) X
    comparisonBeta X K M =
      (Functor.LaxMonoidal.ihomComparison (comparisonNu X) K).natTrans.app M := by
  unfold comparisonBeta AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom comparisonNu
  rfl

private theorem nativeSiteSquare
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (X : Scheme.{u}) (φ : A →+* B)
    (hm : FiniteHomRhoMonoidal X φ)
    (K M : EtaleDerived A X) : finiteHomSiteSquare X φ K M := by
  let : (etaleScalar X φ).Monoidal := (etaleCore X φ).toMonoidal
  let : (proEtaleScalar X φ).Monoidal := (proCore X φ).toMonoidal
  let : (comparisonNu (R := A) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat A) X
  let : (comparisonNu (R := B) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat B) X
  simpa only [finiteHomSiteSquare, nativeEtaleHom_eq, nativeProHom_eq,
    nativeComparisonBeta_eq, canonicalRho, canonicalRhoInv, Iso.symm_hom, Iso.symm_inv]
    using closedSquare_of_monoidal (etaleScalar X φ) (proEtaleScalar X φ)
      (comparisonNu X) (comparisonNu X) (finiteHomRhoIso X φ).symm hm K M

/-- The inverse of the successive scalar/site comparison, before scalar reassociation.
Source: thm-coef-finite-hom proof, final paragraph, successive coefficient change
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
def finiteHomRhoChain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) (K : EtaleDerived A X) :=
  (proEtaleScalar X ψ).map (canonicalRho X φ K) ≫
    canonicalRho X ψ ((etaleScalar X φ).obj K)

/-- The successive scalar/site comparison, before scalar reassociation.
Source: thm-coef-finite-hom proof, final paragraph, successive coefficient change
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
def finiteHomRhoChainInv
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) (K : EtaleDerived A X) :=
  canonicalRhoInv X ψ ((etaleScalar X φ).obj K) ≫
    (proEtaleScalar X ψ).map (canonicalRhoInv X φ K)

/-- Pasting of the two coefficient-change squares, before reassociation. The
`rho_successive` and the tensor/Hom compositor equations identify this equation
with the direct A → C square.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
def finiteHomSuccessiveSiteSquare
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) (K M : EtaleDerived A X) : Prop :=
  (comparisonNu X).map
      ((etaleScalar X ψ).map (etaleHom X φ K M) ≫
        etaleHom X ψ ((etaleScalar X φ).obj K) ((etaleScalar X φ).obj M)) ≫
      comparisonBeta X ((etaleScalar X ψ).obj ((etaleScalar X φ).obj K))
        ((etaleScalar X ψ).obj ((etaleScalar X φ).obj M)) ≫
      (MonoidalClosed.pre (finiteHomRhoChain X φ ψ K)).app
        ((comparisonNu X).obj ((etaleScalar X ψ).obj ((etaleScalar X φ).obj M))) ≫
      (ihom ((proEtaleScalar X ψ).obj
        ((proEtaleScalar X φ).obj ((comparisonNu X).obj K)))).map
        (finiteHomRhoChainInv X φ ψ M) =
    finiteHomRhoChainInv X φ ψ ((ihom K).obj M) ≫
      (proEtaleScalar X ψ).map ((proEtaleScalar X φ).map (comparisonBeta X K M)) ≫
      (proEtaleScalar X ψ).map
        (proHom X φ ((comparisonNu X).obj K) ((comparisonNu X).obj M)) ≫
      proHom X ψ ((proEtaleScalar X φ).obj ((comparisonNu X).obj K))
        ((proEtaleScalar X φ).obj ((comparisonNu X).obj M))

private theorem nativeSuccessiveSiteSquare
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (hφ : FiniteHomRhoMonoidal X φ) (hψ : FiniteHomRhoMonoidal X ψ)
    (K M : EtaleDerived A X) : finiteHomSuccessiveSiteSquare X φ ψ K M := by
  let : (etaleScalar X φ).Monoidal := (etaleCore X φ).toMonoidal
  let : (etaleScalar X ψ).Monoidal := (etaleCore X ψ).toMonoidal
  let : (proEtaleScalar X φ).Monoidal := (proCore X φ).toMonoidal
  let : (proEtaleScalar X ψ).Monoidal := (proCore X ψ).toMonoidal
  let : (comparisonNu (R := A) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat A) X
  let : (comparisonNu (R := B) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat B) X
  let : (comparisonNu (R := C) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat C) X
  simpa only [finiteHomSuccessiveSiteSquare, nativeEtaleHom_eq, nativeProHom_eq,
    nativeComparisonBeta_eq, canonicalRho, canonicalRhoInv, finiteHomRhoChain,
    finiteHomRhoChainInv, Iso.symm_hom, Iso.symm_inv]
    using closedPastedSquare_of_monoidal (etaleScalar X φ) (etaleScalar X ψ)
      (proEtaleScalar X φ) (proEtaleScalar X ψ) (comparisonNu X) (comparisonNu X)
      (comparisonNu X) (finiteHomRhoIso X φ).symm (finiteHomRhoIso X ψ).symm hφ hψ K M

section SiteLawPredicates

variable {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]
  (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)

/-- The `rho_tensor` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_rho_tensor : Prop :=
  ∀ (K M : EtaleDerived A X),
    (comparisonNu X).map (etaleTensor X φ K M) ≫
        (AlgebraicGeometry.ProEtale.siteComparisonTensorIso (ModuleCat B) X
          ((etaleScalar X φ).obj K)).hom.app ((etaleScalar X φ).obj M) ≫
        (canonicalRhoInv X φ K ⊗ₘ canonicalRhoInv X φ M) =
      canonicalRhoInv X φ (K ⊗ M) ≫
        (proEtaleScalar X φ).map
          ((AlgebraicGeometry.ProEtale.siteComparisonTensorIso (ModuleCat A) X K).hom.app M) ≫
        proTensor X φ ((comparisonNu X).obj K) ((comparisonNu X).obj M)

/-- The `rho_unit` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_rho_unit : Prop :=
  (comparisonNu X).map (etaleCore X φ).εIso.inv ≫ finiteHomSiteUnit B X =
      canonicalRhoInv X φ (𝟙_ (EtaleDerived A X)) ≫
        (proEtaleScalar X φ).map (finiteHomSiteUnit A X) ≫ (proCore X φ).εIso.inv

/-- The `rho_successive` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_rho_successive : Prop :=
  ∀ (K : EtaleDerived A X),
    (finiteHomScalarComp (ProEt.topology X) φ ψ).hom.app ((comparisonNu X).obj K) ≫
        canonicalRho X (ψ.comp φ) K =
      finiteHomRhoChain X φ ψ K ≫
        (comparisonNu X).map ((finiteHomScalarComp X.smallEtaleTopology φ ψ).hom.app K)

/-- The `rho_identity` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_rho_identity : Prop :=
  ∀ (K : EtaleDerived A X),
    canonicalRho X (RingHom.id A) K ≫
        (comparisonNu X).map ((finiteHomScalarId X.smallEtaleTopology A).hom.app K) =
      (finiteHomScalarId (ProEt.topology X) A).hom.app ((comparisonNu X).obj K)

/-- The `site_square` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_site_square : Prop :=
  ∀ (K M : EtaleDerived A X), finiteHomSiteSquare X φ K M

/-- The `site_square_next` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_site_square_next : Prop :=
  ∀ (K M : EtaleDerived B X), finiteHomSiteSquare X ψ K M

/-- The `site_square_composite` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_site_square_composite : Prop :=
  ∀ (K M : EtaleDerived A X), finiteHomSiteSquare X (ψ.comp φ) K M

/-- The `site_square_identity` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_site_square_identity : Prop :=
  ∀ (K M : EtaleDerived A X), finiteHomSiteSquare X (RingHom.id A) K M

/-- The `site_square_successive` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_site_square_successive : Prop :=
  ∀ (K M : EtaleDerived A X), finiteHomSuccessiveSiteSquare X φ ψ K M

private theorem nativeRhoTensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (X : Scheme.{u}) (φ : A →+* B) (hm : FiniteHomRhoMonoidal X φ) :
    finiteHomSiteLaw_rho_tensor X φ := by
  let : (etaleScalar X φ).Monoidal := (etaleCore X φ).toMonoidal
  let : (proEtaleScalar X φ).Monoidal := (proCore X φ).toMonoidal
  let : (comparisonNu (R := A) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat A) X
  let : (comparisonNu (R := B) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat B) X
  unfold finiteHomSiteLaw_rho_tensor
  intro K M
  simpa only [etaleTensor, proTensor, canonicalRhoInv,
    AlgebraicGeometry.ProEtale.siteComparisonTensorIso_hom_app,
    Functor.OplaxMonoidal.comp_δ, Functor.comp_obj, comparisonNu,
    Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
    Functor.CoreMonoidal.toOplaxMonoidal_δ, Category.assoc, id_eq]
    using (monoidal_delta (finiteHomRhoIso X φ).inv hm K M).symm

private theorem nativeRhoUnit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (X : Scheme.{u}) (φ : A →+* B) (hm : FiniteHomRhoMonoidal X φ) :
    finiteHomSiteLaw_rho_unit X φ := by
  let : (etaleScalar X φ).Monoidal := (etaleCore X φ).toMonoidal
  let : (proEtaleScalar X φ).Monoidal := (proCore X φ).toMonoidal
  let : (comparisonNu (R := A) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat A) X
  let : (comparisonNu (R := B) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat B) X
  unfold finiteHomSiteLaw_rho_unit
  simpa only [finiteHomSiteUnit, canonicalRhoInv, Functor.OplaxMonoidal.comp_η,
    Functor.comp_obj, comparisonNu, Functor.Monoidal.εIso_inv,
    Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
    Functor.CoreMonoidal.toOplaxMonoidal_η] using (monoidal_eta (finiteHomRhoIso X φ).inv hm).symm

end SiteLawPredicates

/-- Equations for the canonical tensor, Hom and scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence).
The `laws` field includes the actual A → C tensor/Hom equations on both sites,
with the canonical compositor and identity isomorphisms. The rho tensor and unit
fields assert monoidality; the direct and pasted square fields assert its site
compatibility. No invertibility of beta is asserted. -/
structure FiniteHomSiteTensorCoherence
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) where
  laws : FiniteCoefficientHomLaws X φ ψ
  rho_tensor : finiteHomSiteLaw_rho_tensor X φ
  rho_unit : finiteHomSiteLaw_rho_unit X φ
  rho_successive : finiteHomSiteLaw_rho_successive X φ ψ
  rho_identity : finiteHomSiteLaw_rho_identity (A := A) X
  site_square : finiteHomSiteLaw_site_square X φ
  site_square_next : finiteHomSiteLaw_site_square_next X ψ
  site_square_composite : finiteHomSiteLaw_site_square_composite X φ ψ
  site_square_identity : finiteHomSiteLaw_site_square_identity (A := A) X
  site_square_successive : finiteHomSiteLaw_site_square_successive X φ ψ

/-- Finite coefficient tensor and internal-Hom coherence on both ordinary sites.
Source: latest blueprint thm-coef-finite-hom.proof.md, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence).
Proof: use the canonical K-flat scalar pullback tensor comparison, including its
symmetric monoidal, composition and identity normalizations. Apply thm-coef-finite-hom
for invertibility of v on bounded constructible finite-Tor objects. Its evaluation
transpose gives the displayed normalization. The derived mate of the ordinary
upper-star/scalar square is monoidal and has the stated composition and identity
comparisons. Uncurry the two sides of the beta/rho square: monoidality of rho and
naturality of evaluation make the resulting evaluations equal, so uniqueness of
transpose gives the square. Paste twice for A → B → C; the scalar compositor's
monoidality and the successive-v equation identify the pasted and direct squares.
The same argument with the scalar unit isomorphism gives the identity case. -/
theorem coefFiniteHomSiteTensorCoherence
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : k) ≠ 0)
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C)
    (hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    (hB : ∃ n : ℕ, (ell ^ n : B) = 0)
    (hC : ∃ n : ℕ, (ell ^ n : C) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    Nonempty (FiniteHomSiteTensorCoherence X φ ψ) := by
  obtain ⟨laws⟩ := thmCoefFiniteHom k hbase ell hell φ ψ hA hB hC X
  have hφ := coefFiniteHomRhoMonoidal X φ
  have hψ := coefFiniteHomRhoMonoidal X ψ
  have hcomp := coefFiniteHomRhoMonoidal X (ψ.comp φ)
  have hid := coefFiniteHomRhoMonoidal X (RingHom.id A)
  have hs := coefFiniteHomRhoScalarCoherence X φ ψ
  refine ⟨{
    laws := laws
    rho_tensor := nativeRhoTensor X φ hφ
    rho_unit := nativeRhoUnit X φ hφ
    rho_successive := ?_
    rho_identity := ?_
    site_square := ?_
    site_square_next := ?_
    site_square_composite := ?_
    site_square_identity := ?_
    site_square_successive := ?_ }⟩
  · unfold finiteHomSiteLaw_rho_successive
    simpa only [finiteHomRhoChain, Category.assoc] using hs.1
  · unfold finiteHomSiteLaw_rho_identity
    exact hs.2
  · unfold finiteHomSiteLaw_site_square
    exact nativeSiteSquare X φ hφ
  · unfold finiteHomSiteLaw_site_square_next
    exact nativeSiteSquare X ψ hψ
  · unfold finiteHomSiteLaw_site_square_composite
    exact nativeSiteSquare X (ψ.comp φ) hcomp
  · unfold finiteHomSiteLaw_site_square_identity
    exact nativeSiteSquare X (RingHom.id A) hid
  · unfold finiteHomSiteLaw_site_square_successive
    exact nativeSuccessiveSiteSquare X φ ψ hφ hψ

end WeilConjectures
