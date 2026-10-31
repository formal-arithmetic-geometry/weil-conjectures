/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRefinementConstruction
import all WeilConjectures.SixFunctors.OpenOperationModels
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependentSupplement
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses

/-! # Geometric realization with a prescribed scalar family

Source: Stacks Project, Modules on Sites and Cohomology on Sites.
(blueprint: lem-pur-ringed-refinement-geometric-calculus).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
open SheafOfModules.GeometricConstruction
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

private noncomputable def scalarEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {A B : Sheaf J RingCat.{u + 1}} (e : A ≅ B) :
    SheafOfModules.{u + 1} B ≌ SheafOfModules.{u + 1} A :=
  by
    have : (CategoryTheory.Equivalence.refl (C := C)).functor.IsContinuous J J :=
      inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
    have : (CategoryTheory.Equivalence.refl (C := C)).inverse.IsContinuous J J :=
      inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
    exact SheafOfModules.pushforwardPushforwardEquivalence
      (J := J) (K := J) (S := A) (R := B)
      (CategoryTheory.Equivalence.refl (C := C)) e.hom e.inv
      (by
        change Functor.whiskerRight (𝟙 (𝟭 Cᵒᵖ)) B.obj = e.inv.hom ≫ e.hom.hom
        rw [Functor.whiskerRight_id']
        exact (congrArg (fun f ↦ f.hom) e.inv_hom_id).symm)
      (by
        change e.hom.hom ≫ e.inv.hom ≫
          Functor.whiskerRight (𝟙 (𝟭 Cᵒᵖ)) A.obj = 𝟙 _
        rw [Functor.whiskerRight_id']
        change e.hom.hom ≫ e.inv.hom ≫ 𝟙 A.obj = 𝟙 _
        rw [Category.comp_id]
        exact congrArg (fun f ↦ f.hom) e.hom_inv_id)

private theorem scalarEquivalence_functor
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {A B : Sheaf J RingCat.{u + 1}} (e : A ≅ B) :
    (scalarEquivalence e).functor = SheafOfModules.restrictScalars e.hom := rfl

private theorem scalarEquivalence_pushforward
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {A B : Sheaf J RingCat.{u + 1}} (e : A ≅ B) :
    (scalarEquivalence e).functor =
      SheafOfModules.pushforward.{u + 1} (F := 𝟭 C) e.hom := rfl

set_option maxHeartbeats 2000000 in
-- Compare scalar restriction with the identical pushforward on module sheaves.
private noncomputable def scalarDirectIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    (R : Sheaf J CommRingCat.{u + 1}) (S S' : Sheaf K CommRingCat.{u + 1})
    (φ : R ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj S)
    (e : S ≅ S') :
    (scalarEquivalence ((sheafCompose K
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso e)).functor ⋙
        SheafOfModules.pushforward.{u + 1} (F := F)
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ) ≅
      SheafOfModules.pushforward.{u + 1} (F := F)
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (φ ≫ (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).map e.hom)) := by
  let A := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let B' := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S'
  let α : A ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj B :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ
  let β : B ⟶ B' :=
    (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map e.hom
  let γ : A ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj B' :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (φ ≫ (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).map e.hom)
  have h : α ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map β = γ := rfl
  rw [scalarEquivalence_pushforward]
  letI : (F ⋙ 𝟭 D).IsContinuous J K := Functor.isContinuous_comp F (𝟭 D) J K K
  exact SheafOfModules.pushforwardComp.{u + 1} (F := F) (G := 𝟭 D)
    (J := J) (K := K) (K' := K) (S := A) (R := B) (R' := B') α β ≪≫
    SheafOfModules.pushforwardCongr.{u + 1} (F := F) (J := J) (K := K)
      (S := A) (R := B') (φ := α ≫
      (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map β) (ψ := γ) h

set_option maxHeartbeats 8000000 in
-- Algebraic inverse image and its scalar-equivalence comparison have large types.
private theorem exactInverseImage
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [RepresentablyFlat F]
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf K CommRingCat.{u + 1})
    (c : (sheafPullback F CommRingCat.{u + 1} J K).obj R ≅ S) :
    let φ := (sheafAdjunctionContinuous F CommRingCat.{u + 1} J K).homEquiv _ _ c.hom
    let ψ := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ
    ∃ (P : Mod R ⥤ Mod S),
      Nonempty (P ⊣ SheafOfModules.pushforward.{u + 1} (F := F) ψ) ∧
        PreservesFiniteLimits P := by
  classical
  have : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  let L := sheafPullback F (Type (u + 1)) J K
  let V := F.sheafPushforwardContinuous (Type (u + 1)) J K
  let adj : L ⊣ V := sheafAdjunctionContinuous F (Type (u + 1)) J K
  let φ := (sheafAdjunctionContinuous F CommRingCat.{u + 1} J K).homEquiv _ _ c.hom
  obtain ⟨RI, ⟨I⟩⟩ := GeneralizedRinged.algebraicImage_exists J K L V adj R
  obtain ⟨b, hb⟩ := GeneralizedRinged.siteStructuralMap_exists F L adj S R φ RI I
  let U := CategoryTheory.forget CommRingCat.{u + 1}
  let : U.PreservesLeftKanExtensions F.op := by
    intro P
    let : PreservesFilteredColimitsOfSize.{u, u + 1} U :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    let : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt U P F.op V := by
      intro V
      infer_instance
    infer_instance
  let e := (sheafPullbackForgetIso J K F U).app R
  have ht : (adj.homEquiv _ _).symm ((sheafCompose J U).map φ) =
      e.inv ≫ (sheafCompose K U).map c.hom := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    have he : (sheafCompose J U).map
        ((sheafAdjunctionContinuous F CommRingCat.{u + 1} J K).unit.app R) ≫
        V.map e.hom = adj.unit.app ((sheafCompose J U).obj R) :=
      sheafPullbackForgetIso_unit J K F U R
    have he' : adj.unit.app ((sheafCompose J U).obj R) ≫ V.map e.inv =
        (sheafCompose J U).map
          ((sheafAdjunctionContinuous F CommRingCat.{u + 1} J K).unit.app R) := by
      rw [← he]
      rw [Category.assoc, ← V.map_comp, e.hom_inv_id, V.map_id]
      rfl
    rw [Functor.map_comp, ← Category.assoc, he']
    rfl
  have : IsIso ((sheafCompose K U).map b) := by
    rw [hb, ht]
    infer_instance
  have : IsIso b := isIso_of_reflects_iso b (sheafCompose K U)
  let E := scalarEquivalence ((sheafCompose K
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (asIso b))
  let a := GeneralizedRinged.tensorAdjunction b
  have hE : E.functor = SheafOfModules.restrictScalars
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map b) :=
    scalarEquivalence_functor _
  let aE := E.symm.toAdjunction.ofNatIsoRight (eqToIso hE)
  have : PreservesFiniteLimits (GeneralizedRinged.tensorFunctor b) :=
    preservesFiniteLimits_of_natIso (aE.leftAdjointUniq a)
  have : PreservesFiniteLimits I.modules := algebraicInverseImage_finiteLimits L I
  obtain ⟨am⟩ := GeneralizedRinged.supplied_adjunction F L adj S R φ RI I b hb
  exact ⟨I.modules ⋙ GeneralizedRinged.tensorFunctor b, ⟨am⟩,
    comp_preservesFiniteLimits _ _⟩

set_option maxHeartbeats 8000000 in
-- Transfer exactness across the canonical, universe-polymorphic adjunction.
private noncomputable def geometricOperation (m : Mode) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (R : Rings m Y) (S : Rings m X)
    (c : (ringInverse m f).obj R ≅ S) : Operation (baseChange m f) R S := by
  have : RepresentablyFlat (baseChange m f) := by
    cases m with
    | ordinary => exact flat_of_preservesFiniteLimits (proEtaleBaseChange f)
    | systems =>
      have : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
      constructor
      intro W
      exact IsCofiltered.of_equivalence
        (StructuredArrow.prodEquivalence W.1 W.2 (𝟭 ℕ) (proEtaleBaseChange f)).symm
  let h := exactInverseImage (topology m Y) (topology m X) (baseChange m f) R S c
  let P := h.choose
  let a := h.choose_spec.1.some
  have hP : PreservesFiniteLimits P := h.choose_spec.2
  let φ := (ringAdjunction m f).homEquiv _ _ c.hom
  let ψ : ((sheafCompose (topology m Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
      ((baseChange m f).sheafPushforwardContinuous RingCat.{u + 1}
        (topology m Y) (topology m X)).obj ((sheafCompose (topology m X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
    (sheafCompose (topology m Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ
  have hr : (SheafOfModules.pushforward.{u + 1} (F := baseChange m f) ψ).IsRightAdjoint := by
    dsimp only [ψ, φ, ringAdjunction]
    exact a.isRightAdjoint
  let a' := SheafOfModules.pullbackPushforwardAdjunction.{u + 1} ψ
  have hp : (SheafOfModules.pushforward.{u + 1} (F := baseChange m f) ψ).Additive :=
    ⟨by intro M N a b; ext U x; rfl⟩
  exact {
    coefficient := ψ
    rightAdjoint := hr
    pullbackAdditive := a'.left_adjoint_additive
    pushforwardAdditive := hp
    pullbackLimits := preservesFiniteLimits_of_natIso (a.leftAdjointUniq a')
    pullbackColimits := by
      have := a'.leftAdjoint_preservesColimits
      infer_instance
    kInjectives := by
      have : (topology m X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
        GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
          u + 1, u + 2, u + 1, u + 1, u + 1} _
      let : IsGrothendieckAbelian.{u + 1} (Mod S) :=
        (grothendieckAbelian_and_functorial_kInjective_resolutionsMixedUniverses
          (topology m X) S).1
      exact Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1} }

private theorem structural_unit {m : Mode} {T : Scheme.{u}} (c : Coefficients m T)
    {U V : Over T} (f : U ⟶ V) (R : Rings m T) :
    (ringAdjunction m V.hom).homEquiv _ _ (c.structural f R) =
      (ringAdjunction m U.hom).unit.app R ≫
        (c.directTriangle f).inv.app ((c.rings U).obj R) := by
  change ((ringAdjunction m V.hom).comp (ringAdjunction m f.left)).homEquiv _ _
    ((c.pull f).hom.app R) = _
  rw [Adjunction.homEquiv_unit]
  exact unit_conjugateEquiv_symm (ringAdjunction m U.hom)
    ((ringAdjunction m V.hom).comp (ringAdjunction m f.left))
    (c.directTriangle f).inv R |>.symm

set_option maxHeartbeats 8000000 in
-- The open-model transport compares the specified sheaf and module adjunctions.
private theorem openModel_exists (m : Mode) {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (R : Rings m Y) (S : Rings m X)
    (c : (ringInverse m j).obj R ≅ S) (o : Operation (baseChange m j) R S)
    (ho : o.coefficient = (sheafCompose (topology m Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((ringAdjunction m j).homEquiv _ _ c.hom)) : Nonempty (OpenModel j o) := by
  classical
  let aR := (openSiteAdjunction m j).sheafPushforwardContinuous
    (E := CommRingCat.{u + 1}) (topology m X) (topology m Y)
  let d := (aR.leftAdjointUniq (ringAdjunction m j)).app R ≪≫ c
  let E := scalarEquivalence ((sheafCompose (topology m X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso d)
  let φ := openRightCoefficient m j R
  have hd : φ ≫ ((baseChange m j).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m Y) (topology m X)).map d.hom =
      (ringAdjunction m j).homEquiv _ _ c.hom := by
    dsimp only [d, Iso.trans_hom, Iso.app_hom]
    rw [Functor.map_comp, ← Category.assoc]
    rw [show φ = aR.unit.app R from rfl,
      Adjunction.unit_leftAdjointUniq_hom_app]
    rfl
  let eDirect : E.functor ⋙ direct m j R (restrictRing m j R) φ ≅ o.pushforward := by
    refine scalarDirectIso (baseChange m j) R (restrictRing m j R) S φ d ≪≫
      SheafOfModules.pushforwardCongr ?_
    rw [ho]
    exact congrArg ((sheafCompose (topology m Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map) hd
  let a := ((openRestrictionAdjunction m j R).comp E.symm.toAdjunction).ofNatIsoRight eDirect
  let e := a.leftAdjointUniq o.moduleAdjunction
  obtain ⟨L⟩ : Nonempty (OpenExtension m j R) := by
    cases m with
    | ordinary => exact ordinaryOpenExtension_exists j R
    | systems => exact systemsOpenExtension_exists j R
  have hη (M) : L.adjunction.unit.app M = (L.sectionIso M).inv := by
    rw [← cancel_mono (L.sectionIso M).hom]
    exact L.sectionUnit M |>.trans (L.sectionIso M).inv_hom_id.symm
  have hunit (M : Mod (restrictRing m j R)) : IsIso (L.adjunction.unit.app M) := by
    rw [hη M]
    infer_instance
  have : IsIso L.adjunction.unit := NatIso.isIso_of_isIso_app _
  let ff := L.adjunction.fullyFaithfulLOfIsIsoUnit
  have : L.ordinary.Full := ff.full
  have : L.ordinary.Faithful := ff.faithful
  let b := (E.toAdjunction.comp L.adjunction).ofNatIsoRight e
  have : PreservesFiniteLimits (E.functor ⋙ L.ordinary) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (E.functor ⋙ L.ordinary) := comp_preservesFiniteColimits _ _
  have : (E.functor ⋙ L.ordinary).Additive := by
    have : E.functor.Additive := Functor.additive_of_preserves_binary_products E.functor
    infer_instance
  exact ⟨{
    functor := E.functor ⋙ L.ordinary
    adjunction := b
    unit := fun M ↦ by
      have := b.unit_isIso_of_L_fully_faithful
      infer_instance }⟩

private theorem ordinaryTriangle_comp {T : Scheme.{u}} {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) (Z : T.ProEt) :
    (siteTriangle .ordinary f).hom.app Z ≫
      (proEtaleBaseChange f.left).map ((siteTriangle .ordinary g).hom.app Z) =
      (siteTriangle .ordinary (f ≫ g)).hom.app Z ≫
        (siteComp .ordinary f g).hom.app ((proEtaleBaseChange W.hom).obj Z) := by
  have h {X Y Z T : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ T)
      (v : Y ⟶ T) (q : X ⟶ T) (hv : v = b ≫ c) (hq : q = a ≫ v) :
      MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) a v q hq ≪≫
          Functor.isoWhiskerRight (MorphismProperty.Over.pullbackComp b c v hv)
            (proEtaleBaseChange a) ≪≫ Functor.associator _ _ _ =
        MorphismProperty.Over.pullbackComp (a ≫ b) c q (by rw [hq, hv, Category.assoc]) ≪≫
          Functor.isoWhiskerLeft (proEtaleBaseChange c)
            (MorphismProperty.Over.pullbackComp a b) := by
    subst v
    exact MorphismProperty.Over.pullbackComp_assoc a b c q hq
  simpa only [siteTriangle, siteComp, baseChange, proEtaleBaseChange, Over.comp_left,
    Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Category.comp_id] using
    congrArg (fun e ↦ e.hom.app Z)
      (h f.left g.left W.hom V.hom U.hom (Over.w g).symm (Over.w f).symm)

private theorem triangle_comp (m : Mode) {T : Scheme.{u}} {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) (Z : Site m T) :
    (siteTriangle m f).hom.app Z ≫
      (baseChange m f.left).map ((siteTriangle m g).hom.app Z) =
      (siteTriangle m (f ≫ g)).hom.app Z ≫
        (siteComp m f g).hom.app ((baseChange m W.hom).obj Z) := by
  cases m with
  | ordinary => exact ordinaryTriangle_comp f g Z
  | systems =>
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact ordinaryTriangle_comp f g Z.2

private theorem triangle_id (m : Mode) {T : Scheme.{u}} (W : Over T)
    (Z : Site m T) :
    (siteTriangle m (𝟙 W)).hom.app Z =
      (siteId m W).inv.app ((baseChange m W.hom).obj Z) := by
  have h (Z : T.ProEt) : (siteTriangle .ordinary (𝟙 W)).hom.app Z =
      (siteId .ordinary W).inv.app ((baseChange .ordinary W.hom).obj Z) := by
    have := MorphismProperty.Over.pullbackComp_id_left (P := @WeaklyEtale) (Q := ⊤)
      W.hom W.hom (Over.w (𝟙 W)).symm
    simpa [siteTriangle, siteId, baseChange, proEtaleBaseChange,
      MorphismProperty.Over.pullbackCongr_refl] using
      congrArg (fun e ↦ e.hom.app Z) this
  cases m with
  | ordinary => exact h Z
  | systems => exact Prod.ext (Subsingleton.elim _ _) (h Z.2)

private noncomputable abbrev ringDirect (m : Mode) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (baseChange m f).sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology m Y) (topology m X)

private noncomputable def ringComp (m : Mode) {T : Scheme.{u}} {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) :
    ringDirect m f.left ⋙ ringDirect m g.left ≅ ringDirect m (f ≫ g).left :=
  Functor.sheafPushforwardContinuousComp' (siteComp m f g).symm CommRingCat.{u + 1}
    (topology m W.left) (topology m V.left) (topology m U.left)

private theorem triangle_direct_comp (m : Mode) {T : Scheme.{u}} {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) (N : Rings m U.left) :
    (ringDirect m W.hom).map ((ringComp m f g).hom.app N) ≫
        ((canonicalCoefficients m T).directTriangle (f ≫ g)).hom.app N =
      ((canonicalCoefficients m T).directTriangle g).hom.app
          ((ringDirect m f.left).obj N) ≫
        ((canonicalCoefficients m T).directTriangle f).hom.app N := by
  ext Z x
  change N.obj.map ((siteTriangle m (f ≫ g)).hom.app Z.unop).op
      (N.obj.map ((siteComp m f g).hom.app
        ((baseChange m W.hom).obj Z.unop)).op x) =
    N.obj.map ((siteTriangle m f).hom.app Z.unop).op
      (N.obj.map ((baseChange m f.left).map
        ((siteTriangle m g).hom.app Z.unop)).op x)
  have h := congrArg (fun q ↦ N.obj.map q.op x) (triangle_comp m f g Z.unop).symm
  simp only [Functor.map_comp, op_comp, CommRingCat.comp_apply] at h
  convert h using 1 <;> rfl

private theorem structural_comp (m : Mode) {T : Scheme.{u}} {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) (R : Rings m T) :
    let c := canonicalCoefficients m T
    c.structural g R ≫ (ringDirect m g.left).map (c.structural f R) ≫
      (ringComp m f g).hom.app ((c.rings U).obj R) = c.structural (f ≫ g) R := by
  let c := canonicalCoefficients m T
  let N := (c.rings U).obj R
  let df := c.directTriangle f
  let dg := c.directTriangle g
  let dh := c.directTriangle (f ≫ g)
  have hi : df.inv.app N ≫ dg.inv.app ((ringDirect m f.left).obj N) ≫
      (ringDirect m W.hom).map ((ringComp m f g).hom.app N) = dh.inv.app N := by
    apply (cancel_mono (dh.hom.app N)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [triangle_direct_comp m f g N]
    dsimp only [df, dg, dh, c] at *
    erw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  dsimp only [Coefficients.rings] at *
  apply ((ringAdjunction m W.hom).homEquiv _ _).injective
  erw [structural_unit c (f ≫ g) R]
  change (ringAdjunction m W.hom).unit.app R ≫
    (ringDirect m W.hom).map
      (c.structural g R ≫ (ringDirect m g.left).map (c.structural f R) ≫
        (ringComp m f g).hom.app N) = _
  simp only [Functor.map_comp]
  have hg := structural_unit c g R
  have hf := structural_unit c f R
  rw [Adjunction.homEquiv_unit] at hg hf
  rw [← Category.assoc, ← Category.assoc, hg]
  have hn := dg.inv.naturality (c.structural f R)
  change (ringDirect m V.hom).map (c.structural f R) ≫ dg.inv.app _ =
    dg.inv.app _ ≫ (ringDirect m W.hom).map
      ((ringDirect m g.left).map (c.structural f R)) at hn
  dsimp only [Coefficients.rings] at hg hf hn ⊢
  have hn' := congrArg
    (fun q ↦ q ≫ (ringDirect m W.hom).map ((ringComp m f g).hom.app N)) hn
  simp only [Category.assoc] at hn'
  simp only [Category.assoc]
  erw [← hn', ← Category.assoc, hf]
  have hh := congrArg (fun q ↦ (ringAdjunction m U.hom).unit.app R ≫ q) hi
  convert hh using 1 <;> (try simp only [Category.assoc]) <;> rfl

private theorem structural_id (m : Mode) {T : Scheme.{u}} (W : Over T)
    (R : Rings m T) :
    let c := canonicalCoefficients m T
    c.structural (𝟙 W) R ≫
      (Functor.sheafPushforwardContinuousNatTrans (siteId m W).inv
        CommRingCat.{u + 1} (topology m W.left) (topology m W.left)).app
          ((c.rings W).obj R) = 𝟙 _ := by
  let c := canonicalCoefficients m T
  let N := (c.rings W).obj R
  let q := (Functor.sheafPushforwardContinuousNatTrans (siteId m W).inv
    CommRingCat.{u + 1} (topology m W.left) (topology m W.left)).app N
  have hq : (c.directTriangle (𝟙 W)).hom.app N = (ringDirect m W.hom).map q := by
    ext Z x
    change N.obj.map ((siteTriangle m (𝟙 W)).hom.app Z.unop).op x =
      N.obj.map ((siteId m W).inv.app ((baseChange m W.hom).obj Z.unop)).op x
    rw [triangle_id]
    rfl
  apply ((ringAdjunction m W.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (ringAdjunction m W.hom).unit.app R ≫
    (ringDirect m W.hom).map (c.structural (𝟙 W) R ≫ q) =
      (ringAdjunction m W.hom).unit.app R ≫ (ringDirect m W.hom).map (𝟙 N)
  erw [(ringDirect m W.hom).map_comp, (ringDirect m W.hom).map_id,
    Category.comp_id, ← Category.assoc]
  have h := structural_unit c (𝟙 W) R
  rw [Adjunction.homEquiv_unit] at h
  erw [h, ← hq]
  change (ringAdjunction m W.hom).unit.app R ≫
    (c.directTriangle (𝟙 W)).inv.app N ≫ (c.directTriangle (𝟙 W)).hom.app N = _
  erw [Iso.inv_hom_id_app, Category.comp_id]

private theorem spatial_exists (m : Mode) (T : Scheme.{u})
    (o : Calculus (canonicalCoefficients m T)) : Nonempty (Spatial o) := by
  let comp {U V W : Over T} (f : U ⟶ V) (g : V ⟶ W) (R : Rings m T) :
      (o.operation f R).pushforward ⋙ (o.operation g R).pushforward ≅
        (o.operation (f ≫ g) R).pushforward := by
    letI : (baseChange m g.left ⋙ baseChange m f.left).IsContinuous
        (topology m W.left) (topology m U.left) :=
      Functor.isContinuous_comp _ _ _ (topology m V.left) _
    refine SheafOfModules.pushforwardComp _ _ ≪≫
      SheafOfModules.pushforwardCongr₂ _ (siteComp m f g) ?_
    simp only [o.coefficient]
    exact congrArg ((sheafCompose (topology m W.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map) (structural_comp m f g R)
  let identity (W : Over T) (R : Rings m T) :
      (o.operation (𝟙 W) R).pushforward ≅
        𝟭 (Mod (((canonicalCoefficients m T).rings W).obj R)) := by
    refine SheafOfModules.pushforwardNatIso _ (siteId m W).symm ≪≫
      SheafOfModules.pushforwardCongr ?_ ≪≫ SheafOfModules.pushforwardId _
    rw [o.coefficient]
    exact congrArg ((sheafCompose (topology m W.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map) (structural_id m W R)
  exact ⟨{
    comp := comp
    comp_sections := by intros; rfl
    identity := identity
    id_sections := by intros; rfl }⟩


/-- Realize the geometric part of the refinement calculus independently of scalar choices.

Source: Stacks Project, Modules on Sites, Tags 03D7, 03DI, 03DJ; Cohomology on
Sites, Tags 06YY, 07A6 and 0D6D; the geometric Steps 1--3 and 5 of
`lem-route-ringed-refinement-core`.
(blueprint: lem-pur-ringed-refinement-geometric-calculus).

Proof: on each pro-etale site take the sheaf inverse image and its adjunction to
sectionwise direct image. Its inverse image of a ring sheaf is the ring sheaf
specified by `ringInverse`. Transport the algebraic inverse-image construction
along the unique ring isomorphism whose adjunct is the specified ring unit.
For an arrow over T, follow this construction by scalar transport along `c.pull`.
The resulting right adjoint is the actual module pushforward for `c.structural`:
this follows by expanding the hom-equivalence defining that structural map.
Identify its left adjoint with the canonical `SheafOfModules.pullback` by uniqueness
of left adjoints. Inverse image of abelian sheaves is exact, and scalar transport
along a ring isomorphism is an equivalence, so this pullback is exact and additive.
Module sheaf categories are Grothendieck, hence supply the K-injective resolutions
required by `Operation`. In systems mode apply the same construction to the
vertical diagram site. The product decomposition of its structured-arrow categories
proves representable flatness; the index category of natural numbers need not have
finite limits. Base change acts by the identity on the index and includes all
transition maps.

For an open immersion identify its pro-etale site with localization at the open
object. Direct-sum extension on presheaves followed by module sheafification is
left adjoint to restriction and is exact. At an object of the open the unique
summand makes its unit invertible. For systems use the levelwise localized
adjunctions and the equivalence with sheaves on the vertical site. Transport this
right adjoint, and its unit, to the very pullback fixed in `Operation`, using
uniqueness of adjoints and the same structural ring isomorphism. This gives every
`OpenModel`; no flatness of coefficient transitions is used.

Define spatial direct-image composition at a module N and object Z by applying
N to the opposite of `siteComp.hom.app Z.unop`. The inverse uses `siteComp.inv`.
The linearity equation is the ring structural composition equation, obtained by
transposing the associativity square of the three ring inverse-image adjunctions.
That square commutes because `canonicalCoefficients` is defined from the actual
site associator. Naturality follows from that of `siteComp`. The identity uses
`siteId.inv` in the same way, with linearity obtained from the adjunction triangle.
These definitions give exactly the two required HEq section equations.
Finally assemble the operations and open models with the supplied scalar family s;
neither their construction nor the spatial maps use s. Thus the scalar field is
literally s, while both modes, arbitrary ring sheaves and the zero ring are allowed. -/
theorem geometricCalculus_exists (m : Mode) (T : Scheme.{u})
    (s : ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B),
      DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
        (((canonicalCoefficients m T).rings W).map a)) :
    ∃ (o : Calculus (canonicalCoefficients m T)) (_p : Spatial o), o.scalar = s := by
  classical
  let c := canonicalCoefficients m T
  let op {U V : Over T} (f : U ⟶ V) (R : Rings m T) :=
    geometricOperation m f.left ((c.rings V).obj R) ((c.rings U).obj R) ((c.pull f).app R)
  let o : Calculus c := {
    operation := op
    coefficient := by intros; rfl
    openModel := fun {U V} j _ R ↦ (openModel_exists m j.left _ _ ((c.pull j).app R)
      (op j R) rfl).some
    scalar := s }
  obtain ⟨p⟩ := spatial_exists m T o
  exact ⟨o, p, rfl⟩

end SheafOfModules.RingedRefinement
