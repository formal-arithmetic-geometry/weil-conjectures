/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparison
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Transport of internal module operations to sectionwise modules

Stacks Project, Modules on Sites, Tags 03D6 and 03D7; Categories, Tag 0B65.
(auxiliary; not a blueprint node).

The sectionwise pushforward uses the actual section-ring homomorphism induced by eta_f.
Pullback is its canonical left adjoint, hence the sheafified tensor-formula pullback.
Open extension is the canonical left adjoint of restriction. Unique characterizations fix
all comparisons; in particular no arbitrary natural isomorphism is used for base change.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u uA vA uB vB uC vC uD vD uE vE uAb vAb uBb vBb uCb vCb uDb vDb

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale
namespace InternalModuleOperations

private theorem comparison_existsUnique
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (E : A ≌ C) (H : B ≌ D) {L : A ⥤ B} {R : B ⥤ A}
    {L' : C ⥤ D} {R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (r : R ⋙ E.functor ≅ H.functor ⋙ R') :
    ∃! c : L ⋙ H.functor ≅ E.functor ⋙ L',
      (mateEquiv a b (.mk _ _ _ _ c.inv)).natTrans = r.hom := by
  obtain ⟨c, hc, huniq, _⟩ := exists_equivalenceAdjunctionComparison E H a b r
  exact ⟨c, hc, fun d hd ↦ huniq d hd⟩

private theorem sectionRingMap_existsUnique
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J Ab.{u + 1}] [HasSheafify K Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal] [(K.W (A := Ab.{u + 1})).IsMonoidal]
    (F : C ⥤ D) [F.IsContinuous J K]
    (RX : Sheaf K Ab.{u + 1}) (RY : Sheaf J Ab.{u + 1})
    [MonObj RX] [IsCommMonObj RX] [MonObj RY] [IsCommMonObj RY]
    (ψ : RY ⟶ (F.sheafPushforwardContinuous Ab.{u + 1} J K).obj RX) [IsMonHom ψ] :
    let BX := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (sectionRingSheaf.{u + 1, u + 1, u} K RX)
    let BY := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (sectionRingSheaf.{u + 1, u + 1, u} J RY)
    ∃! φ : BY ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj BX,
      ∀ (V : Cᵒᵖ) (r : BY.obj.obj V), (φ.hom.app V).hom r = (ψ.hom.app V).hom r := by
  dsimp only
  let BX := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf.{u + 1, u + 1, u} K RX)
  let BY := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf.{u + 1, u + 1, u} J RY)
  let AX := Mon.mk RX
  let AY := Mon.mk RY
  let IY := sheafToPresheaf J Ab.{u + 1}
  let IX := sheafToPresheaf K Ab.{u + 1}
  let P := F.sheafPushforwardContinuous Ab.{u + 1}
    J K
  let W := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj F.op
  let e : IX ⋙ W ≅ P ⋙ IY :=
    Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F Ab.{u + 1} J K
  let h : IY.mapMon.obj AY ⟶
      (IX ⋙ W).mapMon.obj AX :=
    IY.mapMon.map
      ({ hom := ψ
         isMonHom_hom := inferInstance } :
        Mon.mk RY ⟶ P.mapMon.obj AX) ≫
      (Functor.mapMonCompIso (F := P) (G := IY)).inv.app _ ≫
        (Functor.mapMonNatIso e).inv.app _
  have he : e.inv.app RX = 𝟙 _ := by
    apply (cancel_epi (e.hom.app RX)).mp
    rw [e.hom_inv_id_app]
    simp only [e,
      Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
      Category.comp_id]
    rfl
  let τ : IY.obj RY ⟶
      (IX ⋙ W).obj RX := ψ.hom
  have hh : h.hom = τ := by
    change ψ.hom ≫
      e.inv.app RX = τ
    rw [he]
    rfl
  let φ : BY ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1}
      J K).obj (BX) :=
    ⟨Functor.whiskerRight (Monoidal.MonFunctorCategoryEquivalence.functor.map h)
      monToRing⟩
  have hφ : ∀ (V : Cᵒᵖ) (r : (BY).obj.obj V),
      (φ.hom.app V).hom r = (ψ.hom.app V).hom r := by
    intro V r
    change ((h.hom.app V).hom r) = _
    rw [hh]
    rfl
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply RingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (hψ V r).trans (hφ V r).symm

private theorem section_action {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J Ab.{u + 1}] [HasSheafify K Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal] [(K.W (A := Ab.{u + 1})).IsMonoidal]
    (F : C ⥤ D) [F.IsContinuous J K]
    (RX : Sheaf K Ab.{u + 1}) (RY : Sheaf J Ab.{u + 1})
    (N : Sheaf K Ab.{u + 1})
    (ψ : RY ⟶ (F.sheafPushforwardContinuous Ab.{u + 1} J K).obj RX)
    (a : RX ⊗ N ⟶ N) (V : Cᵒᵖ) (r : RY.obj.obj V)
    (m : N.obj.obj (F.op.obj V)) :
    ((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1}) RY
      ((F.sheafPushforwardContinuous Ab.{u + 1} J K).obj N)).app V ≫
      (ψ ▷ _ ≫ Functor.LaxMonoidal.μ (F.sheafPushforwardContinuous Ab.{u + 1} J K)
        RX N ≫ (F.sheafPushforwardContinuous Ab.{u + 1} J K).map a).hom.app V).hom
        (r ⊗ₜ[ℤ] m) =
    ((Functor.LaxMonoidal.μ (sheafToPresheaf K Ab.{u + 1}) RX N).app (F.op.obj V) ≫
      a.hom.app (F.op.obj V)).hom ((ψ.hom.app V).hom r ⊗ₜ[ℤ] m) := by
  let IY := sheafToPresheaf J Ab.{u + 1}
  let P := F.sheafPushforwardContinuous Ab.{u + 1} J K
  have hn := congr_app (Functor.LaxMonoidal.μ_natural_left IY ψ (P.obj N)) V
  simp only [NatTrans.comp_app] at hn
  have ht := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    F Ab.{u + 1} J K RX N V
  change ((Functor.LaxMonoidal.μ IY RY (P.obj N)).app V ≫
    (ψ ▷ P.obj N).hom.app V ≫ (Functor.LaxMonoidal.μ P RX N).hom.app V ≫
    (P.map a).hom.app V).hom (r ⊗ₜ[ℤ] m) = _
  erw [← reassoc_of% hn, reassoc_of% ht]
  change ((Functor.LaxMonoidal.μ (sheafToPresheaf K Ab.{u + 1}) RX N).app
    (F.op.obj V) ≫ a.hom.app (F.op.obj V)).hom
      ((ψ.hom.app V ▷ N.obj.obj (F.op.obj V)).hom (r ⊗ₜ[ℤ] m)) = _
  rw [AddCommGrpCat.MonoidalCategory.whiskerRight_tmul]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The reconstructed section-ring sheaf B_T, using the recorded reconstruction.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
noncomputable abbrev ring (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (condensedRingObj Λ T))

/-- The fixed internal/sectionwise equivalence E_T, not a new equivalence.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
noncomputable abbrev equivalence (T : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) ≌
      SheafOfModules.{u + 1} (ring Λ T) :=
  sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (condensedRingObj Λ T)

/-- The base-change functor on the small pro-etale sites.
Source: Stacks 03D6 (auxiliary; not a blueprint node). -/
noncomputable abbrev siteMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ f

/-- Continuity of the existing base-change functor, exposed at this abbreviation.
Source: Stacks 03D6 (auxiliary; not a blueprint node). -/
instance siteMap_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (siteMap f).IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isContinuous_overPullback f

/-- The adjunct of alpha_f induces the unique section-ring homomorphism with its given
underlying additive map.
Source: Stacks 03D6 (auxiliary; not a blueprint node).
Proof: Step 2. Reconstruct multiplication and unit by evaluating the tensor action on pure
section tensors. Monoidality of eta_f gives preservation of multiplication and unit;
its naturality gives restriction compatibility. Faithfulness of the forgetful ring functor
makes this lift unique. The underlying pushforward is evaluation at V times_Y X. -/
theorem coefficientMap_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! φ : ring Λ Y ⟶ ((siteMap f).sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (ring Λ X),
      ∀ (V : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj V),
        (φ.hom.app V).hom r = ((condensedPushforwardHom Λ f).hom.app V).hom r := by
  let := siteMap_continuous f
  exact sectionRingMap_existsUnique.{u} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (siteMap f) (condensedRingObj Λ X) (condensedRingObj Λ Y)
    (condensedPushforwardHom Λ f)

/-- The canonical section-ring map B_Y -> f_* B_X, fixed by eta_f on every section.
Source: Stacks 03D6 (auxiliary; not a blueprint node). -/
noncomputable def coefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ring Λ Y ⟶ ((siteMap f).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (ring Λ X) :=
  (coefficientMap_existsUnique Λ f).exists.choose

private theorem coefficientMap_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj V) :
    ((coefficientMap Λ f).hom.app V).hom r =
      ((condensedPushforwardHom Λ f).hom.app V).hom r := by
  unfold coefficientMap
  exact (coefficientMap_existsUnique Λ f).exists.choose_spec V r

/-- Ordinary direct image with scalar restriction along the adjunct of alpha_f.
Source: Stacks 03D6 (auxiliary; not a blueprint node). -/
noncomputable abbrev lowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.pushforward.{u + 1} (F := siteMap f) (coefficientMap Λ f)

/-- The canonical direct-image comparison is uniquely the identity on underlying sheaves.
Source: Stacks 03D6 (auxiliary; not a blueprint node).
Proof: Steps 1--2. E preserves underlying sections and maps. The internal lax action is
eta_f(r) times n, precisely scalar restriction in the sectionwise direct image. Thus the
identity sheaf map and its inverse are linear and natural. Their underlying maps determine
them uniquely by faithfulness. -/
theorem lowerComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! r : CondensedRing.lowerStar Λ f ⋙ (equivalence Λ Y).functor ≅
        (equivalence Λ X).functor ⋙ lowerStar Λ f,
      ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
        (V : Y.ProEtᵒᵖ) (m : ((lowerStar Λ f).obj ((equivalence Λ X).functor.obj M)).val.obj V),
        ((r.hom.app M).val.app V).hom m = m := by
  classical
  let L := CondensedRing.lowerStar Λ f ⋙ (equivalence Λ Y).functor
  let R := (equivalence Λ X).functor ⋙ lowerStar Λ f
  have h (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) (V : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj V)
      (m : (R.obj M).val.obj V) :
      ((ModuleCat.smul ((L.obj M).val.obj V) r).hom) m =
        ((ModuleCat.smul ((R.obj M).val.obj V) r).hom) m := by
    change ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)
      (((siteMap f).sheafPushforwardContinuous Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj M.X)).app V ≫
      (condensedPushforwardHom Λ f ▷ _ ≫ Functor.LaxMonoidal.μ
        ((siteMap f).sheafPushforwardContinuous Ab.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X))
        (condensedRingObj Λ X) M.X ≫
          ((siteMap f).sheafPushforwardContinuous Ab.{u + 1}
            (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
              (Mod.act M.X)).hom.app V).hom (r ⊗ₜ[ℤ] m) = _
    rw [section_action]
    change ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X) M.X).app ((siteMap f).op.obj V) ≫
      (Mod.act M.X).hom.app ((siteMap f).op.obj V)).hom
        (((condensedPushforwardHom Λ f).hom.app V).hom r ⊗ₜ[ℤ] m) =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X) M.X).app ((siteMap f).op.obj V) ≫
        (Mod.act M.X).hom.app ((siteMap f).op.obj V)).hom
          (((coefficientMap Λ f).hom.app V).hom r ⊗ₜ[ℤ] m)
    have hc : ((coefficientMap Λ f).hom.app V).hom r =
        ((condensedPushforwardHom Λ f).hom.app V).hom r :=
      coefficientMap_apply Λ f V r
    rw [hc]
  let q (M) : L.obj M ⟶ R.obj M :=
    ⟨PresheafOfModules.homMk (M₁ := (L.obj M).val) (M₂ := (R.obj M).val)
      (𝟙 _) (fun V r m ↦ h M V r m)⟩
  let p (M) : R.obj M ⟶ L.obj M :=
    ⟨PresheafOfModules.homMk (M₁ := (R.obj M).val) (M₂ := (L.obj M).val)
      (𝟙 _) (fun V r m ↦ (h M V r m).symm)⟩
  let c : L ≅ R := NatIso.ofComponents
    (fun M ↦ { hom := q M, inv := p M,
               hom_inv_id := by ext V m; rfl,
               inv_hom_id := by ext V m; rfl })
    (fun α ↦ by ext V m; rfl)
  refine ⟨c, ?_, ?_⟩
  · intro M V m
    rfl
  · intro d hd
    apply Iso.ext
    ext M V m
    exact hd M V m

/-- The identity-on-sections direct-image comparison.
Source: Stacks 03D6 (auxiliary; not a blueprint node). -/
noncomputable def lowerComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.lowerStar Λ f ⋙ (equivalence Λ Y).functor ≅
      (equivalence Λ X).functor ⋙ lowerStar Λ f :=
  (lowerComparison_existsUnique Λ f).exists.choose

attribute [local irreducible] squareData

attribute [local irreducible] internalSquare sectionSquare

end InternalModuleOperations
end AlgebraicGeometry.ProEtale
