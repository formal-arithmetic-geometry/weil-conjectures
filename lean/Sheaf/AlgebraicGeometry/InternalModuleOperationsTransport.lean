/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleModuleObjects
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.SheafTensorStructure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Transport of internal module operations to sectionwise modules

Source: blueprint main-20261015, Nagata density normalization, sheaves proof, Steps 1--2;
Stacks Project, Modules on Sites, Tags 03D6 and 03D7; Categories, Tag 0B65.
(blueprint: lem-sfb-internal-module-operations-transport).

The sectionwise pushforward uses the actual section-ring homomorphism induced by eta_f.
Pullback is its canonical left adjoint, hence the sheafified tensor-formula pullback.
Open extension is the canonical left adjoint of restriction. Unique characterizations fix
all comparisons; in particular no arbitrary natural isomorphism is used for base change.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale
namespace InternalModuleOperations

private theorem comparison_existsUnique
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (E : A ≌ C) (H : B ≌ D) {L : A ⥤ B} {R : B ⥤ A}
    {L' : C ⥤ D} {R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (r : R ⋙ E.functor ≅ H.functor ⋙ R') :
    ∃! c : L ⋙ H.functor ≅ E.functor ⋙ L',
      (mateEquiv a b (.mk _ _ _ _ c.inv)).natTrans = r.hom := by
  let β : TwoSquare R H.functor E.functor R' := .mk _ _ _ _ r.hom
  let α := (mateEquiv a b).symm β
  have hγ : IsIso (mateEquiv H.toAdjunction E.toAdjunction β).natTrans := by
    simp only [mateEquiv_apply]
    infer_instance
  have hα : IsIso α.natTrans := by
    have h := iterated_mateEquiv_conjugateEquiv a b E.toAdjunction H.toAdjunction α
    have : IsIso (conjugateEquiv (a.comp H.toAdjunction)
        (E.toAdjunction.comp b) α.natTrans) := by
      rw [← h]
      simpa only [α, Equiv.apply_symm_apply] using hγ
    exact conjugateEquiv_of_iso (a.comp H.toAdjunction)
      (E.toAdjunction.comp b) α.natTrans
  refine ⟨(asIso α.natTrans).symm, ?_, ?_⟩
  · exact congrArg TwoSquare.natTrans ((mateEquiv a b).apply_symm_apply β)
  · intro c hc
    apply Iso.ext_inv
    change c.inv = α.natTrans
    have h : mateEquiv a b (.mk _ _ _ _ c.inv) = β := by
      ext M
      exact congr_app hc M
    exact congrArg TwoSquare.natTrans ((mateEquiv a b).eq_symm_apply.mpr h)

private theorem presheafPushforward_isRightAdjoint
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) (RX : Dᵒᵖ ⥤ RingCat.{u + 1}) (RY : Cᵒᵖ ⥤ RingCat.{u + 1})
    (ψ : RY ⟶ G.op ⋙ RX) : (PresheafOfModules.pushforward.{u + 1} ψ).IsRightAdjoint := by
  let eX : PresheafOfModules.{u + 1} RX ≌
      PresheafOfModules.{u + 1} ((AsSmall.down.{u, u + 1, 0} (C := D)).op ⋙ RX) :=
    { functor := PresheafOfModules.pushforward₀ (AsSmall.down.{u, u + 1, 0} (C := D)) RX
      inverse := PresheafOfModules.pushforward₀ (AsSmall.up.{u, u + 1, 0} (C := D)) _
      unitIso := Iso.refl _
      counitIso := Iso.refl _ }
  let eY : PresheafOfModules.{u + 1} RY ≌
      PresheafOfModules.{u + 1} ((AsSmall.down.{u, u + 1, 0} (C := C)).op ⋙ RY) :=
    { functor := PresheafOfModules.pushforward₀ (AsSmall.down.{u, u + 1, 0} (C := C)) RY
      inverse := PresheafOfModules.pushforward₀ (AsSmall.up.{u, u + 1, 0} (C := C)) _
      unitIso := Iso.refl _
      counitIso := Iso.refl _ }
  let F := AsSmall.down.{u, u + 1, 0} (C := C) ⋙ G ⋙
    AsSmall.up.{u, u + 1, 0} (C := D)
  let φ : (AsSmall.down.{u, u + 1, 0} (C := C)).op ⋙ RY ⟶
      F.op ⋙ (AsSmall.down.{u, u + 1, 0} (C := D)).op ⋙ RX :=
    Functor.whiskerLeft (AsSmall.down.{u, u + 1, 0} (C := C)).op ψ
  have : (PresheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint := inferInstance
  have : eX.functor.IsRightAdjoint := eX.symm.toAdjunction.isRightAdjoint
  have : eY.inverse.IsRightAdjoint := eY.toAdjunction.isRightAdjoint
  have : (eX.functor ⋙ PresheafOfModules.pushforward φ ⋙ eY.inverse).IsRightAdjoint :=
    inferInstance
  exact this

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
  let : IsMonHom τ := by
    rw [← hh]
    exact h.isMonHom_hom
  let k : IY.mapMon.obj AY ⟶ (IX ⋙ W).mapMon.obj AX := Mon.Hom.mk' τ
  let φ : BY ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1}
      J K).obj (BX) :=
    ⟨Functor.whiskerRight (Monoidal.MonFunctorCategoryEquivalence.functor.map k)
      monToRing⟩
  have hφ : ∀ (V : Cᵒᵖ) (r : (BY).obj.obj V),
      (φ.hom.app V).hom r = (ψ.hom.app V).hom r := by
    intro V r
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
Source: Stacks 00YV (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev ring (T : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (condensedRingObj Λ T))

/-- The fixed internal/sectionwise equivalence E_T, not a new equivalence.
Source: Stacks 00YV (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev equivalence (T : Scheme.{u}) :=
  sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (condensedRingObj Λ T)

/-- The base-change functor on the small pro-etale sites.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev siteMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ f

/-- Continuity of the existing base-change functor, exposed at this abbreviation.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
instance siteMap_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (siteMap f).IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isContinuous_overPullback f

/-- The adjunct of alpha_f induces the unique section-ring homomorphism with its given
underlying additive map.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport).
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
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def coefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ring Λ Y ⟶ ((siteMap f).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (ring Λ X) :=
  (coefficientMap_existsUnique Λ f).exists.choose

/-- Ordinary direct image with scalar restriction along the adjunct of alpha_f.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev lowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.pushforward.{u + 1} (F := siteMap f) (coefficientMap Λ f)

/-- Presheaf pullback exists in the coefficient universe even though the small pro-etale
site has object universe u+1 and morphism universe u.
Source: the tensor-formula construction in Stacks 03D7
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: transport both sites and their presheaves to coefficient-sized small models.
On these models the presheaf pullback is the left Kan extension and sectionwise scalar
extension; its Hom bijection sends m to 1 tensor m. Transport that adjunction back.
No equality between the original site object and morphism universes is imposed. -/
@[instance]
theorem presheafLowerStar_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (PresheafOfModules.pushforward.{u + 1}
      (F := siteMap f) (coefficientMap Λ f).hom).IsRightAdjoint := by
  exact presheafPushforward_isRightAdjoint (siteMap f) (ring Λ X).obj (ring Λ Y).obj
    (coefficientMap Λ f).hom

/-- The canonical sectionwise ringed-topos pullback, constructed by presheaf pullback
and sheafification: inverse image followed by B_X tensor_{f^{-1}B_Y} (-).
Source: Stacks 03D7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev upperStar {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.forget (ring Λ Y) ⋙
    PresheafOfModules.pullback.{u + 1} (F := siteMap f) (coefficientMap Λ f).hom ⋙
      PresheafOfModules.sheafification (R₀ := (ring Λ X).obj) (𝟙 (ring Λ X).obj)

/-- The tensor-formula sectionwise adjunction, with its sheafification Hom bijection.
Source: Stacks 03D7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev adjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.PullbackConstruction.adjunction.{u + 1}
    (F := siteMap f) (coefficientMap Λ f)

/-- The canonical direct-image comparison is uniquely the identity on underlying sheaves.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport).
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
      (coefficientMap_existsUnique Λ f).exists.choose_spec V r
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
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def lowerComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.lowerStar Λ f ⋙ (equivalence Λ Y).functor ≅
      (equivalence Λ X).functor ⋙ lowerStar Λ f :=
  (lowerComparison_existsUnique Λ f).exists.choose

/-- The mate of the direct-image comparison is invertible and uniquely fixes pullback.
Source: Stacks 03D7, Categories 0B65
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: Steps 3--4. Conjugate the specified internal adjunction by E. The two left
adjoints of the identified direct image are uniquely isomorphic by the unit equation
lem-weil-pbc-conjugate-iso-unit-equation. Undo the conjugation. The mate equation below
is exactly the Hom-transposition identity; evaluating it on identities gives both unit
and counit equations, by lem-weil-pbc-adjunction-of-natural-bijection. -/
theorem upperComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! c : CondensedRing.upperStar Λ f ⋙ (equivalence Λ X).functor ≅
        (equivalence Λ Y).functor ⋙ upperStar Λ f,
      (mateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
        (.mk _ _ _ _ c.inv)).natTrans =
        (lowerComparison Λ f).hom := by
  exact comparison_existsUnique (equivalence Λ Y) (equivalence Λ X)
    (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
    (lowerComparison Λ f)

/-- The pullback comparison normalized by the actual specified adjunctions.
Source: Stacks 03D7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def upperComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.upperStar Λ f ⋙ (equivalence Λ X).functor ≅
      (equivalence Λ Y).functor ⋙ upperStar Λ f :=
  (upperComparison_existsUnique Λ f).exists.choose

/-- For an open immersion, sectionwise restriction admits extension by zero.
Source: blueprint module-lower-shriek, Extension by zero clause
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: Step 5. Conjugate the given internal open-extension adjunction by the fixed
E equivalences, and identify its right adjoint using upperComparison. This supplies
the sectionwise left adjoint, characterized uniquely by its extension-by-zero universal
property. The same underlying abelian extension by zero carries the transported action. -/
@[instance]
theorem upperStar_isRightAdjoint {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] : (upperStar Λ j).IsRightAdjoint := by
  have : (CondensedRing.upperStar Λ j).IsRightAdjoint :=
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).isRightAdjoint
  have : (CondensedRing.upperStar Λ j ⋙ (equivalence Λ U).functor).IsRightAdjoint :=
    inferInstance
  have : ((equivalence Λ T).functor ⋙ upperStar Λ j).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso (upperComparison Λ j)
  exact (Functor.isRightAdjoint_comp_iff_right
    (equivalence Λ T).functor (upperStar Λ j)).mp inferInstance

/-- Sectionwise extension by zero, the canonical left adjoint of restriction.
Source: blueprint module-lower-shriek, Extension by zero clause
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev extension {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (upperStar Λ j).leftAdjoint

/-- The sectionwise open-extension adjunction to restriction.
Source: blueprint module-lower-shriek, Extension by zero clause
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev openAdjunction {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  Adjunction.ofIsRightAdjoint (upperStar Λ j)

/-- The canonical open-extension comparison, normalized by the specified adjunctions.
Source: blueprint module-lower-shriek, Extension by zero clause; Categories 0B65
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: Step 5. Apply unit-normalized uniqueness of left adjoints again to the internal
open adjunction and the sectionwise one, with upperComparison identifying the right
adjoints. The mate equation identifies the Hom bijections, units and counits. -/
theorem openComparison_existsUnique {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    ∃! o : CondensedRing.openImmersionLowerShriek Λ j ⋙ (equivalence Λ T).functor ≅
        (equivalence Λ U).functor ⋙ extension Λ j,
      (mateEquiv (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
        (openAdjunction Λ j) (.mk _ _ _ _ o.inv)).natTrans = (upperComparison Λ j).hom := by
  exact comparison_existsUnique (equivalence Λ U) (equivalence Λ T)
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j) (openAdjunction Λ j)
    (upperComparison Λ j)

/-- The uniquely adjunction-normalized comparison for extension by zero.
Source: blueprint module-lower-shriek, Extension by zero clause
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def openComparison {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    CondensedRing.openImmersionLowerShriek Λ j ⋙ (equivalence Λ T).functor ≅
      (equivalence Λ U).functor ⋙ extension Λ j :=
  (openComparison_existsUnique Λ j).exists.choose

/-- The sectionwise direct-image composition comparison is the ordinary sheaf comparison.
Source: blueprint module-upper-star-comp; Stacks 03D6
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: Step 6. Evaluation rebrackets the iterated fibre product. The two scalar actions
agree by compatibility of eta_f with composition, so the underlying abelian comparison
is linear, natural and invertible. Faithfulness gives uniqueness. -/
theorem lowerComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! c : lowerStar Λ f ⋙ lowerStar Λ g ≅ lowerStar Λ (f ≫ g),
      ∀ (M : SheafOfModules.{u + 1} (ring Λ X)) (V : Z.ProEtᵒᵖ)
        (m : ((lowerStar Λ g).obj ((lowerStar Λ f).obj M)).val.obj V),
        ((c.hom.app M).val.app V).hom m =
          (((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app
            ((SheafOfModules.toSheaf (ring Λ X)).obj M)).hom.app V).hom m := by
  sorry

/-- The canonical sectionwise direct-image composition comparison.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def lowerComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    lowerStar Λ f ⋙ lowerStar Λ g ≅ lowerStar Λ (f ≫ g) :=
  (lowerComp_existsUnique Λ f g).exists.choose

/-- The sectionwise pullback-composition comparison, conjugate to direct-image composition.
Source: blueprint module-upper-star-comp
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def upperComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    upperStar Λ (f ≫ g) ≅ upperStar Λ g ⋙ upperStar Λ f :=
  (Adjunction.leftAdjointCompIso (adjunction Λ g) (adjunction Λ f)
    (adjunction Λ (f ≫ g)) (lowerComp Λ f g)).symm

/-- The actual internal pullback-composition comparison around a scheme square.
Source: blueprint module-upper-star-comp
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def internalSquare {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    (sq : ChosenCartesianSquare g' j' j g) :
    CondensedRing.upperStar Λ j ⋙ CondensedRing.upperStar Λ g' ≅
      CondensedRing.upperStar Λ g ⋙ CondensedRing.upperStar Λ j' :=
  (CondensedRing.upperStarComp Λ g' j).symm ≪≫
    eqToIso (congrArg (CondensedRing.upperStar Λ) sq.w) ≪≫
      CondensedRing.upperStarComp Λ j' g

/-- The sectionwise pullback-composition comparison around the same square.
Source: blueprint module-upper-star-comp
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def sectionSquare {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    (sq : ChosenCartesianSquare g' j' j g) :
    upperStar Λ j ⋙ upperStar Λ g' ≅ upperStar Λ g ⋙ upperStar Λ j' :=
  (upperComp Λ g' j).symm ≪≫ eqToIso (congrArg (upperStar Λ) sq.w) ≪≫ upperComp Λ j' g

/-- The internal open-extension base-change map, with the specified unit and counit.
Source: Stacks 07A7 and the node proof Step 7
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def internalBaseChange {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : ChosenCartesianSquare g' j' j g) :
    CondensedRing.upperStar Λ g' ⋙ CondensedRing.openImmersionLowerShriek Λ j' ⟶
      CondensedRing.openImmersionLowerShriek Λ j ⋙ CondensedRing.upperStar Λ g :=
  ((mateEquiv (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j')).symm
      (.mk _ _ _ _ (internalSquare Λ sq).hom)).natTrans

/-- The sectionwise map is the same adjunction mate of pullback composition.
Source: Stacks 07A7 and the node proof Step 7
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def sectionBaseChange {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : ChosenCartesianSquare g' j' j g) :
    upperStar Λ g' ⋙ extension Λ j' ⟶ extension Λ j ⋙ upperStar Λ g :=
  ((mateEquiv (openAdjunction Λ j) (openAdjunction Λ j')).symm
    (.mk _ _ _ _ (sectionSquare Λ sq).hom)).natTrans

/-- Comparison of the source of the open-extension base-change transformation.
Source: node proof Step 7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def baseChangeSourceComparison {U' U T' : Scheme.{u}}
    (g' : U' ⟶ U) (j' : U' ⟶ T') [IsOpenImmersion j'] :
    (CondensedRing.upperStar Λ g' ⋙ CondensedRing.openImmersionLowerShriek Λ j') ⋙
        (equivalence Λ T').functor ≅
      (equivalence Λ U).functor ⋙ (upperStar Λ g' ⋙ extension Λ j') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (openComparison Λ j') ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (upperComparison Λ g') _ ≪≫
      Functor.associator _ _ _

/-- Comparison of the target of the open-extension base-change transformation.
Source: node proof Step 7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def baseChangeTargetComparison {U T T' : Scheme.{u}}
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek Λ j ⋙ CondensedRing.upperStar Λ g) ⋙
        (equivalence Λ T').functor ≅
      (equivalence Λ U).functor ⋙ (extension Λ j ⋙ upperStar Λ g) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (upperComparison Λ g) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (openComparison Λ j) _ ≪≫
      Functor.associator _ _ _

/-- Internal module operations agree canonically with sectionwise operations, including
specified adjunctions, open-extension mates and exactness.
Source: blueprint main-20261015, Nagata density normalization sheaves proof, Steps 1--2;
Stacks 03D6, 03D7, 0B65 and 07A7
(blueprint: lem-sfb-internal-module-operations-transport).

Proof (the eight steps of the DAG node):
1. E_T preserves underlying section groups and maps. Its action formula is
   a(r tensor m), so it and its inverse preserve addition and zero of morphisms
   (def-weil-pbc-internal-abelian-sheaf-module-equivalence,
   det-def-sfb-sheaf-tensor-structure).
2. Both direct images evaluate N on V times_T T'. The lax tensor map sends pure
   tensors to the same tensors there. Their actions are eta_f(r) times n, where
   eta_f is f_* alpha_f after the abelian unit (def-sfb-finite-lower-star,
   def-sfb-finite-lower-star-lax-monoidal, def-sfb-module-lower-star,
   sk-def-sfb-coefficient-morphisms). Thus lowerComparison is the identity on sections.
3. Conjugate the specified internal adjunction by E, and use the unique unit-normalized
   left-adjoint comparison (lem-weil-pbc-conjugate-iso-unit-equation), with the sectionwise
   adjunction of lem-weil-pbc-ringed-topoi-module-adjunction.
4. Naturality of the Hom bijections gives the mate equation, hence the displayed unit
   and counit equations (lem-weil-pbc-adjunction-of-natural-bijection).
5. Repeat for the given internal open-extension adjunction
   (sk-def-sfb-module-lower-shriek) and the sectionwise extension-by-zero adjunction.
6. The direct-image comparisons commute with composition because their section maps
   are identities, and both compositions rebracket the same fibre product. Conjugation
   is injective, so the pullback comparisons commute with composition too
   (def-sfb-module-lower-star-comp, def-sfb-module-upper-star-comp,
   def-weil-pbc-adjunction-conjugate).
7. The open-extension map is the inverse mate of pullback composition: insert eta_j,
   apply the square comparison, then contract epsilon_j'. Steps 4--6 identify each
   factor, yielding the displayed transformation equation (def-weil-pbc-adjunction-mate).
8. The additive equivalences and their inverses preserve finite limits and colimits
   (lem-galois-equivalence-preserves-limits, def-weil-sheaf-of-modules-category).
   They therefore preserve and reflect exact sequences and exactness of operations.
   The transformation equation conjugates base change by isomorphisms; equivalences
   reflect isomorphisms, so sectionwise invertibility implies internal invertibility.
-/
theorem internal_module_operations_transport :
    (∀ (T : Scheme.{u}),
      (equivalence Λ T).functor.Additive ∧ (equivalence Λ T).inverse.Additive ∧
      PreservesFiniteLimits (equivalence Λ T).functor ∧
      PreservesFiniteColimits (equivalence Λ T).functor ∧
      PreservesFiniteLimits (equivalence Λ T).inverse ∧
      PreservesFiniteColimits (equivalence Λ T).inverse ∧
      (∀ (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj Λ T))),
        (S.map (equivalence Λ T).functor).Exact ↔ S.Exact) ∧
      (∀ (S : ShortComplex (SheafOfModules.{u + 1} (ring Λ T))),
        (S.map (equivalence Λ T).inverse).Exact ↔ S.Exact)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (mateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
          (.mk _ _ _ _ (upperComparison Λ f).inv)).natTrans = (lowerComparison Λ f).hom ∧
      (∀ M,
        (equivalence Λ Y).functor.map
            ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M) ≫
          (lowerComparison Λ f).hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
          (lowerStar Λ f).map ((upperComparison Λ f).hom.app M) =
        (adjunction Λ f).unit.app ((equivalence Λ Y).functor.obj M)) ∧
      (∀ N,
        (upperStar Λ f).map ((lowerComparison Λ f).inv.app N) ≫
          (upperComparison Λ f).inv.app ((CondensedRing.lowerStar Λ f).obj N) ≫
          (equivalence Λ X).functor.map
            ((CondensedRing.upperStarLowerStarAdjunction Λ f).counit.app N) =
        (adjunction Λ f).counit.app ((equivalence Λ X).functor.obj N))) ∧
    (∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j],
      (mateEquiv (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
        (openAdjunction Λ j) (.mk _ _ _ _ (openComparison Λ j).inv)).natTrans =
        (upperComparison Λ j).hom ∧
      (∀ M,
        (equivalence Λ U).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M) ≫
          (upperComparison Λ j).hom.app ((CondensedRing.openImmersionLowerShriek Λ j).obj M) ≫
          (upperStar Λ j).map ((openComparison Λ j).hom.app M) =
        (openAdjunction Λ j).unit.app ((equivalence Λ U).functor.obj M)) ∧
      (∀ N,
        (extension Λ j).map ((upperComparison Λ j).inv.app N) ≫
          (openComparison Λ j).inv.app ((CondensedRing.upperStar Λ j).obj N) ≫
          (equivalence Λ T).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app N) =
        (openAdjunction Λ j).counit.app ((equivalence Λ T).functor.obj N))) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (PreservesFiniteLimits (CondensedRing.upperStar Λ f) ↔
        PreservesFiniteLimits (upperStar Λ f)) ∧
      (PreservesFiniteColimits (CondensedRing.upperStar Λ f) ↔
        PreservesFiniteColimits (upperStar Λ f)) ∧
      (PreservesFiniteLimits (CondensedRing.lowerStar Λ f) ↔
        PreservesFiniteLimits (lowerStar Λ f)) ∧
      (PreservesFiniteColimits (CondensedRing.lowerStar Λ f) ↔
        PreservesFiniteColimits (lowerStar Λ f))) ∧
    (∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j],
      (PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ j) ↔
        PreservesFiniteLimits (extension Λ j)) ∧
      (PreservesFiniteColimits (CondensedRing.openImmersionLowerShriek Λ j) ↔
        PreservesFiniteColimits (extension Λ j))) ∧
    (∀ {U' U T' T : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ T'}
      {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
      (sq : ChosenCartesianSquare g' j' j g),
      Functor.whiskerRight (internalBaseChange Λ sq) (equivalence Λ T').functor ≫
          (baseChangeTargetComparison Λ j g).hom =
        (baseChangeSourceComparison Λ g' j').hom ≫
          Functor.whiskerLeft (equivalence Λ U).functor (sectionBaseChange Λ sq) ∧
      (IsIso (sectionBaseChange Λ sq) → IsIso (internalBaseChange Λ sq))) := by
  sorry

end InternalModuleOperations
end AlgebraicGeometry.ProEtale
