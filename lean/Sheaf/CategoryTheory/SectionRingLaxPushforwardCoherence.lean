/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Coherent reconstruction of lax module direct images

Source: Stacks Project, Tag 03D6, definition-pushforward, and the internal-module
refinement in Steps 1–9 of the DAG proof. The generalized coefficient restriction
uses the localized tensor and actual counit transport, with independent site universes
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
universe u uC vC uD vD uH vH uA vA
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct
attribute [instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace CategoryTheory.Sheaf

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type uA} [Category.{vA} A] [MonoidalCategory A] [BraidedCategory A]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal]

/-- Restriction on coefficient sheaves, without a continuity assumption on set sheaves.
Source: blueprint pushforward-composition proof, second sentence
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
def coefficientRestriction (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj)) :
    Sheaf K A ⥤ Sheaf J A :=
  ObjectProperty.lift _
    (sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj F.op) hF

/-- The actual sheafification counit identifies sheafified restriction with restriction.
Source: blueprint pushforward-composition proof, second sentence
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def coefficientRestrictionCounitIso (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj)) :
    sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj F.op ⋙
      presheafToSheaf J A ≅ coefficientRestriction F hF :=
  Functor.isoWhiskerLeft (coefficientRestriction F hF)
      (asIso (sheafificationAdjunction J A).counit) ≪≫
    (coefficientRestriction F hF).rightUnitor

/-- The lax restriction structure transported along the actual counit from inclusion,
pointwise restriction and strong monoidal sheafification. Source: blueprint
pushforward-composition proof, second sentence
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable instance coefficientRestrictionLaxMonoidal (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj)) :
    (coefficientRestriction F hF).LaxMonoidal :=
  Functor.LaxMonoidal.transport (coefficientRestrictionCounitIso F hF)

private noncomputable def restrictionUnderlyingIso (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj)) :
    sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj F.op ≅
      coefficientRestriction F hF ⋙ sheafToPresheaf J A := by
  have : IsIso (Functor.whiskerLeft
      (sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj F.op)
      (sheafificationAdjunction J A).unit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun M ↦ isIso_toSheafify J (hF M)
  exact (sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj F.op).rightUnitor.symm ≪≫
    asIso (Functor.whiskerLeft _ (sheafificationAdjunction J A).unit) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    Functor.isoWhiskerRight (coefficientRestrictionCounitIso F hF) _

private instance restrictionUnderlyingIso_monoidal (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj)) :
    NatTrans.IsMonoidal (restrictionUnderlyingIso F hF).hom := by
  have := Functor.LaxMonoidal.natTransIsMonoidal_of_transport
    (coefficientRestrictionCounitIso F hF)
  dsimp only [restrictionUnderlyingIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, Functor.isoWhiskerRight_hom]
  infer_instance

private theorem restrictionUnderlyingIso_hom_app (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj)) (M : Sheaf K A) :
    (restrictionUnderlyingIso F hF).hom.app M = 𝟙 _ := by
  simp [restrictionUnderlyingIso, coefficientRestrictionCounitIso]
  rfl

/-- Generator normalization and uniqueness for independently sized sites, in the
localized tensor convention. Source: blueprint pushforward-composition proof,
second sentence (blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. The inclusion tensorator is the adjunction mate of the inverse strong
sheafification tensorator followed by the two counits. The triangle identities
identify it with the actual unit transported to the localized tensor. Expanding
counit transport on restriction cancels the inverse counits with these units,
leaving the restricted inclusion tensorator. The unit calculation is identical.
The sheafification Hom bijections make precomposition with these two generators
injective, so both extensions are unique. This is the same calculation as
`generatorRestriction_comparison`, without identifying site and coefficient
universes or replacing the localized tensor by a retensored copy. -/
theorem coefficientRestriction_comparison
    [Abelian A] [IsGrothendieckAbelian.{vA} A] [MonoidalClosed A]
    [UnivLE.{max uC vC, vA}] [UnivLE.{max uD vD, vA}]
    (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj)) :
    (∀ M N : Sheaf K A,
      Functor.LaxMonoidal.μ (sheafToPresheaf J A)
          ((coefficientRestriction F hF).obj M) ((coefficientRestriction F hF).obj N) ≫
        (Functor.LaxMonoidal.μ (coefficientRestriction F hF) M N).hom =
          Functor.whiskerLeft F.op (Functor.LaxMonoidal.μ (sheafToPresheaf K A) M N) ∧
      ∀ f g : (coefficientRestriction F hF).obj M ⊗
          (coefficientRestriction F hF).obj N ⟶ (coefficientRestriction F hF).obj (M ⊗ N),
        Functor.LaxMonoidal.μ (sheafToPresheaf J A) _ _ ≫ f.hom =
          Functor.LaxMonoidal.μ (sheafToPresheaf J A) _ _ ≫ g.hom → f = g) ∧
    (Functor.LaxMonoidal.ε (sheafToPresheaf J A) ≫
        (Functor.LaxMonoidal.ε (coefficientRestriction F hF)).hom =
          Functor.whiskerLeft F.op (Functor.LaxMonoidal.ε (sheafToPresheaf K A)) ∧
      ∀ f g : 𝟙_ (Sheaf J A) ⟶ (coefficientRestriction F hF).obj (𝟙_ (Sheaf K A)),
        Functor.LaxMonoidal.ε (sheafToPresheaf J A) ≫ f.hom =
          Functor.LaxMonoidal.ε (sheafToPresheaf J A) ≫ g.hom → f = g) := by
  refine ⟨fun M N ↦ ⟨?_, fun f g h ↦ tensor_hom_ext h⟩,
    ?_, fun f g h ↦ unit_hom_ext h⟩
  · have h := NatTrans.IsMonoidal.tensor (τ := (restrictionUnderlyingIso F hF).hom) M N
    have hr : Functor.LaxMonoidal.μ ((Functor.whiskeringLeft _ _ A).obj F.op)
        M.obj N.obj = 𝟙 _ := rfl
    simpa [restrictionUnderlyingIso_hom_app, Functor.LaxMonoidal.comp_μ, hr] using h.symm
  · have h := NatTrans.IsMonoidal.unit (τ := (restrictionUnderlyingIso F hF).hom)
    have hr : Functor.LaxMonoidal.ε ((Functor.whiskeringLeft _ _ A).obj F.op) = 𝟙 _ := rfl
    simpa [restrictionUnderlyingIso_hom_app, Functor.LaxMonoidal.comp_ε, hr] using h.symm

private noncomputable def restrictionMonoidIso (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj))
    (S : Mon (Sheaf K A)) :
    (sheafToPresheaf J A).mapMon.obj ((coefficientRestriction F hF).mapMon.obj S) ≅
      ((Functor.whiskeringLeft _ _ A).obj F.op).mapMon.obj
        ((sheafToPresheaf K A).mapMon.obj S) :=
  (Functor.mapMonCompIso (F := coefficientRestriction F hF)
      (G := sheafToPresheaf J A)).symm.app S ≪≫
    (Functor.mapMonNatIso (restrictionUnderlyingIso F hF)).symm.app S ≪≫
    (Functor.mapMonCompIso (F := sheafToPresheaf K A)
      (G := (Functor.whiskeringLeft _ _ A).obj F.op)).app S

private theorem restrictionMonoidIso_hom (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj))
    (S : Mon (Sheaf K A)) : (restrictionMonoidIso F hF S).hom.hom = 𝟙 _ := by
  have h := (restrictionUnderlyingIso F hF).inv_hom_id_app S.X
  erw [restrictionUnderlyingIso_hom_app, Category.comp_id] at h
  change 𝟙 _ ≫ (restrictionUnderlyingIso F hF).inv.app S.X ≫ 𝟙 _ = 𝟙 _
  erw [h, Category.id_comp, Category.id_comp]
  rfl

private theorem restrictionMonoidIso_inv (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj))
    (S : Mon (Sheaf K A)) : (restrictionMonoidIso F hF S).inv.hom = 𝟙 _ := by
  have h := congrArg (fun f ↦ f.hom) (restrictionMonoidIso F hF S).inv_hom_id
  change (restrictionMonoidIso F hF S).inv.hom ≫
    (restrictionMonoidIso F hF S).hom.hom = 𝟙 _ at h
  erw [restrictionMonoidIso_hom, Category.comp_id] at h
  exact h

end CategoryTheory.Sheaf

namespace CategoryTheory.InternalAbelianSheafModule

/-- Sectionwise direct image for a ring-presheaf map whose underlying abelian
restriction preserves sheaves. The source and target ring presheaves are sheaves.
Source: Stacks Tag 03D6, DAG proof Step 4
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def coefficientModulePushforward
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D)
    (hF : ∀ M : Sheaf K AddCommGrpCat.{u}, Presheaf.IsSheaf J (F.op ⋙ M.obj))
    {BC : Sheaf J RingCat.{u}} {BD : Sheaf K RingCat.{u}}
    (φ : BC.obj ⟶ F.op ⋙ BD.obj) : SheafOfModules.{u} BD ⥤ SheafOfModules.{u} BC where
  obj M :=
    { val := (PresheafOfModules.pushforward φ).obj M.val
      isSheaf := hF ((SheafOfModules.toSheaf _).obj M) }
  map f := ⟨(PresheafOfModules.pushforward φ).map f.val⟩

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal]
  (F : C ⥤ D)
  (hF : ∀ M : Sheaf K AddCommGrpCat.{u}, Presheaf.IsSheaf J (F.op ⋙ M.obj))
  (RC : Sheaf J AddCommGrpCat.{u}) (RD : Sheaf K AddCommGrpCat.{u})
  [MonObj RC] [IsCommMonObj RC] [MonObj RD] [IsCommMonObj RD]
  (ψ : RC ⟶ (Sheaf.coefficientRestriction F hF).obj RD) [IsMonHom ψ]

include hF in
/-- The sectionwise direct image of the reconstructed ring presheaf is a sheaf.
Source: Stacks Tag 03D6, DAG proof Step 1
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Forget the reconstructed ring to its abelian presheaf. This is exactly
F.op composed with RD.obj, a sheaf by hF. The forgetful functor reflects the sheaf
condition for algebraic structures, so the ring presheaf is a sheaf. -/
theorem laxSectionRingImage_isSheaf :
    Presheaf.IsSheaf J (F.op ⋙ sectionRings.{u, uD, vD} K RD) := by
  let : PreservesLimitsOfSize.{vC, max uC vC}
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
    preservesLimitsOfSize_of_univLE.{max uC vC, max uC vC} _
  apply (Presheaf.isSheaf_iff_isSheaf_comp J _
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})).2
  exact hF RD

/-- The direct image ring sheaf has exactly the section rings B_D(FV).
Source: Stacks Tag 03D6, DAG proof Step 1
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def laxSectionRingImage : Sheaf J CommRingCat.{u} :=
  ⟨F.op ⋙ sectionRings.{u, uD, vD} K RD, laxSectionRingImage_isSheaf F hF RD⟩

/-- The ring map is uniquely determined by the given additive section maps.
Source: Stacks Tag 03D6; DAG proof Steps 1–2
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Precompose the transported multiplication and unit with the actual tensor
and unit generators. The generator comparison gives the original products and
units on RD(FV). The monoid-map laws for ψ therefore say its additive components
preserve products and one. Naturality gives a ring-presheaf map, hence a map of
ring sheaves. Equality of the additive components proves uniqueness. -/
theorem laxSectionRingMap_existsUnique :
    ∃! φ : sectionRings.{u, uC, vC} J RC ⟶ F.op ⋙ sectionRings.{u, uD, vD} K RD,
      ∀ U : Cᵒᵖ, (φ.app U).hom.toAddMonoidHom = (ψ.hom.app U).hom := by
  let P := Sheaf.coefficientRestriction F hF
  let UC := sheafToPresheaf J AddCommGrpCat.{u}
  let UD := sheafToPresheaf K AddCommGrpCat.{u}
  let r := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj F.op
  let e := Sheaf.restrictionUnderlyingIso F hF
  let c : (UC.mapMon.obj (P.mapMon.obj (Mon.mk RD))) ≅
      r.mapMon.obj (UD.mapMon.obj (Mon.mk RD)) :=
    (Functor.mapMonCompIso (F := P) (G := UC)).symm.app (Mon.mk RD) ≪≫
      (Functor.mapMonNatIso e).symm.app (Mon.mk RD) ≪≫
      (Functor.mapMonCompIso (F := UD) (G := r)).app (Mon.mk RD)
  let f : UC.mapMon.obj (Mon.mk RC) ⟶ r.mapMon.obj (UD.mapMon.obj (Mon.mk RD)) :=
    UC.mapMon.map (Mon.Hom.mk ψ) ≫ c.hom
  have hf : f.hom = ψ.hom := by
    change ψ.hom ≫ (e.inv.app RD) = ψ.hom
    have heh : e.hom.app RD = 𝟙 (F.op ⋙ RD.obj) :=
      Sheaf.restrictionUnderlyingIso_hom_app F hF RD
    have he := e.inv_hom_id_app RD
    erw [heh, Category.comp_id] at he
    erw [he, Category.comp_id]
  let q := (Monoidal.monFunctorCategoryEquivalence Cᵒᵖ AddCommGrpCat.{u}).functor.map f
  let φ : sectionRings J RC ⟶ F.op ⋙ sectionRings K RD :=
    { app := fun U ↦ by
        let g : (sectionRings J RC).obj U →+*
            (sectionRings K RD).obj (F.op.obj U) := ringHom (q.app U).hom
        exact ConcreteCategory.ofHom (C := CommRingCat) g
      naturality := fun U V g ↦ by
        ext x
        exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  have hφ (U : Cᵒᵖ) : (φ.app U).hom.toAddMonoidHom = (ψ.hom.app U).hom :=
    congrArg (fun z ↦ (z.app U).hom) hf
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  ext U x
  exact congrArg (fun z ↦ z x) ((hφ' U).trans (hφ U).symm)

/-- The unique reconstructed coefficient map, selected from its uniqueness theorem.
Source: Stacks Tag 03D6, DAG proof Step 2
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def laxSectionRingMap :
    sectionRings.{u, uC, vC} J RC ⟶ F.op ⋙ sectionRings.{u, uD, vD} K RD :=
  Classical.choose (laxSectionRingMap_existsUnique F hF RC RD ψ).exists

private theorem laxSectionRingMap_additive (U : Cᵒᵖ) :
    ((laxSectionRingMap F hF RC RD ψ).app U).hom.toAddMonoidHom =
      (ψ.hom.app U).hom :=
  Classical.choose_spec (laxSectionRingMap_existsUnique F hF RC RD ψ).exists U

/-- The same unique reconstructed coefficient map, bundled as a map of ring sheaves.
Source: Stacks Tag 03D6, DAG proof Step 2
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def laxSectionRingSheafMap :
    sectionRingSheaf.{u, uC, vC} J RC ⟶ laxSectionRingImage.{u, uC, vC, uD, vD} F hF RD :=
  ⟨laxSectionRingMap F hF RC RD ψ⟩

/-- Direct image of internal modules is mapMod followed by restriction of scalars.
Source: Stacks Tag 03D6, DAG proof Step 3
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def laxInternalPushforward :
    Mod (Sheaf K AddCommGrpCat.{u}) RD ⥤ Mod (Sheaf J AddCommGrpCat.{u}) RC :=
  (Sheaf.coefficientRestriction F hF).mapMod RD ⋙ Mod.comap ψ

/-- Sectionwise direct image using only preservation of abelian sheaves.
Source: Stacks Tag 03D6, DAG proof Step 4
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def laxSectionPushforward :
    SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf.{u, uD, vD} K RD)) ⥤
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf.{u, uC, vC} J RC)) :=
  coefficientModulePushforward F hF
    (Functor.whiskerRight (laxSectionRingMap F hF RC RD ψ)
      (forget₂ CommRingCat RingCat))

omit [UnivLE.{max uD vD, u}] in
private theorem reconstructed_smul
    (M : Mod (Sheaf J AddCommGrpCat.{u}) RC) (U : Cᵒᵖ)
    (r : (sectionRings J RC).obj U) (x : M.X.obj.obj U) :
    r • (@id (((sectionModuleEquivalence J RC).functor.obj M).val.obj U) x) =
      (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) RC M.X) ≫
        (Mod.act M.X).hom).app U).hom (r ⊗ₜ[ℤ] x) := by
  rfl

/-- The reconstructed pushed action is multiplication by ψ_V(r) on sections.
Source: Stacks Tag 03D6, DAG proof Step 3
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Precompose the internal action with the tensor generator. Naturality moves
ψ to the sectionwise tensor. Generator normalization for F then replaces its lax
tensorator by the restricted generator on D. The resulting action is ψ_V(r)n. -/
theorem laxInternalPushforward_sectionAction
    (M : Mod (Sheaf K AddCommGrpCat.{u}) RD) (U : Cᵒᵖ)
    (r : (sectionRings.{u, uC, vC} J RC).obj U) (x : M.X.obj.obj (F.op.obj U)) :
    r • (@id (((sectionModuleEquivalence.{u, uC, vC} J RC).functor.obj
        ((laxInternalPushforward F hF RC RD ψ).obj M)).val.obj U) x) =
      ((ψ.hom.app U).hom r : (sectionRings.{u, uD, vD} K RD).obj (F.op.obj U)) •
        (@id (((sectionModuleEquivalence.{u, uD, vD} K RD).functor.obj M).val.obj
          (F.op.obj U)) x) := by
  let P := Sheaf.coefficientRestriction F hF
  let UC := sheafToPresheaf J AddCommGrpCat.{u}
  let UD := sheafToPresheaf K AddCommGrpCat.{u}
  have h : Functor.LaxMonoidal.μ UC RC (P.obj M.X) ≫
      (ψ ▷ P.obj M.X ≫ Functor.LaxMonoidal.μ P RD M.X ≫ P.map (Mod.act M.X)).hom =
        (ψ.hom ▷ (P.obj M.X).obj) ≫
          Functor.whiskerLeft F.op (Functor.LaxMonoidal.μ UD RD M.X) ≫
            Functor.whiskerLeft F.op (Mod.act M.X).hom := by
    simp only [ObjectProperty.FullSubcategory.comp_hom]
    erw [← Functor.LaxMonoidal.μ_natural_left_assoc]
    rw [reassoc_of% ((Sheaf.coefficientRestriction_comparison F hF).1 RD M.X).1]
    rfl
  refine (reconstructed_smul.{u, uC, vC} RC
    ((laxInternalPushforward F hF RC RD ψ).obj M) U r x).trans ?_
  refine Eq.trans ?_ (reconstructed_smul.{u, uD, vD} RD M (F.op.obj U)
    ((ψ.hom.app U).hom r) x).symm
  dsimp only [laxInternalPushforward, Functor.comp_obj]
  erw [Mod.act_comap_obj, Functor.act_mapMod_obj]
  dsimp only [Mod.comap, Functor.mapMod]
  have he := congrArg (fun z ↦ z.hom (r ⊗ₜ[ℤ] x)) (congr_app h U)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.comp_apply] at he ⊢
  erw [Monoidal.whiskerRight_app,
    AddCommGrpCat.MonoidalCategory.whiskerRight_tmul] at he
  exact he

/-- The comparison is the unique natural isomorphism with identity section maps.
Source: Stacks Tag 03D6, DAG proof Steps 3–4
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. On a tensor generator the internal pushed action is ψ_V(r)n, by naturality
and the generator normalization. This is exactly the sectionwise action. Identity
section maps are therefore linear in both directions and natural in the module.
Their composites are identities; a comparison with these section maps is unique. -/
theorem laxSectionComparison_existsUnique :
    ∃! r : laxInternalPushforward F hF RC RD ψ ⋙
        (sectionModuleEquivalence.{u, uC, vC} J RC).functor ≅
        (sectionModuleEquivalence.{u, uD, vD} K RD).functor ⋙ laxSectionPushforward F hF RC RD ψ,
      ∀ (M : Mod (Sheaf K AddCommGrpCat.{u}) RD) (U : Cᵒᵖ)
        (x : M.X.obj.obj (F.op.obj U)), ((r.hom.app M).val.app U).hom x = x := by
  have hs (M : Mod (Sheaf K AddCommGrpCat.{u}) RD) (U : Cᵒᵖ)
      (r : (sectionRings J RC).obj U) (x : M.X.obj.obj (F.op.obj U)) :
      r • (@id (((sectionModuleEquivalence J RC).functor.obj
          ((laxInternalPushforward F hF RC RD ψ).obj M)).val.obj U) x) =
        r • (@id ((((sectionModuleEquivalence K RD).functor ⋙
          laxSectionPushforward F hF RC RD ψ).obj M).val.obj U) x) := by
    have e := congrArg (fun z ↦ z r) (laxSectionRingMap_additive F hF RC RD ψ U)
    change ((laxSectionRingMap F hF RC RD ψ).app U).hom r =
      (ψ.hom.app U).hom r at e
    change _ = ((laxSectionRingMap F hF RC RD ψ).app U).hom r •
      (@id (((sectionModuleEquivalence K RD).functor.obj M).val.obj (F.op.obj U)) x)
    rw [e]
    exact laxInternalPushforward_sectionAction F hF RC RD ψ M U r x
  let e (M : Mod (Sheaf K AddCommGrpCat.{u}) RD) :
      ((laxInternalPushforward F hF RC RD ψ ⋙
        (sectionModuleEquivalence J RC).functor).obj M) ≅
      (((sectionModuleEquivalence K RD).functor ⋙
        laxSectionPushforward F hF RC RD ψ).obj M) :=
    { hom := ⟨PresheafOfModules.homMk (𝟙 _) (hs M)⟩
      inv := ⟨PresheafOfModules.homMk (𝟙 _) (fun U r x ↦ (hs M U r x).symm)⟩
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }
  let z := NatIso.ofComponents e (fun f ↦ by ext U x; rfl)
  refine ⟨z, fun M U x ↦ rfl, ?_⟩
  intro z' hz'
  apply Iso.ext
  ext M U x
  exact hz' M U x

/-- The uniquely normalized internal/sectionwise direct-image comparison.
Source: Stacks Tag 03D6, DAG proof Steps 3–4
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def laxSectionComparison :
    laxInternalPushforward F hF RC RD ψ ⋙ (sectionModuleEquivalence.{u, uC, vC} J RC).functor ≅
      (sectionModuleEquivalence.{u, uD, vD} K RD).functor ⋙ laxSectionPushforward F hF RC RD ψ :=
  Classical.choose (laxSectionComparison_existsUnique F hF RC RD ψ).exists

private theorem laxSectionComparison_apply
    (M : Mod (Sheaf K AddCommGrpCat.{u}) RD) (U : Cᵒᵖ)
    (x : M.X.obj.obj (F.op.obj U)) :
    (((laxSectionComparison F hF RC RD ψ).hom.app M).val.app U).hom x = x :=
  Classical.choose_spec (laxSectionComparison_existsUnique F hF RC RD ψ).exists M U x

private theorem restrictionMonoid_one
    (S : Sheaf K AddCommGrpCat.{u}) [MonObj S] :
    Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u}) ≫
        (MonObj.one (X := (Sheaf.coefficientRestriction F hF).obj S)).hom =
      Functor.whiskerLeft F.op
        (Functor.LaxMonoidal.ε (sheafToPresheaf K AddCommGrpCat.{u}) ≫
          (MonObj.one (X := S)).hom) := by
  change Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u}) ≫
    (Functor.LaxMonoidal.ε (Sheaf.coefficientRestriction F hF) ≫
      (Sheaf.coefficientRestriction F hF).map (MonObj.one (X := S))).hom = _
  rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
    (Sheaf.coefficientRestriction_comparison F hF).2.1]
  rfl

private theorem restrictionMonoid_mul
    (S : Sheaf K AddCommGrpCat.{u}) [MonObj S] :
    Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u})
        ((Sheaf.coefficientRestriction F hF).obj S)
        ((Sheaf.coefficientRestriction F hF).obj S) ≫
        (MonObj.mul (X := (Sheaf.coefficientRestriction F hF).obj S)).hom =
      Functor.whiskerLeft F.op
        (Functor.LaxMonoidal.μ (sheafToPresheaf K AddCommGrpCat.{u}) S S ≫
          (MonObj.mul (X := S)).hom) := by
  change Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) _ _ ≫
    (Functor.LaxMonoidal.μ (Sheaf.coefficientRestriction F hF) S S ≫
      (Sheaf.coefficientRestriction F hF).map (MonObj.mul (X := S))).hom = _
  rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
    ((Sheaf.coefficientRestriction_comparison F hF).1 S S).1]
  rfl

section Composition

variable {H : Type uH} [Category.{vH} H] {L : GrothendieckTopology H}
  [UnivLE.{max uH vH, u}] [HasSheafify L AddCommGrpCat.{u}]
  [(L.W (A := AddCommGrpCat.{u})).IsMonoidal]
  (G : D ⥤ H)
  (hG : ∀ M : Sheaf L AddCommGrpCat.{u}, Presheaf.IsSheaf K (G.op ⋙ M.obj))
  (T : C ⥤ H)
  (hT : ∀ M : Sheaf L AddCommGrpCat.{u}, Presheaf.IsSheaf J (T.op ⋙ M.obj))
  (κ : T ≅ F ⋙ G)

/-- The compositor on an underlying sheaf is restriction along κ, contravariantly.
Source: DAG proof Step 5, general-site compositor calculation
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
def laxRestrictionCompositor (M : Sheaf L AddCommGrpCat.{u}) :
    (Sheaf.coefficientRestriction F hF).obj
        ((Sheaf.coefficientRestriction G hG).obj M) ≅
      (Sheaf.coefficientRestriction T hT).obj M :=
  ObjectProperty.isoMk _ (Functor.isoWhiskerRight (NatIso.op κ) M.obj)

private def presheafRestrictionCompositor :
    ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj G.op ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj F.op) ≅
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj T.op :=
  NatIso.ofComponents (fun M ↦ Functor.isoWhiskerRight (NatIso.op κ) M) (by
    intro M N f
    ext U x
    exact ConcreteCategory.congr_hom (f.naturality (κ.hom.app U.unop).op).symm x)

private instance presheafRestrictionCompositor_monoidal :
    NatTrans.IsMonoidal (presheafRestrictionCompositor F G T κ).hom := by
  constructor
  · ext U x
    rfl
  · intro M N
    ext U x
    rfl

/-- The actual compositor respects the transported monoid structures.
Source: DAG proof Step 5
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. The presheaf compositor is pointwise monoidal. Lift it with mapMon and
identify the twice-restricted and singly-restricted monoids using the monoidal
underlying-restriction isomorphisms. Those isomorphisms have identity components,
so the resulting monoid map has exactly the prescribed κ components. The faithful
inclusion of sheaves reflects its monoid-map equations. -/
@[instance] theorem laxRestrictionCompositor_isMonHom
    (RH : Sheaf L AddCommGrpCat.{u}) [MonObj RH] :
    IsMonHom (laxRestrictionCompositor F hF G hG T hT κ RH).hom := by
  let PF := Sheaf.coefficientRestriction F hF
  let PG := Sheaf.coefficientRestriction G hG
  let PT := Sheaf.coefficientRestriction T hT
  let UC := sheafToPresheaf J AddCommGrpCat.{u}
  let UH := sheafToPresheaf L AddCommGrpCat.{u}
  let rF := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj F.op
  let rG := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj G.op
  let rT := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj T.op
  let S := Mon.mk RH
  let cF := Sheaf.restrictionMonoidIso F hF (PG.mapMon.obj S)
  let cG := Sheaf.restrictionMonoidIso G hG S
  let cT := Sheaf.restrictionMonoidIso T hT S
  let f : UC.mapMon.obj (PF.mapMon.obj (PG.mapMon.obj S)) ⟶
      UC.mapMon.obj (PT.mapMon.obj S) :=
    cF.hom ≫ rF.mapMon.map cG.hom ≫
      (Functor.mapMonCompIso (F := rG) (G := rF)).inv.app (UH.mapMon.obj S) ≫
      (Functor.mapMonNatIso (presheafRestrictionCompositor F G T κ)).hom.app
        (UH.mapMon.obj S) ≫ cT.inv
  have hf : f.hom = UC.map (laxRestrictionCompositor F hF G hG T hT κ RH).hom := by
    change cF.hom.hom ≫ rF.map cG.hom.hom ≫ 𝟙 _ ≫
      (presheafRestrictionCompositor F G T κ).hom.app RH.obj ≫ cT.inv.hom = _
    erw [Sheaf.restrictionMonoidIso_hom, Sheaf.restrictionMonoidIso_hom,
      Sheaf.restrictionMonoidIso_inv, Functor.map_id]
    ext U x
    rfl
  have : IsMonHom f.hom := inferInstance
  have : IsMonHom (UC.map (laxRestrictionCompositor F hF G hG T hT κ RH).hom) := by
    erw [hf] at this
    exact this
  exact Sheaf.isMonHom_of_isMonHom_map (laxRestrictionCompositor F hF G hG T hT κ RH).hom

variable (RH : Sheaf L AddCommGrpCat.{u}) [MonObj RH] [IsCommMonObj RH]
  (θ : RD ⟶ (Sheaf.coefficientRestriction G hG).obj RH) [IsMonHom θ]

/-- The coefficient map of the composite, with the actual κ component.
Source: DAG proof Step 5
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
def laxCompositeCoefficient : RC ⟶ (Sheaf.coefficientRestriction T hT).obj RH :=
  ψ ≫ (Sheaf.coefficientRestriction F hF).map θ ≫
    (laxRestrictionCompositor F hF G hG T hT κ RH).hom

/-- The composite coefficient is a monoid morphism.
Source: DAG proof Step 5
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. ψ and θ are monoid morphisms; lax monoidal transport preserves the latter
property. The compositor is a monoid morphism by the generator calculation.
Compose these three monoid morphisms. -/
@[instance] theorem laxCompositeCoefficient_isMonHom :
    IsMonHom (laxCompositeCoefficient F hF RC RD ψ G hG T hT κ RH θ) := by
  dsimp only [laxCompositeCoefficient]
  infer_instance

/-- Reconstructed ring maps and normalized module comparisons commute with arbitrary
specified compositors, including the literal composite.
Source: Stacks Tag 03D6, DAG proof Steps 5–7
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Step 5 gives the monoid compositor. On sections the composite ring map has
additive map RH(κ_V) θ_FV ψ_V; uniqueness of reconstruction proves the ring equality.
For a module N, semilinear naturality along κ_V identifies its two actions, so
N(κ_V) and its inverse give linear compositors on both sides. Full faithfulness of
reconstruction also lifts the sectionwise compositor internally. Every path in
the comparison square sends n to N(κ_V)(n), proving the asserted square. -/
theorem laxSectionPushforward_composition :
    laxSectionRingMap T hT RC RH
        (laxCompositeCoefficient F hF RC RD ψ G hG T hT κ RH θ) =
      laxSectionRingMap F hF RC RD ψ ≫
        Functor.whiskerLeft F.op (laxSectionRingMap G hG RD RH θ) ≫
          Functor.whiskerRight (NatTrans.op κ.hom) (sectionRings.{u, uH, vH} L RH) ∧
    ∃ i : laxInternalPushforward G hG RD RH θ ⋙
        laxInternalPushforward F hF RC RD ψ ≅
        laxInternalPushforward T hT RC RH
          (laxCompositeCoefficient F hF RC RD ψ G hG T hT κ RH θ),
    ∃ s : laxSectionPushforward G hG RD RH θ ⋙
        laxSectionPushforward F hF RC RD ψ ≅
        laxSectionPushforward T hT RC RH
          (laxCompositeCoefficient F hF RC RD ψ G hG T hT κ RH θ),
      (∀ (M : Mod (Sheaf L AddCommGrpCat.{u}) RH) (U : Cᵒᵖ),
        (i.hom.app M).hom.hom.app U = M.X.obj.map (κ.hom.app U.unop).op) ∧
      (∀ (M : SheafOfModules.{u}
          ((sheafCompose L (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf.{u, uH, vH} L RH)))
          (U : Cᵒᵖ),
        ((s.hom.app M).val.app U).hom.toAddMonoidHom =
          (M.val.presheaf.map (κ.hom.app U.unop).op).hom) ∧
      (∀ M : Mod (Sheaf L AddCommGrpCat.{u}) RH,
        (sectionModuleEquivalence.{u, uC, vC} J RC).functor.map (i.hom.app M) ≫
          (laxSectionComparison T hT RC RH
            (laxCompositeCoefficient F hF RC RD ψ G hG T hT κ RH θ)).hom.app M =
        (laxSectionComparison F hF RC RD ψ).hom.app
            ((laxInternalPushforward G hG RD RH θ).obj M) ≫
          (laxSectionPushforward F hF RC RD ψ).map
            ((laxSectionComparison G hG RD RH θ).hom.app M) ≫
          s.hom.app ((sectionModuleEquivalence.{u, uH, vH} L RH).functor.obj M)) := by
  let χ := laxCompositeCoefficient F hF RC RD ψ G hG T hT κ RH θ
  let φF := laxSectionRingMap F hF RC RD ψ
  let φG := laxSectionRingMap G hG RD RH θ
  let φT := laxSectionRingMap T hT RC RH χ
  have hφ (U : Cᵒᵖ) (r : (sectionRings J RC).obj U) :
      (φT.app U).hom r = (sectionRings L RH).map (κ.hom.app U.unop).op
        ((φG.app (F.op.obj U)).hom ((φF.app U).hom r)) := by
    have hF' := congrArg (fun z ↦ z r) (laxSectionRingMap_additive F hF RC RD ψ U)
    have hG' := congrArg (fun z ↦ z ((φF.app U).hom r))
      (laxSectionRingMap_additive G hG RD RH θ (F.op.obj U))
    have hT' := congrArg (fun z ↦ z r) (laxSectionRingMap_additive T hT RC RH χ U)
    change (φF.app U).hom r = (ψ.hom.app U).hom r at hF'
    change (φG.app (F.op.obj U)).hom ((φF.app U).hom r) =
      (θ.hom.app (F.op.obj U)).hom ((φF.app U).hom r) at hG'
    change (φT.app U).hom r = (RH.obj.map (κ.hom.app U.unop).op).hom
      ((θ.hom.app (F.op.obj U)).hom ((ψ.hom.app U).hom r)) at hT'
    change (φT.app U).hom r = (RH.obj.map (κ.hom.app U.unop).op).hom
      ((φG.app (F.op.obj U)).hom ((φF.app U).hom r))
    rw [hG', hF']
    exact hT'
  have hring : φT = φF ≫ Functor.whiskerLeft F.op φG ≫
      Functor.whiskerRight (NatTrans.op κ.hom) (sectionRings L RH) := by
    ext U r
    exact hφ U r
  let PF := laxSectionPushforward F hF RC RD ψ
  let PG := laxSectionPushforward G hG RD RH θ
  let PT := laxSectionPushforward T hT RC RH χ
  let es (M : SheafOfModules.{u}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf L RH))) :
      (PG ⋙ PF).obj M ≅ PT.obj M := by
    let f : (PG ⋙ PF).obj M ⟶ PT.obj M :=
      ⟨PresheafOfModules.homMk
        (Functor.whiskerRight (NatTrans.op κ.hom) M.val.presheaf) (by
          intro U r x
          change M.val.map (κ.hom.app U.unop).op
              ((φG.app (F.op.obj U)).hom ((φF.app U).hom r) •
                (@id (M.val.obj (G.op.obj (F.op.obj U))) x)) =
            (φT.app U).hom r • M.val.map (κ.hom.app U.unop).op x
          rw [hφ]
          exact M.val.map_smul _ _ _)⟩
    have : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map f) := by
      change IsIso (Functor.whiskerRight (NatTrans.op κ.hom) M.val.presheaf)
      infer_instance
    have : IsIso f := isIso_of_reflects_iso f
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)
    exact asIso f
  let s : PG ⋙ PF ≅ PT := NatIso.ofComponents es (by
    intro M N f
    ext U x
    exact (PresheafOfModules.naturality_apply f.val (κ.hom.app U.unop).op x).symm)
  let IF := laxInternalPushforward F hF RC RD ψ
  let IG := laxInternalPushforward G hG RD RH θ
  let IT := laxInternalPushforward T hT RC RH χ
  let EC := (sectionModuleEquivalence J RC).functor
  let ED := (sectionModuleEquivalence K RD).functor
  let EH := (sectionModuleEquivalence L RH).functor
  let rF := laxSectionComparison F hF RC RD ψ
  let rG := laxSectionComparison G hG RD RH θ
  let rT := laxSectionComparison T hT RC RH χ
  let z : (IG ⋙ IF) ⋙ EC ≅ IT ⋙ EC :=
    Functor.associator IG IF EC ≪≫ Functor.isoWhiskerLeft IG rF ≪≫
      (Functor.associator IG ED PF).symm ≪≫ Functor.isoWhiskerRight rG PF ≪≫
      Functor.associator EH PG PF ≪≫ Functor.isoWhiskerLeft EH s ≪≫ rT.symm
  let i := Functor.fullyFaithfulCancelRight EC z
  have hi (M : Mod (Sheaf L AddCommGrpCat.{u}) RH) :
      EC.map (i.hom.app M) ≫ rT.hom.app M =
        rF.hom.app (IG.obj M) ≫ PF.map (rG.hom.app M) ≫ s.hom.app (EH.obj M) := by
    dsimp only [i, Functor.fullyFaithfulCancelRight_hom_app]
    rw [Functor.map_preimage]
    have h : (z.hom.app M) ≫ rT.hom.app M =
        rF.hom.app (IG.obj M) ≫ PF.map (rG.hom.app M) ≫ s.hom.app (EH.obj M) := by
      ext U x
      simp [z, Functor.comp_obj]
    exact h
  refine ⟨hring, i, s, ?_, fun M U ↦ rfl, hi⟩
  intro M U
  ext x
  have h := congrArg (fun f ↦ ((f.val.app U).hom x)) (hi M)
  change (((laxSectionComparison T hT RC RH χ).hom.app M).val.app U).hom
      (((i.hom.app M).hom.hom.app U).hom x) =
    (M.X.obj.map (κ.hom.app U.unop).op).hom
      ((((laxSectionComparison G hG RD RH θ).hom.app M).val.app (F.op.obj U)).hom
        ((((laxSectionComparison F hF RC RD ψ).hom.app (IG.obj M)).val.app U).hom x)) at h
  simp only [laxSectionComparison_apply] at h
  convert! h using 1

end Composition

omit [UnivLE.{max uD vD, u}]

/-- Reconstruction and its fixed quasi-inverse are additive and exact, and reflect
exact sequences in both directions. This applies separately on every site.
Source: Stacks Tag 03DA, DAG proof Steps 8–9
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Reconstruction preserves the underlying additive maps, hence their sums.
Faithfulness, bilinearity of composition and the equivalence counit imply
additivity of its quasi-inverse. Additive equivalences preserve kernels and
cokernels, and hence exact sequences. Equivalences preserve all finite limits and
colimits. Applying the opposite equivalence and its unit/counit reflects exactness,
since exactness is invariant under isomorphism of short complexes. -/
theorem sectionModuleEquivalence_additive_exact :
    (sectionModuleEquivalence.{u, uC, vC} J RC).functor.Additive ∧
    (sectionModuleEquivalence.{u, uC, vC} J RC).inverse.Additive ∧
    PreservesFiniteLimits (sectionModuleEquivalence.{u, uC, vC} J RC).functor ∧
    PreservesFiniteColimits (sectionModuleEquivalence.{u, uC, vC} J RC).functor ∧
    PreservesFiniteLimits (sectionModuleEquivalence.{u, uC, vC} J RC).inverse ∧
    PreservesFiniteColimits (sectionModuleEquivalence.{u, uC, vC} J RC).inverse ∧
    (∀ S : ShortComplex (Mod (Sheaf J AddCommGrpCat.{u}) RC),
      S.Exact ↔ (S.map (sectionModuleEquivalence.{u, uC, vC} J RC).functor).Exact) ∧
    (∀ S : ShortComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf.{u, uC, vC} J RC))),
      S.Exact ↔ (S.map (sectionModuleEquivalence.{u, uC, vC} J RC).inverse).Exact) := by
  let E := sectionModuleEquivalence J RC
  have : E.functor.Additive :=
    { map_add := by intros; ext U x; rfl }
  have : UnivLE.{uC, u} := UnivLE.trans.{uC, max uC vC, u}
  have : UnivLE.{vC, u} := UnivLE.trans.{vC, max uC vC, u}
  have : EssentiallySmall.{u} C := essentiallySmall_of_small_of_locallySmall C
  have : J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{vC, u, uC, u + 1, u, u, u} J
  let : Abelian (Mod (Sheaf J AddCommGrpCat.{u}) RC) := abelianOfEquivalence E.functor
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_⟩
  · intro S
    exact (S.exact_map_iff_of_faithful E.functor).symm
  · intro S
    exact (S.exact_map_iff_of_faithful E.inverse).symm

/-- The identity coefficient map has identity additive sections, with its actual
transported target monoid. Source: DAG proof Step 7
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
def laxIdentityCoefficient : RC ⟶
    (Sheaf.coefficientRestriction (𝟭 C)
      (fun M : Sheaf J AddCommGrpCat.{u} ↦ M.property)).obj RC :=
  ⟨𝟙 RC.obj⟩

/-- The identity coefficient map respects the normalized lax structure.
Source: DAG proof Steps 5 and 7
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. The generator equations identify the identity restriction multiplication
and unit with those of RC. Its identity additive map respects both. -/
@[instance] theorem laxIdentityCoefficient_isMonHom :
    IsMonHom (laxIdentityCoefficient RC) := by
  have : IsMonHom ((sheafToPresheaf J AddCommGrpCat.{u}).map (laxIdentityCoefficient RC)) := by
    constructor
    · change (Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u}) ≫
          (MonObj.one (X := RC)).hom) ≫ 𝟙 _ =
        Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u}) ≫
          (MonObj.one (X := (Sheaf.coefficientRestriction (𝟭 C)
            (fun M : Sheaf J AddCommGrpCat.{u} ↦ M.property)).obj RC)).hom
      erw [restrictionMonoid_one (𝟭 C) (fun M ↦ M.property) RC]
      ext U x
      rfl
    · change (Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) RC RC ≫
          (MonObj.mul (X := RC)).hom) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫
        (Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) _ _ ≫
          (MonObj.mul (X := (Sheaf.coefficientRestriction (𝟭 C)
            (fun M : Sheaf J AddCommGrpCat.{u} ↦ M.property)).obj RC)).hom)
      erw [restrictionMonoid_mul (𝟭 C) (fun M ↦ M.property) RC]
      erw [id_tensorHom_id]
      ext U x
      rfl
  exact Sheaf.isMonHom_of_isMonHom_map (laxIdentityCoefficient RC)

/-- Identity comparisons agree with the identity internal and sectionwise
compositors. Source: DAG proof Step 7
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Both identity direct images have the original action on every section.
Thus identity maps give the two unit compositors. Reconstruction of the identity
coefficient map is the identity by uniqueness. The comparison followed by the
sectionwise unitor and reconstruction of the internal unitor have identical
section maps, proving agreement. -/
theorem laxSectionPushforward_identity :
    laxSectionRingMap (𝟭 C) (fun M : Sheaf J AddCommGrpCat.{u} ↦ M.property)
      RC RC (laxIdentityCoefficient RC) = 𝟙 (sectionRings.{u, uC, vC} J RC) ∧
    ∃ i : laxInternalPushforward (𝟭 C)
        (fun M : Sheaf J AddCommGrpCat.{u} ↦ M.property)
        RC RC (laxIdentityCoefficient RC) ≅ 𝟭 _,
    ∃ s : laxSectionPushforward (𝟭 C)
        (fun M : Sheaf J AddCommGrpCat.{u} ↦ M.property)
        RC RC (laxIdentityCoefficient RC) ≅ 𝟭 _,
      (∀ M : Mod (Sheaf J AddCommGrpCat.{u}) RC, (i.hom.app M).hom = 𝟙 M.X) ∧
      (∀ (M : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf.{u, uC, vC} J RC)))
          (U : Cᵒᵖ), ((s.hom.app M).val.app U).hom.toAddMonoidHom =
            AddMonoidHom.id _) ∧
      (∀ M : Mod (Sheaf J AddCommGrpCat.{u}) RC,
        (sectionModuleEquivalence.{u, uC, vC} J RC).functor.map (i.hom.app M) =
          (laxSectionComparison (𝟭 C) (fun N : Sheaf J AddCommGrpCat.{u} ↦ N.property)
              RC RC (laxIdentityCoefficient RC)).hom.app M ≫
            s.hom.app ((sectionModuleEquivalence.{u, uC, vC} J RC).functor.obj M)) := by
  let hid := fun M : Sheaf J AddCommGrpCat.{u} ↦ M.property
  let ψid := laxIdentityCoefficient RC
  have hring : laxSectionRingMap (𝟭 C) hid RC RC ψid = 𝟙 (sectionRings J RC) := by
    ext U x
    exact congrArg (fun z ↦ z x) (laxSectionRingMap_additive (𝟭 C) hid RC RC ψid U)
  let PS := laxSectionPushforward (𝟭 C) hid RC RC ψid
  let e (M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf J RC))) :
      PS.obj M ≅ M := by
    have hs (U : Cᵒᵖ) (r : (sectionRings J RC).obj U) (x : M.val.obj U) :
        r • (@id ((PS.obj M).val.obj U) x) = r • x := by
      change ((laxSectionRingMap (𝟭 C) hid RC RC ψid).app U).hom r • x = r • x
      rw [hring]
      rfl
    exact
      { hom := ⟨PresheafOfModules.homMk (𝟙 _) hs⟩
        inv := ⟨PresheafOfModules.homMk (𝟙 _) (fun U r x ↦ (hs U r x).symm)⟩
        hom_inv_id := by ext U x; rfl
        inv_hom_id := by ext U x; rfl }
  let s : PS ≅ 𝟭 _ := NatIso.ofComponents e (fun f ↦ by ext U x; rfl)
  let E := (sectionModuleEquivalence J RC).functor
  let z := laxSectionComparison (𝟭 C) hid RC RC ψid ≪≫
    Functor.isoWhiskerLeft E s ≪≫ E.rightUnitor ≪≫ E.leftUnitor.symm
  let i := Functor.fullyFaithfulCancelRight E z
  have hi (M : Mod (Sheaf J AddCommGrpCat.{u}) RC) :
      E.map (i.hom.app M) =
        (laxSectionComparison (𝟭 C) hid RC RC ψid).hom.app M ≫ s.hom.app (E.obj M) := by
    dsimp only [i, Functor.fullyFaithfulCancelRight_hom_app]
    rw [Functor.map_preimage]
    simp [z]
  refine ⟨hring, i, s, ?_, fun M U ↦ rfl, hi⟩
  intro M
  ext U x
  have h := congrArg (fun f ↦ ((f.val.app U).hom x)) (hi M)
  change ((i.hom.app M).hom.hom.app U).hom x =
    (((laxSectionComparison (𝟭 C) hid RC RC ψid).hom.app M).val.app U).hom x at h
  exact h.trans (laxSectionComparison_apply (𝟭 C) hid RC RC ψid M U x)

end CategoryTheory.InternalAbelianSheafModule
