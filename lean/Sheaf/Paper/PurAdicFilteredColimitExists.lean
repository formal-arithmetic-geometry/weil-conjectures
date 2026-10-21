/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V6
-/
module

public import Sheaf.Paper.PurAdicLineSystemData
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-! # Filtered colimits of varying ring/module pairs

Source: the Integral twist and Rational and algebraic closure paragraphs of the
main-20261015 coefficient-twists proof (blueprint: lem-pur-adic-filtered-colimit-exists).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe w uC vC uD vD

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace CategoryTheory

namespace PurAdicColimitConstruction
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  {I : Type w} [PartialOrder I]
  (A : PurAdicPairDiagram.{w} J I)
@[instance_reducible] private def presentationModule (i : I) (W : Cᵒᵖ) :
    Module ((A.R.obj i).obj.obj W) ((A.P.obj i).obj.obj W) :=
  let q := ((sheafToPresheaf J AddCommGrpCat.{w}).mapIso (A.identify i)).app W
  let e : (A.P.obj i).obj.obj W ≃+ (A.M i).val.obj W :=
    q.symm.addCommGroupIsoToAddEquiv
  AddEquiv.module (β := (A.M i).val.obj W) ((A.R.obj i).obj.obj W) e
private theorem presentation_smul (i : I) (W : Cᵒᵖ)
    (r : (A.R.obj i).obj.obj W) (m : (A.P.obj i).obj.obj W) :
    letI := presentationModule A i W
    r • m = A.act i W r m := by
  rfl
private theorem presentation_semilinear {i j : I} (f : i ⟶ j) (W : Cᵒᵖ)
    (r : (A.R.obj i).obj.obj W) (m : (A.P.obj i).obj.obj W) :
    (A.P.map f).hom.app W (A.act i W r m) =
      A.act j W ((A.R.map f).hom.app W r) ((A.P.map f).hom.app W m) := by
  have h := A.semilinear f W r ((A.identify i).inv.hom.app W m)
  simpa only [PurAdicPairDiagram.act, ← ConcreteCategory.comp_apply,
    ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.inv_hom_id, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app, Category.id_comp, ConcreteCategory.id_apply, id_eq] using h
private theorem presentation_restriction (i : I) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (r : (A.R.obj i).obj.obj X) (m : (A.P.obj i).obj.obj X) :
    (A.P.obj i).obj.map f (A.act i X r m) =
      A.act i Y ((A.R.obj i).obj.map f r) ((A.P.obj i).obj.map f m) := by
  let x : (A.M i).val.obj X := (A.identify i).inv.hom.app X m
  have hInv := ConcreteCategory.congr_hom
    ((A.identify i).inv.hom.naturality f) m
  have hHom := ConcreteCategory.congr_hom ((A.identify i).hom.hom.naturality f)
    (r • x)
  change (A.identify i).inv.hom.app Y ((A.P.obj i).obj.map f m) =
    (A.M i).val.map f ((A.identify i).inv.hom.app X m) at hInv
  change (A.identify i).hom.hom.app Y
      ((A.M i).val.map f (r • x)) =
    (A.P.obj i).obj.map f
      ((A.identify i).hom.hom.app X (r • x)) at hHom
  dsimp only [PurAdicPairDiagram.act, id_eq]
  rw [← hHom, (A.M i).val.map_smul, ← hInv]
  rfl

variable [Nonempty I] [IsDirected I (· ≤ ·)]

private abbrev ringColim := colimit (A.R ⋙ sheafToPresheaf J CommRingCat.{w})
private abbrev addColim := colimit (A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w})
@[instance_reducible] private def colimitSectionModule (W : Cᵒᵖ) :
    Module ((ringColim A).obj W) ((addColim A).obj W) := by
  let R := A.R ⋙ sheafToPresheaf J CommRingCat.{w} ⋙
    (evaluation Cᵒᵖ CommRingCat.{w}).obj W ⋙ forget₂ CommRingCat.{w} RingCat.{w}
  let P := A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj W
  letI (i : I) : Module (R.obj i) (P.obj i) := presentationModule A i W
  have H : ∀ {i j : I} (f : i ⟶ j) (r : R.obj i) (m : P.obj i),
      P.map f (r • m) = R.map f r • P.map f m := by
    intro i j f r m
    change (A.P.map f).hom.app W (A.act i W r m) =
      A.act j W ((A.R.map f).hom.app W r) ((A.P.map f).hom.app W m)
    exact presentation_semilinear A f W r m
  exact IsColimit.module R P H
    (isColimitOfPreserves
      ((evaluation Cᵒᵖ CommRingCat.{w}).obj W ⋙ forget₂ CommRingCat.{w} RingCat.{w})
      (colimit.isColimit (A.R ⋙ sheafToPresheaf J CommRingCat.{w})))
    (isColimitOfPreserves ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj W)
      (colimit.isColimit (A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w})))


private theorem colimitSection_smul (W : Cᵒᵖ) (i : I)
    (r : (A.R.obj i).obj.obj W) (m : (A.P.obj i).obj.obj W) :
    letI := colimitSectionModule A W
    ((colimit.ι (A.R ⋙ sheafToPresheaf J CommRingCat.{w}) i).app W r) •
      ((colimit.ι (A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w}) i).app W m) =
    (colimit.ι (A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w}) i).app W
      (A.act i W r m) := by
  let R := A.R ⋙ sheafToPresheaf J CommRingCat.{w} ⋙
    (evaluation Cᵒᵖ CommRingCat.{w}).obj W ⋙ forget₂ CommRingCat.{w} RingCat.{w}
  let P := A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj W
  let (i : I) : Module (R.obj i) (P.obj i) := presentationModule A i W
  have H : ∀ {i j : I} (f : i ⟶ j) (r : R.obj i) (m : P.obj i),
      P.map f (r • m) = R.map f r • P.map f m := by
    intro i j f r m
    change (A.P.map f).hom.app W (A.act i W r m) =
      A.act j W ((A.R.map f).hom.app W r) ((A.P.map f).hom.app W m)
    exact presentation_semilinear A f W r m
  exact (IsColimit.ι_smul R P H
    (isColimitOfPreserves
      ((evaluation Cᵒᵖ CommRingCat.{w}).obj W ⋙ forget₂ CommRingCat.{w} RingCat.{w})
      (colimit.isColimit (A.R ⋙ sheafToPresheaf J CommRingCat.{w})))
    (isColimitOfPreserves ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj W)
      (colimit.isColimit (A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w}))) i r m).symm

private theorem ringStage_eq {i k : I} (h : i ≤ k) (W : Cᵒᵖ)
    (r : (A.R.obj i).obj.obj W) :
    (colimit.ι (A.R ⋙ sheafToPresheaf J CommRingCat.{w}) i).app W r =
      (colimit.ι (A.R ⋙ sheafToPresheaf J CommRingCat.{w}) k).app W
        ((A.R.map (homOfLE h)).hom.app W r) := by
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (colimit.w (A.R ⋙ sheafToPresheaf J CommRingCat.{w}) (homOfLE h)) W) r).symm

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private theorem moduleStage_eq {j k : I} (h : j ≤ k) (W : Cᵒᵖ)
    (m : (A.P.obj j).obj.obj W) :
    (colimit.ι (A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w}) j).app W m =
      (colimit.ι (A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w}) k).app W
        ((A.P.map (homOfLE h)).hom.app W m) := by
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (colimit.w (A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w}) (homOfLE h)) W) m).symm

private theorem colimitSection_commonStage (W : Cᵒᵖ) (i j k : I)
    (hi : i ≤ k) (hj : j ≤ k)
    (r : (A.R.obj i).obj.obj W) (m : (A.P.obj j).obj.obj W) :
    letI := colimitSectionModule A W
    ((colimit.ι (A.R ⋙ sheafToPresheaf J CommRingCat.{w}) i).app W r) •
      ((colimit.ι (A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w}) j).app W m) =
    (colimit.ι (A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w}) k).app W
      (A.act k W ((A.R.map (homOfLE hi)).hom.app W r)
        ((A.P.map (homOfLE hj)).hom.app W m)) := by
  rw [ringStage_eq A hi W r, moduleStage_eq A hj W m]
  exact colimitSection_smul A W k _ _

private theorem colimitSection_restriction {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (r : (ringColim A).obj X) (m : (addColim A).obj X) :
    letI := colimitSectionModule A X
    letI := colimitSectionModule A Y
    (addColim A).map f (r • m) = (ringColim A).map f r • (addColim A).map f m := by
  let FR := A.R ⋙ sheafToPresheaf J CommRingCat.{w}
  let FP := A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w}
  obtain ⟨i, ri, hri⟩ := Concrete.isColimit_exists_rep
    (FR ⋙ (evaluation Cᵒᵖ CommRingCat.{w}).obj X)
    (isColimitOfPreserves ((evaluation Cᵒᵖ CommRingCat.{w}).obj X)
      (colimit.isColimit FR)) r
  obtain ⟨j, mj, hmj⟩ := Concrete.isColimit_exists_rep
    (FP ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj X)
    (isColimitOfPreserves ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj X)
      (colimit.isColimit FP)) m
  change (colimit.ι FR i).app X ri = r at hri
  change (colimit.ι FP j).app X mj = m at hmj
  rw [← hri, ← hmj]
  obtain ⟨k, hi, hj⟩ := exists_ge_ge i j
  rw [ringStage_eq A hi X ri, moduleStage_eq A hj X mj]
  let rr := (A.R.map (homOfLE hi)).hom.app X ri
  let mm := (A.P.map (homOfLE hj)).hom.app X mj
  have hR := ConcreteCategory.congr_hom ((colimit.ι FR k).naturality f) rr
  have hP := ConcreteCategory.congr_hom ((colimit.ι FP k).naturality f) mm
  have hAct := ConcreteCategory.congr_hom ((colimit.ι FP k).naturality f)
    (A.act k X rr mm)
  change (colimit.ι FR k).app Y ((A.R.obj k).obj.map f rr) =
    (ringColim A).map f ((colimit.ι FR k).app X rr) at hR
  change (colimit.ι FP k).app Y ((A.P.obj k).obj.map f mm) =
    (addColim A).map f ((colimit.ι FP k).app X mm) at hP
  change (colimit.ι FP k).app Y ((A.P.obj k).obj.map f (A.act k X rr mm)) =
    (addColim A).map f ((colimit.ι FP k).app X (A.act k X rr mm)) at hAct
  rw [colimitSection_smul A X k, ← hAct, ← hR, ← hP, colimitSection_smul A Y k,
    presentation_restriction A k f rr mm]

private def moduleColim : PresheafOfModules.{w} (ringColim A ⋙
    forget₂ CommRingCat.{w} RingCat.{w}) :=
  letI (W : Cᵒᵖ) : Module
      ((ringColim A ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj W)
      ((addColim A).obj W) := colimitSectionModule A W
  PresheafOfModules.ofPresheaf (addColim A) (fun {_ _} f r m ↦
    colimitSection_restriction A f r m)

omit [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)] in
private theorem ring_locallyBijective [HasSheafify J CommRingCat.{w}] :
    J.WEqualsLocallyBijective CommRingCat.{w} := by
  let : PreservesFilteredColimitsOfSize.{w, w} (forget CommRingCat.{w}) :=
    preservesFilteredColimitsOfSize_shrink _
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{w} C).inverse.op)
        CommRingCat.{w} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := CommRingCat.{w})

private theorem constructedColimit
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J CommRingCat.{w}] : Nonempty (PurAdicFilteredColimit A) := by
  have : J.WEqualsLocallyBijective CommRingCat.{w} := ring_locallyBijective (J := J)
  let FR := A.R ⋙ sheafToPresheaf J CommRingCat.{w}
  let FP := A.P ⋙ sheafToPresheaf J AddCommGrpCat.{w}
  let R := (presheafToSheaf J CommRingCat.{w}).obj (ringColim A)
  let O := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
  let P := (presheafToSheaf J AddCommGrpCat.{w}).obj (addColim A)
  let α : (ringColim A ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ⟶ O.obj :=
    whiskerRight (toSheafify J (ringColim A)) (forget₂ CommRingCat.{w} RingCat.{w})
  have : Presheaf.IsLocallyInjective J α :=
    ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J (toSheafify J (ringColim A)) x y h⟩
  have : Presheaf.IsLocallySurjective J α :=
    ⟨fun x ↦ Presheaf.imageSieve_mem J (toSheafify J (ringColim A)) x⟩
  let φ : (moduleColim A).presheaf ⟶ P.obj := toSheafify J (addColim A)
  have : Presheaf.IsLocallyInjective J φ := by
    change Presheaf.IsLocallyInjective J (toSheafify J (addColim A))
    infer_instance
  have : Presheaf.IsLocallySurjective J φ := by
    change Presheaf.IsLocallySurjective J (toSheafify J (addColim A))
    infer_instance
  let M := PresheafOfModules.sheafify α φ
  refine ⟨{ R := R
            P := P
            M := M
            identify := Iso.refl _
            rι := (Sheaf.sheafifyCocone (colimit.cocone FR)).ι
            rcolimit := Sheaf.isColimitSheafifyCocone _ (colimit.isColimit FR)
            pι := (Sheaf.sheafifyCocone (colimit.cocone FP)).ι
            pcolimit := Sheaf.isColimitSheafifyCocone _ (colimit.isColimit FP)
            scalar := ?_ }⟩
  intro i j k hi hj W r m
  let _ := PresheafOfModules.Sheafify.module α φ W
  let _ := colimitSectionModule A W
  have h := ((PresheafOfModules.toSheafify α φ).app W).hom.map_smul
    ((colimit.ι FR i).app W r) ((colimit.ι FP j).app W m)
  have hStage := colimitSection_commonStage A W i j k hi hj r m
  simp only [Sheaf.sheafifyCocone_ι_app_val, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  change α.app W ((colimit.ι FR i).app W r) • φ.app W ((colimit.ι FP j).app W m) =
    φ.app W ((colimit.ι FP k).app W
      (A.act k W ((A.R.map (homOfLE hi)).hom.app W r)
        ((A.P.map (homOfLE hj)).hom.app W m)))
  change φ.app W ((colimit.ι FR i).app W r • (colimit.ι FP j).app W m) =
    α.app W ((colimit.ι FR i).app W r) • φ.app W ((colimit.ι FP j).app W m) at h
  rw [← h]
  exact congrArg (φ.app W) hStage

end PurAdicColimitConstruction

/-- A directed diagram of varying ring/module pairs has a sheaf colimit with its
common-stage scalar action.

Source: the Rational and algebraic closure paragraph of the coefficient-twists proof;
Stacks Algebra, Tags 00D6 and 00D7, and Modules on Sites, Tag 03CO.
(blueprint: lem-pur-adic-filtered-colimit-exists)

Proof: transport each module structure along its additive presentation. Apply the
filtered-colimit module construction to the sectionwise ring and additive diagrams;
semilinearity of transitions makes the action well defined. Every pair of representatives
can be moved to a common upper bound, giving the required scalar formula. Naturality of
the stage coprojections and restriction maps proves compatibility with restrictions.
This gives a presheaf module over the ring presheaf colimit. Sheafify both the ring and
module; the module sheafification transports the action along the locally bijective units.
The sheafification adjunction proves both colimit universal properties. Its linear unit
carries the common-stage scalar formula to the sheaf colimit. -/
theorem purAdicFilteredColimit_exists
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J CommRingCat.{w}]
    {I : Type w} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (A : PurAdicPairDiagram.{w} J I) : Nonempty (PurAdicFilteredColimit A) := by
  exact PurAdicColimitConstruction.constructedColimit A

end CategoryTheory
