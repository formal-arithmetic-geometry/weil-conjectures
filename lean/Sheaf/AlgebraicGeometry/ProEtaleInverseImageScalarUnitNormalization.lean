/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import all Sheaf.SecSmoothPurity.CochainInverseComparison

/-!
# Scalar-unit normalization of the specified pro-etale inverse image

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03EL, Section 03EK;
Sites, Tag 00YV (blueprint: lem-pur-inverse-image-scalar-unit-normalization).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules MonoidalCategory
open scoped ChangeOfRings
open CanonicalRingedTensorComparisonOnSmallSites
namespace SheafOfModules
universe c v d z w
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] monoidalCategory

private theorem normalizationComposeInstance {E : Type c} [Category.{v} E]
    [EssentiallySmall.{w} E] (J : GrothendieckTopology E) :
    J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance

private theorem normalizationSheafifyInstance {E : Type c} [Category.{v} E]
    [EssentiallySmall.{w} E] (J : GrothendieckTopology E) :
    HasWeakSheafify J AddCommGrpCat.{w} := inferInstance

attribute [local instance] normalizationComposeInstance normalizationSheafifyInstance

variable {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{w}) (RI : Sheaf JD CommRingCat.{w})
  (uInv : Sheaf JC (Type w) ⥤ Sheaf JD (Type w))
  (AI : AlgebraicInverseImage uInv R RI) (g : C ⥤ D)

/-- The comparison normalized by the identity-scalar-extension isomorphism.
This is exactly a inverse, followed by mu, followed by a tensor a.
Source: Stacks Project, Tag 03EL and the scalar-unit cancellation of Section 03EK
(blueprint: lem-pur-inverse-image-scalar-unit-normalization). -/
noncomputable def CanonicalRingedTensorComparisonOnSmallSites.normalizedHom
    (T : SheafOfModules.{w} ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj RI))
    (ho : ∀ M, T.obj M = changeOfRings.{z, d, w} (𝟙 RI) (AI.modules.obj M))
    (k : CanonicalRingedTensorComparisonOnSmallSites R RI RI uInv AI (𝟙 RI) T ho)
    (a : T ≅ AI.modules)
    (M N : SheafOfModules.{w} ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    AI.modules.obj ((monoidalCategory.{v, c, w} R).tensorObj M N) ⟶
      (monoidalCategory.{z, d, w} RI).tensorObj (AI.modules.obj M) (AI.modules.obj N) :=
  a.inv.app ((monoidalCategory.{v, c, w} R).tensorObj M N) ≫ (k.mu M N).hom ≫
    (monoidalCategory.{z, d, w} RI).tensorHom (a.hom.app M) (a.hom.app N)

/-- The full section equation for a supplied unit-section operation. The theorem below
supplies the specified pro-etale adjunction unit, rather than an arbitrary section map.
Factoring this formula over abstract sites avoids unfolding concrete sites repeatedly.
Source: Stacks Project, Tag 03EL and Section 03EK
(blueprint: lem-pur-inverse-image-scalar-unit-normalization). -/
noncomputable def scalarUnitComparisonNormalized
    (η : ∀ (M : SheafOfModules.{w} ((sheafCompose JC
        (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (V : C),
      M.val.obj (op V) → (AI.modules.obj M).val.obj (op (g.obj V)))
    (T : SheafOfModules.{w} ((sheafCompose JC
        (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj RI))
    (ho : ∀ M, T.obj M = changeOfRings.{z, d, w} (𝟙 RI) (AI.modules.obj M))
    (a : T ≅ AI.modules) : Prop :=
  ∀ (k : CanonicalRingedTensorComparisonOnSmallSites R RI RI uInv AI (𝟙 RI) T ho)
    (M N : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (V : C)
    (s : M.val.obj (op V)) (t : N.val.obj (op V)),
    (normalizedHom R RI uInv AI T ho k a M N).val.app (op (g.obj V))
      (η ((monoidalCategory.{v, c, w} R).tensorObj M N) V
        (ringedComparisonPure R M N (op V) s t)) =
    ringedComparisonPure RI (AI.modules.obj M) (AI.modules.obj N) (op (g.obj V))
      (η M V s) (η N V t)


section IdentityScalars
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type c} [Category.{v} E] [EssentiallySmall.{w} E]
  {J : GrothendieckTopology E}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (A : Sheaf J CommRingCat.{w})
  (H : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A))

private noncomputable def scalarPresheafIso : changeOfRingsPresheaf.{v, c, w} (𝟙 A) H ≅ H.val :=
  PresheafOfModules.isoMk (fun W ↦ (ModuleCat.extendScalarsId (A.obj.obj W)).app
    (H.val.obj W)) (by
      intro U V i
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      change (ModuleCat.extendScalarsId (A.obj.obj V)).hom.app (H.val.obj V)
        (changeOfRingsMap.{v, c, w} (𝟙 A) H i ((1 : A.obj.obj U) ⊗ₜ[A.obj.obj U, RingHom.id _] m)) =
        H.val.map i ((ModuleCat.extendScalarsId (A.obj.obj U)).hom.app
          (H.val.obj U) ((1 : A.obj.obj U) ⊗ₜ[A.obj.obj U, RingHom.id _] m))
      erw [Classical.choose_spec (exists_changeOfRingsMap.{v, c, w} (𝟙 A) H i)]
      simp only [map_one, ModuleCat.extendScalarsId_hom_app_one_tmul]
      exact ModuleCat.extendScalarsId_hom_app_one_tmul _ _)

private noncomputable def scalarMulIso : changeOfRings.{v, c, w} (𝟙 A) H ≅ H :=
  (PresheafOfModules.sheafification.{w} (𝟙 _)).mapIso (scalarPresheafIso A H) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction.{w} (𝟙 _)).counit.app H)

private theorem scalarMulIso_one (W : Eᵒᵖ) (m : H.val.obj W) :
    (scalarMulIso A H).hom.val.app W (ringedComparisonScalarSection (𝟙 A) H W 1 m) = m := by
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)
  have hn := adj.unit.naturality (scalarPresheafIso A H).hom
  have ht := adj.right_triangle_components H
  have hh := congrArg (fun f ↦ f.app W ((1 : A.obj.obj W) ⊗ₜ[A.obj.obj W, RingHom.id _] m))
    (congrArg (fun f ↦ f ≫ (adj.counit.app H).val) hn)
  change (adj.counit.app H).val.app W
      (adj.unit.app H.val |>.app W
        ((scalarPresheafIso A H).hom.app W ((1 : A.obj.obj W) ⊗ₜ[A.obj.obj W, RingHom.id _] m))) =
    (scalarMulIso A H).hom.val.app W
      (ringedComparisonScalarSection (𝟙 A) H W 1 m) at hh
  rw [show (scalarPresheafIso A H).hom.app W
      ((1 : A.obj.obj W) ⊗ₜ[A.obj.obj W, RingHom.id _] m) = m from
        ModuleCat.extendScalarsId_hom_app_one_tmul _ _] at hh
  exact hh.symm.trans (congrArg (fun f ↦ f.app W m) ht)


private theorem scalarMulIso_pure (W : Eᵒᵖ) (b : A.obj.obj W) (m : H.val.obj W) :
    (scalarMulIso A H).hom.val.app W (ringedComparisonScalarSection (𝟙 A) H W b m) =
      b • m := by
  have h := scalarMulIso_one A H W m
  have he : ringedComparisonScalarSection (𝟙 A) H W b m =
      b • ringedComparisonScalarSection (𝟙 A) H W 1 m := by
    let eta := ((PresheafOfModules.sheafificationAdjunction.{w} (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)).unit.app
        (changeOfRingsPresheaf.{v, c, w} (𝟙 A) H)).app W
    have ht : (b ⊗ₜ[A.obj.obj W, RingHom.id _] m) =
        b • ((1 : A.obj.obj W) ⊗ₜ[A.obj.obj W, RingHom.id _] m) := by
      rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
    exact (congrArg (fun x ↦ eta x) ht).trans (eta.hom.map_smul b _)
  rw [he, map_smul, h]

private theorem scalarMulIso_inv (W : Eᵒᵖ) (m : H.val.obj W) :
    (scalarMulIso A H).inv.val.app W m =
      ringedComparisonScalarSection (𝟙 A) H W 1 m := by
  have h := scalarMulIso_one A H W m
  have hi := congrArg (fun f ↦ f.val.app W
      (ringedComparisonScalarSection (𝟙 A) H W 1 m)) (scalarMulIso A H).hom_inv_id
  change (scalarMulIso A H).inv.val.app W
    ((scalarMulIso A H).hom.val.app W _) = _ at hi
  rw [h] at hi
  exact hi

private noncomputable def scalarPresheafFunctor :
    SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A) ⥤
      PresheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj where
  obj H := changeOfRingsPresheaf.{v, c, w} (𝟙 A) H
  map {H K} f :=
    { app := fun W ↦ (ModuleCat.extendScalars (RingHom.id (A.obj.obj W))).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{v, c, w} (𝟙 A) H f }
  map_id H := by
    ext W : 1
    exact (ModuleCat.extendScalars (RingHom.id (A.obj.obj W))).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (RingHom.id (A.obj.obj W))).map_comp _ _

private noncomputable def scalarFunctor := scalarPresheafFunctor A ⋙
  PresheafOfModules.sheafification.{w} (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)

private noncomputable def scalarNatIso : scalarFunctor A ≅ 𝟭 _ := by
  let G := SheafOfModules.forget
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A) ⋙
    PresheafOfModules.restrictScalars (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)
  let e : scalarPresheafFunctor A ≅ G :=
    NatIso.ofComponents (fun H ↦ scalarPresheafIso A H) (by
      intro H K f
      ext W : 1
      exact (ModuleCat.extendScalarsId (A.obj.obj W)).hom.naturality (f.val.app W))
  let S := PresheafOfModules.sheafification.{w} (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)
  let a : scalarFunctor A ≅ 𝟭 _ := Functor.isoWhiskerRight e S ≪≫ asIso adj.counit
  exact NatIso.ofComponents (fun H ↦ scalarMulIso A H) (fun f ↦ a.hom.naturality f)

end IdentityScalars


section PureSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type c} [Category.{v} E] [EssentiallySmall.{w} E]
  {J : GrothendieckTopology E}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (A : Sheaf J CommRingCat.{w})

private theorem comparisonPure_restrict
    (M N : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj A))
    {U V : Eᵒᵖ} (i : U ⟶ V) (m : M.val.obj U) (n : N.val.obj U) :
    ((monoidalCategory A).tensorObj M N).val.map i (ringedComparisonPure A M N U m n) =
      ringedComparisonPure A M N V (M.val.map i m) (N.val.map i n) :=
  CochainScalarConstruction.pure_restrict A M N i m n

private theorem comparisonPure_map
    {M M' N N' : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj A)}
    (f : M ⟶ M') (g : N ⟶ N') (W : Eᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory A).tensorHom f g).val.app W (ringedComparisonPure A M N W m n) =
      ringedComparisonPure A M' N' W (f.val.app W m) (g.val.app W n) :=
  CochainScalarConstruction.pure_map A f g W m n

private theorem comparisonPure_iso
    {M M' N N' : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj A)}
    (e : M ≅ M') (f : N ≅ N') (W : Eᵒᵖ) (m : M'.val.obj W) (n : N'.val.obj W) :
    ((monoidalCategory A).tensorHom e.hom f.hom).val.app W
      (ringedComparisonPure A M N W (e.inv.val.app W m) (f.inv.val.app W n)) =
      ringedComparisonPure A M' N' W m n := by
  have he : e.hom.val.app W (e.inv.val.app W m) = m :=
    congrArg (fun k ↦ k.val.app W m) e.inv_hom_id
  have hf : f.hom.val.app W (f.inv.val.app W n) = n :=
    congrArg (fun k ↦ k.val.app W n) f.inv_hom_id
  exact (comparisonPure_map A e.hom f.hom W _ _).trans
    (congrArg₂ (ringedComparisonPure A M' N' W) he hf)

private noncomputable abbrev normalizationUnderlying :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})

private noncomputable def comparisonPureSheaf
    (M N : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj A)) :
    (normalizationUnderlying A).obj M ⊗ (normalizationUnderlying A).obj N ⟶
      (normalizationUnderlying A).obj ((monoidalCategory A).tensorObj M N) :=
  ⟨{ app := fun W ↦ ↾fun p ↦ ringedComparisonPure A M N W p.1 p.2
     naturality := by
       intro U V i
       ext p
       exact (comparisonPure_restrict A M N i p.1 p.2).symm }⟩
end PureSections

section NormalizationFormula
attribute [local irreducible] ringedComparisonPure
set_option allowUnsafeReducibility true in
attribute [local reducible] RingedComparisonInsertion RingedComparisonTensor
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem normalizationFormulaOnSites
    (η : ∀ (F : Sheaf JC (Type w)) (V : C),
      F.obj.obj (op V) → (uInv.obj F).obj.obj (op (g.obj V)))
    (hη : ∀ {F G : Sheaf JC (Type w)} (b : F ⟶ G) (V : C) (p : F.obj.obj (op V)),
      (uInv.map b).hom.app (op (g.obj V)) (η F V p) = η G V (b.hom.app (op V) p))
    (T : SheafOfModules.{w} ((sheafCompose JC
        (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj RI))
    (ho : ∀ M, T.obj M = changeOfRings (𝟙 RI) (AI.modules.obj M))
    (a : T ≅ AI.modules)
    (hi : ∀ M W m, (a.inv.app M).val.app W m =
      (eqToHom (ho M).symm).val.app W
        (ringedComparisonScalarSection (𝟙 RI) (AI.modules.obj M) W 1 m)) :
    scalarUnitComparisonNormalized R RI uInv AI g
      (fun M V s ↦ (AI.moduleUnderlying.inv.app M).hom.app (op (g.obj V))
        (η ((normalizationUnderlying R).obj M) V s)) T ho a := by
  intro k M N V s t
  let W : Dᵒᵖ := op (g.obj V)
  let U := normalizationUnderlying R
  let Z : Sheaf JC (Type w) := U.obj M ⊗ U.obj N
  let x : Z ⟶ U.obj M := CartesianMonoidalCategory.fst _ _
  let y : Z ⟶ U.obj N := CartesianMonoidalCategory.snd _ _
  let z : Z ⟶ U.obj ((monoidalCategory R).tensorObj M N) := comparisonPureSheaf R M N
  let p : Z.obj.obj (op V) := (s, t)
  let q := η Z V p
  have hq (H : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
      (W : Dᵒᵖ) (m : (AI.modules.obj H).val.obj W) :
      (k.q H).hom.app W m = (a.inv.app H).val.app W m :=
    (k.q_one H W m).trans (hi H W m).symm
  have hx : (uInv.map x).hom.app W q = η (U.obj M) V s := hη x V p
  have hy : (uInv.map y).hom.app W q = η (U.obj N) V t := hη y V p
  have hz : (uInv.map z).hom.app W q =
      η (U.obj ((monoidalCategory R).tensorObj M N)) V
        (ringedComparisonPure R M N (op V) s t) := hη z V p
  let mu := (k.mu M N).hom
  let qM := k.q M
  let qN := k.q N
  let qMN := k.q ((monoidalCategory R).tensorObj M N)
  have he := k.pure M N Z x y z (by intro W p; rfl) W q
  change mu.val.app W
      (qMN.hom.app W ((AI.moduleUnderlying.inv.app _).hom.app W
        ((uInv.map z).hom.app W q))) =
    ringedComparisonPure RI (T.obj M) (T.obj N) W
      (qM.hom.app W ((AI.moduleUnderlying.inv.app M).hom.app W
        ((uInv.map x).hom.app W q)))
      (qN.hom.app W ((AI.moduleUnderlying.inv.app N).hom.app W
        ((uInv.map y).hom.app W q))) at he
  rw [hx, hy, hz] at he
  have hM := hq M W
  have hN := hq N W
  have hMN := hq ((monoidalCategory R).tensorObj M N) W
  change ∀ m, qM.hom.app W m = (a.inv.app M).val.app W m at hM
  change ∀ m, qN.hom.app W m = (a.inv.app N).val.app W m at hN
  change ∀ m, qMN.hom.app W m =
    (a.inv.app ((monoidalCategory R).tensorObj M N)).val.app W m at hMN
  have hM' := hM ((AI.moduleUnderlying.inv.app M).hom.app W (η (U.obj M) V s))
  have hN' := hN ((AI.moduleUnderlying.inv.app N).hom.app W (η (U.obj N) V t))
  have hMN' := hMN ((AI.moduleUnderlying.inv.app _).hom.app W
    (η (U.obj ((monoidalCategory R).tensorObj M N)) V
      (ringedComparisonPure R M N (op V) s t)))
  have hp := congrArg₂ (ringedComparisonPure RI (T.obj M) (T.obj N) W) hM' hN'
  have he := (congrArg (fun v ↦ mu.val.app W v) hMN').symm.trans (he.trans hp)
  have he' := congrArg (fun v ↦ ((monoidalCategory RI).tensorHom
    (a.hom.app M) (a.hom.app N)).val.app W v) he
  exact he'.trans (comparisonPure_iso RI (a.app M) (a.app N) W
    ((AI.moduleUnderlying.inv.app M).hom.app W (η (U.obj M) V s))
    ((AI.moduleUnderlying.inv.app N).hom.app W (η (U.obj N) V t)))

end NormalizationFormula

end SheafOfModules

namespace AlgebraicGeometry.Scheme
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] monoidalCategory
-- Keep the specified abbrev folded while elaborating section rings. This affects
-- local elaboration only; the declaration and its mathematical value are unchanged.
set_option allowUnsafeReducibility true in
attribute [local irreducible] proEtaleSheafInverseImage

/-- The specified set-unit section, viewed through an algebraic presentation's
underlying-sheaf identification. This is evaluation of the existing unit and isomorphism.
Source: Stacks Project, Tag 03D2 and Sites Tag 00YV
(blueprint: lem-pur-inverse-image-scalar-unit-normalization). -/
noncomputable def proEtaleAlgebraicUnitSection {X Y : Scheme.{u}} (h : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (AI : AlgebraicInverseImage (proEtaleSheafInverseImage h (Type (u + 1))) R
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
    (M : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1}
    RingCat.{u + 1})).obj R)) (V : Y.ProEt) (s : M.val.obj (op V)) :
    (AI.modules.obj M).val.obj (op ((proEtaleBaseChange h).obj V)) :=
  (AI.moduleUnderlying.inv.app M).hom.app (op ((proEtaleBaseChange h).obj V))
    (((proEtaleSheafAdjunction h (Type (u + 1))).unit.app
      ((toSheaf.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u
    + 1})).obj R) ⋙ sheafCompose (ProEt.topology Y)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M)).hom.app (op V) s)

/-- The full certificate in the scalar-unit normalization statement. Its fields retain
all specified functors, unit identifications, scalar formulas and the universally quantified
comparison formula. No data are selected from a mere existence theorem.
Source: Stacks Project, Tags 03D2, 03EL and Section 03EK
(blueprint: lem-pur-inverse-image-scalar-unit-normalization). -/
structure ProEtaleScalarUnitNormalization {X Y : Scheme.{u}} (h : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) where
  algebraic : AlgebraicInverseImage (proEtaleSheafInverseImage h (Type (u + 1))) R
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)
  modules_eq : algebraic.modules = proEtaleModuleInverseImage h R
  ring_unit : ∀ (V : Y.ProEt) (r : R.obj.obj (op V)), algebraic.ringUnderlying.hom.hom.app (op
    ((proEtaleBaseChange h).obj V)) (((proEtaleSheafAdjunction h (Type (u + 1))).unit.app
    ((sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat.{u + 1})).obj R)).hom.app
    (op V) r) = ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app R).hom.app (op V) r
  module_unit : ∀ (M : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (V : Y.ProEt) (s : M.val.obj (op V)), (eqToHom
    (congrArg (fun (F : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤ ringedSiteModules.{u + 1} ((sheafCompose
    (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))) ↦ F.obj M) modules_eq)).val.app
    (op ((proEtaleBaseChange h).obj V)) (proEtaleAlgebraicUnitSection h R algebraic M V s) =
    (((pullbackPushforwardAdjunction (proEtaleModelRingUnit h R)).unit.app ((proEtaleModuleToModel
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj
    M)).val.app (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj V))) s
  scalar : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤ ringedSiteModules.{u + 1} ((sheafCompose
    (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
  scalar_obj : ∀ M : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R), scalar.obj M = changeOfRings.{u, u + 1, u + 1}
    (𝟙 ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)) (algebraic.modules.obj M)
  scalar_map : ∀ (M N : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (f : M ⟶ N), scalar.map f = eqToHom (scalar_obj
    M) ≫ changeOfRingsHom.{u, u + 1, u + 1} (𝟙 ((proEtaleSheafInverseImage h
    CommRingCat.{u + 1}).obj R)) (algebraic.modules.obj M) (algebraic.modules.map f) ≫ eqToHom
    (scalar_obj N).symm
  multiplication : scalar ≅ algebraic.modules
  multiply_pure : ∀ (M : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (W : X.ProEtᵒᵖ) (b : ((proEtaleSheafInverseImage
    h CommRingCat.{u + 1}).obj R).obj.obj W) (m : (algebraic.modules.obj M).val.obj W),
    (multiplication.hom.app M).val.app W ((eqToHom (scalar_obj M).symm).val.app W
    (((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((proEtaleSheafInverseImage h
    CommRingCat.{u + 1}).obj R)).obj)).unit.app (changeOfRingsPresheaf.{u, u + 1, u + 1} (𝟙
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)) (algebraic.modules.obj M))).app W
    (b ⊗ₜ[((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R).obj.obj W, RingHom.id _] m)))
    = b • m
  insert_one : ∀ (M : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (W : X.ProEtᵒᵖ) (m : (algebraic.modules.obj
    M).val.obj W), (multiplication.inv.app M).val.app W m = ((eqToHom (scalar_obj M).symm).val.app
    W (((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((proEtaleSheafInverseImage h
    CommRingCat.{u + 1}).obj R)).obj)).unit.app (changeOfRingsPresheaf.{u, u + 1, u + 1} (𝟙
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)) (algebraic.modules.obj M))).app W
    ((1 : ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R).obj.obj W)
    ⊗ₜ[((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R).obj.obj W, RingHom.id _] m)))
  normalized : scalarUnitComparisonNormalized.{u + 1, u, u + 1, u, u + 1}
    (C := Y.ProEt) (D := X.ProEt) (JC := ProEt.topology Y) (JD := ProEt.topology X)
    R
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)
    (proEtaleSheafInverseImage h (Type (u + 1))) algebraic (proEtaleBaseChange h)
    (proEtaleAlgebraicUnitSection h R algebraic) scalar scalar_obj multiplication


open AlgebraicGeometry.ProEtaleTensorComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option allowUnsafeReducibility true in
attribute [local reducible] proEtaleSheafInverseImage

private noncomputable def normalizationAlgebraic {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    AlgebraicInverseImage (proEtaleSheafInverseImage f (Type (u + 1))) R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) := by
  let eR := ringSetsIdentification f R
  let eI : (SheafOfModules.toSheaf ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⋙
        sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1})) ⋙
      AlgebraicGeometry.ProEtale.setPullback f ≅
      inverse f R ⋙ (SheafOfModules.toSheaf ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (inverseRing f R)) ⋙
          sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) :=
    NatIso.ofComponents (fun M ↦ moduleSetsIdentification f M)
      (fun k ↦ moduleSetsIdentification_naturality f k)
  have hr (U : Y.ProEtᵒᵖ) (r : R.obj.obj U) :
      eR.hom.hom.app ((proEtaleBaseChange f).op.obj U)
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (AlgebraicGeometry.ProEtaleTensorComparison.ringSets R)).hom.app U r) =
      ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U r :=
    (Classical.choose_spec (ringSetsIdentification_exists f R)).1 U.unop r
  have hm (M : Modules R) (U : Y.ProEtᵒᵖ) (m : M.val.obj U) :
      (moduleSetsIdentification f M).hom.hom.app ((proEtaleBaseChange f).op.obj U)
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (moduleSets M)).hom.app U m) = inverseSection f M U.unop m :=
    (Classical.choose_spec (moduleSetsIdentification_exists f M)).1 U.unop m
  refine {
    ringUnderlying := eR
    modules := inverse f R
    moduleUnderlying := eI.symm
    ringAdd := ?_
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_
  }
  · intro T a b t ht
    exact transport_binary f eR eR eR
      (fun U x y ↦ @Add.add (R.obj.obj U) inferInstance x y)
      (fun V x y ↦ @Add.add ((inverseRing f R).obj.obj V) inferInstance x y)
      (fun i x y ↦ ((inverseRing f R).obj.map i).hom.map_add x y |>.symm)
      (by
        intro U x y
        rw [hr, hr, hr]
        exact (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U).hom.map_add
          x y) T a b t ht
  · intro T a b t ht
    exact transport_binary f eR eR eR
      (fun U x y ↦ @Mul.mul (R.obj.obj U) inferInstance x y)
      (fun V x y ↦ @Mul.mul ((inverseRing f R).obj.obj V) inferInstance x y)
      (fun i x y ↦ ((inverseRing f R).obj.map i).hom.map_mul x y |>.symm)
      (by
        intro U x y
        rw [hr, hr, hr]
        exact (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U).hom.map_mul
          x y) T a b t ht
  · intro T a ha
    exact transport_binary f eR eR eR
      (fun U _ _ ↦ (0 : R.obj.obj U))
      (fun V _ _ ↦ (0 : (inverseRing f R).obj.obj V))
      (fun i _ _ ↦ ((inverseRing f R).obj.map i).hom.map_zero.symm)
      (by
        intro U x y
        rw [hr]
        exact (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U).hom.map_zero)
      T a a a ha
  · intro T a ha
    exact transport_binary f eR eR eR
      (fun U _ _ ↦ (1 : R.obj.obj U))
      (fun V _ _ ↦ (1 : (inverseRing f R).obj.obj V))
      (fun i _ _ ↦ ((inverseRing f R).obj.map i).hom.map_one.symm)
      (by
        intro U x y
        rw [hr]
        exact (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U).hom.map_one)
      T a a a ha
  · intro M T a b t ht
    exact transport_binary f (moduleSetsIdentification f M) (moduleSetsIdentification f M)
      (moduleSetsIdentification f M)
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun V x y ↦ @Add.add (((inverse f R).obj M).val.obj V) inferInstance x y)
      (fun i x y ↦ (((inverse f R).obj M).val.map i).hom.map_add x y |>.symm)
      (by intro U x y; rw [hm, hm, hm]; exact inverseSection_add f M U.unop x y)
      T a b t ht
  · intro M T a ha
    exact transport_binary f (moduleSetsIdentification f M) (moduleSetsIdentification f M)
      (moduleSetsIdentification f M)
      (fun U _ _ ↦ (0 : M.val.obj U))
      (fun V _ _ ↦ (0 : ((inverse f R).obj M).val.obj V))
      (fun i _ _ ↦ (((inverse f R).obj M).val.map i).hom.map_zero.symm)
      (by
        intro U x y
        rw [hm]
        exact (((SheafOfModules.pullbackPushforwardAdjunction
          (proEtaleModelRingUnit f R)).unit.app
            ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.app
                (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj U.unop))).hom.map_zero)
      T a a a ha
  · intro M T a b t ht
    exact transport_binary f eR (moduleSetsIdentification f M) (moduleSetsIdentification f M)
      (fun U x y ↦ @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x y)
      (fun V x y ↦ @SMul.smul ((inverseRing f R).obj.obj V)
        (((inverse f R).obj M).val.obj V) inferInstance x y)
      (fun i x y ↦ (((inverse f R).obj M).val.map_smul i x y).symm)
      (by intro U x y; rw [hm, hr, hm]; exact inverseSection_smul f M U.unop x y)
      T a b t ht



set_option allowUnsafeReducibility true in
attribute [local irreducible] proEtaleSheafInverseImage

/-- The specified module inverse image has its canonical algebraic presentation, and
identity scalar extension cancels every normalized ringed tensor comparison.
Source: Stacks Project, Tags 03D2 and 03EL, Section 03EK, and Sites Tag 00YV
(blueprint: lem-pur-inverse-image-scalar-unit-normalization).

Proof:
1. Finite-limit preservation of the set inverse image transports ring and module
operations. Their graph equations follow by applying the binary-product comparison
and checking both projections. Use the specified module functor itself; the canonical
underlying identifications are fixed by their ring and module adjunction-unit formulas.
This uses lem-weil-pbc-left-exact-site-inverse-image-tensor and the specified inverse image.
2. The bilinear universal property (lem-pc-sites-sheaf-tensor-bilinear-universal)
constructs multiplication a on identity scalar extension. Insertion q sends m to 1 tensor m;
balancing gives its linearity. All pure tensors pass through module sheafification.
3. Multiplication after insertion is the identity because 1 acts as the identity.
Insertion after multiplication is the identity on pure tensors by balancing, hence on
the whole sheaf tensor by injectivity of the same universal property.
4. Linearity of I(f) gives naturality of multiplication and insertion. Tensor generation
and sheafification uniqueness give the functor laws of T and its specified morphisms.
5. For any normalized comparison, q_one identifies its q with a inverse. Use the product
of the underlying sheaves of M and N as the test sheaf in its generalized pure equation.
Evaluate at the unit image of (s,t); unit naturality for the two projections and the pure
pairing gives the three original unit sections. Apply a tensor a and cancel a after q
on both factors. This gives the final formula, without assuming target sheaf sections
are globally generated by the original unit images. -/
theorem proEtaleInverseImage_scalarUnit_normalization
    {X Y : Scheme.{u}} (h : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    Nonempty (ProEtaleScalarUnitNormalization h R) := by
  let AI := normalizationAlgebraic h R
  let S := (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R
  let T := AI.modules ⋙ scalarFunctor S
  let a : T ≅ AI.modules :=
    Functor.isoWhiskerLeft AI.modules (scalarNatIso S) ≪≫ AI.modules.rightUnitor
  refine ⟨{
    algebraic := AI
    modules_eq := rfl
    ring_unit := ?_
    module_unit := ?_
    scalar := T
    scalar_obj := fun _ ↦ rfl
    scalar_map := ?_
    multiplication := a
    multiply_pure := ?_
    insert_one := ?_
    normalized := ?_
  }⟩
  · intro V r
    exact (Classical.choose_spec (ringSetsIdentification_exists h R)).1 V r
  · intro M V s
    exact (Classical.choose_spec (moduleSetsIdentification_exists h M)).1 V s
  · intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro M W b m
    exact scalarMulIso_pure S (AI.modules.obj M) W b m
  · intro M W m
    exact scalarMulIso_inv S (AI.modules.obj M) W m
  · exact normalizationFormulaOnSites R S _ AI (proEtaleBaseChange h)
      (fun F V s ↦ ((proEtaleSheafAdjunction h (Type (u + 1))).unit.app F).hom.app
        (op V) s)
      (by
        intro F G b V p
        exact (congrArg (fun k ↦ k.hom.app (op V) p)
          ((proEtaleSheafAdjunction h (Type (u + 1))).unit.naturality b)).symm)
      T (fun _ ↦ rfl) a
      (by intro M W m; exact scalarMulIso_inv S (AI.modules.obj M) W m)


end AlgebraicGeometry.Scheme
