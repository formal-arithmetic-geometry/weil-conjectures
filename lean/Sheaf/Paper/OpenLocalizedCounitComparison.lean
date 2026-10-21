/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
public import Sheaf.CategoryTheory.Sites.LocalizedModulePullbackComparison
public import Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Open localized pullback and the actual extension counit

Source: Stacks Project, Modules on Sites, Tags 03DI, 0F6Z and 04J0
(blueprint: lem-cbc-open-localized-counit-comparison).

We use the published `proEtaleSiteModel`, which retains every pro-etale object and
only enlarges the Hom universe. Localized sites are its literal Over categories.
The ring maps below are the constant-section maps, transported by precomposition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The constant coefficient sheaf on the published small model, by precomposition.
Source: Stacks 04J0 and 0H7J (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenModelCoefficient (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    Sheaf (proEtaleModelTopology X) CommRingCat.{u + 1} :=
  ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of B))

/-- The actual constant-section structural map on the small models. Its adjunct is c_g.
Source: Stacks 04J0 and 0H7J (blueprint: lem-cbc-open-localized-counit-comparison). -/
def cbcOpenModelCoefficientMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] :
    cbcOpenModelCoefficient Y B ⟶
      ((proEtaleModelBaseChange g).sheafPushforwardContinuous CommRingCat.{u + 1}
        (proEtaleModelTopology Y) (proEtaleModelTopology X)).obj
          (cbcOpenModelCoefficient X B) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of B)).hom⟩

/-- Tensor pullback in small-model coordinates, along the canonical coefficient map.
`pullbackIso` identifies it with presheaf module pullback followed by sheafification.
Source: Stacks 03D2 and 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenFinitePullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] :=
  SheafOfModules.pullback
    (SheafOfModules.ringedSiteModuleMap (proEtaleModelBaseChange g)
      (cbcOpenModelCoefficientMap g B))

/-- The actual sheafified direct-sum extension, without a replacement left adjoint.
Source: Stacks 03DI (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenExtension (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (U : Y.ProEt) :=
  SheafOfModules.localizedSystemExtension.{u + 1, u + 1, u + 1}
    (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U)

/-- The target restriction: the open object is precisely base change of U along g.
Source: Stacks 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenTargetRestriction {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] (U : Y.ProEt) :=
  SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
    (cbcOpenModelCoefficient X B) ((proEtaleModelBaseChange g).obj (AsSmall.up.obj U))

/-- H = j'^* g_B^* j_!, with composition in Lean's left-to-right order.
Source: Stacks 03DI and 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenLocalizedPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] (U : Y.ProEt) :=
  cbcOpenExtension Y B U ⋙ cbcOpenFinitePullback g B ⋙ cbcOpenTargetRestriction g B U

/-- beta is literally pullback of the actual counit, followed by target restriction.
Source: Stacks 03DI and 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
def cbcOpenLocalizedCounit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] (U : Y.ProEt) :
    (SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
        (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U)) ⋙ cbcOpenLocalizedPullback g B U ⟶
      cbcOpenFinitePullback g B ⋙ cbcOpenTargetRestriction g B U :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((SheafOfModules.localizedSystemAdjunction.{u + 1, u + 1, u + 1}
        (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).counit _ ≫
      (Functor.leftUnitor _).hom

/-- Continuity for the literal localized base-change functor, with no extra hypothesis.
Source: Stacks 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
instance cbcOpenSliceContinuous {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.ProEt) :
    (Over.post (X := AsSmall.up.obj U) (proEtaleModelBaseChange g)).IsContinuous
      ((proEtaleModelTopology Y).over (AsSmall.up.obj U))
      ((proEtaleModelTopology X).over
        ((proEtaleModelBaseChange g).obj (AsSmall.up.obj U))) :=
  overPost_isContinuous (proEtaleModelTopology Y) (proEtaleModelTopology X)
    (proEtaleModelBaseChange g) (AsSmall.up.obj U)

/-- The localized tensor pullback g_{U,B}^* in slice coordinates, with the restricted
canonical coefficient map, rather than a separately chosen ring structure.
Source: Stacks 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenSlicePullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] (U : Y.ProEt) :=
  SheafOfModules.pullback
    (SheafOfModules.sliceModuleRingMap (proEtaleModelBaseChange g)
      (SheafOfModules.ringedSiteModuleMap (proEtaleModelBaseChange g)
        (cbcOpenModelCoefficientMap g B)) (AsSmall.up.obj U))

/-- The canonical localized pullback comparison is the inverse mate of the
sectionwise identity direct-image square, as in the recorded ringed localization theorem.
Source: Stacks 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenSliceComparison {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] (U : Y.ProEt) :=
  SheafOfModules.sliceModulePullbackMap (proEtaleModelBaseChange g)
    (SheafOfModules.ringedSiteModuleMap (proEtaleModelBaseChange g)
      (cbcOpenModelCoefficientMap g B)) (AsSmall.up.obj U)

/-- The sheafification unit on the actual extension presheaf; its values on summands
are the generators used in both adjunction formulas below.
Source: Stacks 03DI (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenExtensionGenerator (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (U : Y.ProEt)
    (F : SheafOfModules.{u + 1}
      (((sheafCompose (proEtaleModelTopology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (cbcOpenModelCoefficient Y B)).over (AsSmall.up.obj U))) :=
  (PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).unit.app
    ((SheafOfModules.extensionByZeroPresheaf.{u + 1} _ (AsSmall.up.obj U)).obj F)

/-- An inverse-image/tensor generator [V, psi, s] tensor b: the pullback-adjunction
unit gives [V, id, s] tensor 1, restriction gives psi, and scalar multiplication gives b.
This defines sections without asserting that all sheaf sections are global generators.
Source: Stacks 03D2 and 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
def cbcOpenPullbackGenerator {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B]
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (proEtaleModelTopology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (cbcOpenModelCoefficient Y B)))
    (V : proEtaleSiteModel Y) (W : proEtaleSiteModel X)
    (psi : W ⟶ (proEtaleModelBaseChange g).obj V) (s : M.val.obj (op V))
    (b : (cbcOpenModelCoefficient X B).obj.obj (op W)) :
    ((cbcOpenFinitePullback g B).obj M).val.obj (op W) :=
  b • ((cbcOpenFinitePullback g B).obj M).val.map psi.op
    ((SheafOfModules.pullbackPushforwardAdjunction
      (SheafOfModules.ringedSiteModuleMap (proEtaleModelBaseChange g)
        (cbcOpenModelCoefficientMap g B))).unit.app M |>.val.app (op V) <| s)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open SheafOfModules in
private theorem pullbackGenerator_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B]
    {M N : SheafOfModules.{u + 1}
      ((sheafCompose (proEtaleModelTopology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (cbcOpenModelCoefficient Y B))}
    (f : M ⟶ N) (V : proEtaleSiteModel Y) (W : proEtaleSiteModel X)
    (psi : W ⟶ (proEtaleModelBaseChange g).obj V) (s : M.val.obj (op V))
    (b : (cbcOpenModelCoefficient X B).obj.obj (op W)) :
    ((cbcOpenFinitePullback g B).map f).val.app (op W)
        (cbcOpenPullbackGenerator g B M V W psi s b) =
      cbcOpenPullbackGenerator g B N V W psi (f.val.app (op V) s) b := by
  let a := SheafOfModules.pullbackPushforwardAdjunction
    (SheafOfModules.ringedSiteModuleMap (proEtaleModelBaseChange g)
      (cbcOpenModelCoefficientMap g B))
  have hn := congrArg (fun h ↦ h.val.app (op V) s) (a.unit.naturality f)
  change (a.unit.app N).val.app (op V) (f.val.app (op V) s) =
    ((cbcOpenFinitePullback g B).map f).val.app (op ((proEtaleModelBaseChange g).obj V))
      ((a.unit.app M).val.app (op V) s) at hn
  unfold cbcOpenPullbackGenerator
  rw [map_smul, PresheafOfModules.naturality_apply, ← hn]

open Classical in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open SheafOfModules in
private theorem extensionRestrict_of
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    (F : SheafOfModules.{u} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W)
    (φ : V.unop ⟶ U) (ψ : W.unop ⟶ U) (h : a.unop ≫ φ = ψ)
    (x : F.val.obj (Opposite.op (Over.mk φ))) :
    extensionByZeroPresheafRestrictAdd R U F a
        (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) =
      DirectSum.of (fun χ : W.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk χ))) ψ
        (F.val.map (Opposite.op (Over.homMk a.unop h : Over.mk ψ ⟶ Over.mk φ)) x) := by
  subst ψ
  change (DirectSum.toAddMonoid _)
    (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) = _
  rw [DirectSum.toAddMonoid_of]
  rfl


set_option backward.isDefEq.respectTransparency false in
open Classical in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open SheafOfModules in
private noncomputable def extensionSectionIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U V : C) [Subsingleton (V ⟶ U)] (φ : V ⟶ U)
    (F : SheafOfModules.{u} (R.over U)) :
    F.val.obj (op (Over.mk φ)) ≅ (extensionByZeroPresheaf R U).obj F |>.obj (op V) := by
  exact LinearEquiv.toModuleIso
    { toLinearMap := DirectSum.lof (R.obj.obj (op V)) (V ⟶ U)
        (fun ψ ↦ F.val.obj (op (Over.mk ψ))) φ
      invFun := DirectSum.component (R.obj.obj (op V)) (V ⟶ U)
        (fun ψ ↦ F.val.obj (op (Over.mk ψ))) φ
      left_inv := by
        intro x
        exact DirectSum.component.lof_self (M := fun ψ ↦ F.val.obj (op (Over.mk ψ)))
          (R.obj.obj (op V)) φ x
      right_inv := by
        intro x
        induction x using DirectSum.induction_on with
        | zero => simp
        | of ψ x =>
          have : ψ = φ := Subsingleton.elim _ _
          subst ψ
          change DirectSum.lof _ _ _ φ (DirectSum.component _ _ _ φ
            (DirectSum.lof (R.obj.obj (op V)) _
              (fun ψ ↦ F.val.obj (op (Over.mk ψ))) φ x)) = _
          rw [DirectSum.component.lof_self]
          rfl
        | add x y hx hy =>
          change DirectSum.of _ φ (x φ + y φ) = x + y
          rw [map_add]
          exact congrArg₂ (· + ·) hx hy }

set_option backward.isDefEq.respectTransparency false in
open Classical in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open SheafOfModules in
private noncomputable def extensionRestrictionIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    (hU : ∀ V : C, Subsingleton (V ⟶ U))
    (F : SheafOfModules.{u} (R.over U)) :
    ((SheafOfModules.toSheaf (R.over U)).obj F).obj ≅
      (Over.forget U).op ⋙ ((extensionByZeroPresheaf R U).obj F).presheaf := by
  refine NatIso.ofComponents (fun V ↦ ?_) ?_
  · let := hU V.unop.left
    exact (forget₂ (ModuleCat (R.obj.obj (op V.unop.left))) AddCommGrpCat).mapIso
      (extensionSectionIso R U V.unop.left V.unop.hom F)
  · intro V W a
    let := hU V.unop.left
    let := hU W.unop.left
    ext x
    change _ = extensionByZeroPresheafRestrictAdd R U F
      ((Over.forget U).op.map a) (DirectSum.of _ V.unop.hom x)
    erw [extensionRestrict_of R U F ((Over.forget U).op.map a)
      V.unop.hom W.unop.hom (by exact a.unop.w)]
    rfl

open Classical in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open SheafOfModules in
private theorem localizedUnit_formula
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (F : SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))
    (W : (Over U)ᵒᵖ) (x : F.val.obj W) :
    ((localizedSystemAdjunction.{u, u, u} R U).unit.app F).val.app W x =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
        ((extensionByZeroPresheaf _ U).obj F)).app (op W.unop.left)
          (DirectSum.lof (R.obj.obj (op W.unop.left)) (W.unop.left ⟶ U)
            (fun a ↦ F.val.obj (op (Over.mk a))) W.unop.hom x) := by
  exact (localizedSystemAdjunction_existsUnique.{u, u, u} R U).exists.choose_spec F W x

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open SheafOfModules in
private theorem localizedUnit_isIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (hU : ∀ V : C, Subsingleton (V ⟶ U))
    (F : SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) :
    IsIso ((localizedSystemAdjunction.{u, u, u} R U).unit.app F) := by
  let A := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let P := ((extensionByZeroPresheaf A U).obj F).presheaf
  let T := (Over.forget U).op ⋙ P
  have hT : Presheaf.IsSheaf (J.over U) T :=
    (Presheaf.isSheaf_of_iso_iff (extensionRestrictionIso A U hU F)).mp
      ((SheafOfModules.toSheaf _).obj F).property
  have : IsIso (toSheafify (J.over U) T) := isIso_toSheafify _ hT
  have hh := (Over.forget U).toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat.{u} (J.over U) J P
  have : IsIso (Functor.whiskerLeft (Over.forget U).op (toSheafify J P)) := by
    rw [← hh]
    infer_instance
  let η := (localizedSystemAdjunction.{u, u, u} R U).unit.app F
  have hη : ((SheafOfModules.toSheaf _).map η).hom =
      (extensionRestrictionIso A U hU F).hom ≫
        Functor.whiskerLeft (Over.forget U).op (toSheafify J P) := by
    ext V x
    exact localizedUnit_formula R U F V x
  have : IsIso ((sheafToPresheaf (J.over U) AddCommGrpCat.{u}).map
      ((SheafOfModules.toSheaf _).map η)) := by
    change IsIso (((SheafOfModules.toSheaf _).map η).hom)
    rw [hη]
    infer_instance
  have : IsIso ((SheafOfModules.toSheaf _).map η) :=
    isIso_of_reflects_iso _ (sheafToPresheaf (J.over U) AddCommGrpCat.{u})
  exact isIso_of_reflects_iso η (SheafOfModules.toSheaf _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
/-- Open localized finite pullback is the pulled-back extension counit, with its
canonical normalization on every summand. The open immersion is represented by U.hom;
its cartesian inverse image is the object `(proEtaleBaseChange g).obj U`.
Source: Stacks 03DI, 0F6Z and 04J0
(blueprint: lem-cbc-open-localized-counit-comparison).

Proof:
1. Use def-weil-proetale-inverse-image and lem-weil-proetale-weakly-etale-localization
   to identify the sites and their slices. The constant-section structure maps of
   prop-weil-pbc-proetale-constant-ring-map restrict to the same constants on the slice.
   lem-weil-pbc-localize-ringed-site-morphism gives the canonical lambda above.
2. The direct-sum Hom bijection evaluates each summand, and its inverse inserts each
   section into its summand. Compose with def-weil-presheaf-modules-sheafification.
   Applying these transpositions to identities gives exactly the unit and counit formulas.
3. Openness gives at most one arrow into U. Restricting the extension presheaf to U
   therefore leaves precisely F. The unit-compatible comparison of
   lem-cbc-sieve-slice-sheafification identifies the unit with sheafification of F;
   as F is a sheaf, this unit is invertible, including for the empty open.
4. Define alpha_F = lambda_(j_!F)^(-1) followed by g_{U,B}^*(eta_F^(-1)).
   Naturality of lambda at epsilon and j^*(epsilon) eta = id give beta = alpha lambda.
   Hence beta is invertible. Applying pullback to the summand evaluation gives the
   generator formula [V,psi,iota(s)] tensor b |-> [V,psi,s] tensor b, using precisely
   def-pur-sheaf-tensor-product; balancing and sheafification preserve this equality. -/
theorem cbcOpenLocalizedCounitComparison {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] [Finite B] (U : Y.ProEt) [IsOpenImmersion U.hom] :
    IsIso (cbcOpenLocalizedCounit g B U) ∧
    IsIso (cbcOpenSliceComparison g B U) ∧
    ∃ alpha : cbcOpenLocalizedPullback g B U ≅ cbcOpenSlicePullback g B U,
      (∀ F, alpha.inv.app F =
        (cbcOpenSlicePullback g B U).map
          (((SheafOfModules.localizedSystemAdjunction.{u + 1, u + 1, u + 1}
            (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).unit.app F) ≫
          (cbcOpenSliceComparison g B U).app ((cbcOpenExtension Y B U).obj F)) ∧
      (∀ M, (cbcOpenLocalizedCounit g B U).app M =
        alpha.hom.app (((SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
            (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).obj M) ≫
          (cbcOpenSliceComparison g B U).app M) ∧
      (∀ (F : SheafOfModules.{u + 1}
          (((sheafCompose (proEtaleModelTopology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (cbcOpenModelCoefficient Y B)).over (AsSmall.up.obj U)))
        (W : Over (AsSmall.up.obj U)) (s : F.val.obj (op W)),
        (((SheafOfModules.localizedSystemAdjunction.{u + 1, u + 1, u + 1}
            (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).unit.app F).val.app (op W) s =
          (cbcOpenExtensionGenerator Y B U F).app (op W.left)
            (DirectSum.lof ((cbcOpenModelCoefficient Y B).obj.obj (op W.left))
              (W.left ⟶ AsSmall.up.obj U) (fun a ↦ F.val.obj (op (Over.mk a))) W.hom s)) ∧
      (∀ (M : SheafOfModules.{u + 1}
          ((sheafCompose (proEtaleModelTopology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (cbcOpenModelCoefficient Y B)))
        (W : Over (AsSmall.up.obj U)) (s : M.val.obj (op W.left)),
        (((SheafOfModules.localizedSystemAdjunction.{u + 1, u + 1, u + 1}
            (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).counit.app M).val.app (op W.left)
          ((cbcOpenExtensionGenerator Y B U
            (((SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
              (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).obj M)).app
            (op W.left)
              (DirectSum.lof ((cbcOpenModelCoefficient Y B).obj.obj (op W.left))
                (W.left ⟶ AsSmall.up.obj U)
                (fun a ↦ (((SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
                    (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).obj M).val.obj
                      (op (Over.mk a)))
                W.hom s)) = s) ∧
      (∀ (M : SheafOfModules.{u + 1}
          ((sheafCompose (proEtaleModelTopology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (cbcOpenModelCoefficient Y B)))
        (V : proEtaleSiteModel Y) (phi : V ⟶ AsSmall.up.obj U)
        (W : Over ((proEtaleModelBaseChange g).obj (AsSmall.up.obj U)))
        (psi : W ⟶ (Over.post (proEtaleModelBaseChange g)).obj (Over.mk phi))
        (s : M.val.obj (op V)) (b : (cbcOpenModelCoefficient X B).obj.obj (op W.left)),
        ((cbcOpenLocalizedCounit g B U).app M).val.app (op W)
          (cbcOpenPullbackGenerator g B
            ((cbcOpenExtension Y B U).obj
              (((SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
                (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).obj M))
            V W.left psi.left
            ((cbcOpenExtensionGenerator Y B U
              (((SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
                (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).obj M)).app
              (op V) (DirectSum.lof ((cbcOpenModelCoefficient Y B).obj.obj (op V))
                (V ⟶ AsSmall.up.obj U)
                (fun a ↦ (((SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
                    (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).obj M).val.obj
                      (op (Over.mk a)))
                phi s)) b) =
          cbcOpenPullbackGenerator g B M V W.left psi.left s b) := by
  let R := SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
    (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U)
  let L := cbcOpenExtension Y B U
  let P := cbcOpenFinitePullback g B
  let T := cbcOpenTargetRestriction g B U
  let S := cbcOpenSlicePullback g B U
  let adj : L ⊣ R := SheafOfModules.localizedSystemAdjunction.{u + 1, u + 1, u + 1}
    (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U)
  let lam : R ⋙ S ⟶ P ⋙ T := cbcOpenSliceComparison g B U
  have hU (V : proEtaleSiteModel Y) : Subsingleton (V ⟶ AsSmall.up.obj U) := by
    constructor
    intro a b
    apply ULift.ext
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono U.hom).mp
    exact (MorphismProperty.Over.w (AsSmall.down.map a)).trans
      (MorphismProperty.Over.w (AsSmall.down.map b)).symm
  have hu (F) : IsIso (adj.unit.app F) :=
    localizedUnit_isIso (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U) hU F
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  let : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  have : PreservesFiniteLimits (proEtaleModelBaseChange g) := by
    change PreservesFiniteLimits
      ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt) ⋙ proEtaleBaseChange g ⋙ AsSmall.up)
    infer_instance
  have : RepresentablyFlat (proEtaleModelBaseChange g) := flat_of_preservesFiniteLimits _
  have : ReflectsLimits (CategoryTheory.forget (Type (u + 1))) :=
    reflectsLimits_of_reflectsIsomorphisms
  have : PreservesFiniteLimits
      ((proEtaleModelBaseChange g).op.lan :
        ((proEtaleSiteModel Y)ᵒᵖ ⥤ Type (u + 1)) ⥤
          (proEtaleSiteModel X)ᵒᵖ ⥤ Type (u + 1)) :=
    lan_preservesFiniteLimits_of_flat (Type (u + 1)) (proEtaleModelBaseChange g)
  have : PreservesFiniteLimits
      ((proEtaleModelBaseChange g).sheafPullback (Type (u + 1))
        (proEtaleModelTopology Y) (proEtaleModelTopology X)) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits
      (proEtaleModelBaseChange g) (Type (u + 1))
      (proEtaleModelTopology Y) (proEtaleModelTopology X)
  have hl : IsIso lam := SheafOfModules.sliceModulePullbackMap_isIso
    (proEtaleModelBaseChange g) (cbcOpenModelCoefficientMap g B) (AsSmall.up.obj U)
  let alpha : L ⋙ P ⋙ T ≅ S :=
    (Functor.isoWhiskerLeft L (asIso lam)).symm ≪≫
      (Functor.associator L R S).symm ≪≫
        Functor.isoWhiskerRight (asIso adj.unit).symm S ≪≫ Functor.leftUnitor S
  have ha (F) : alpha.inv.app F =
      S.map (adj.unit.app F) ≫ lam.app (L.obj F) := by
    simp [alpha]
  have hb (M) : (cbcOpenLocalizedCounit g B U).app M =
      alpha.hom.app (R.obj M) ≫ lam.app M := by
    have hn := lam.naturality (adj.counit.app M)
    change S.map (R.map (adj.counit.app M)) ≫ lam.app M =
      lam.app (L.obj (R.obj M)) ≫ T.map (P.map (adj.counit.app M)) at hn
    apply (cancel_epi (alpha.inv.app (R.obj M))).mp
    rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp, ha]
    change (S.map (adj.unit.app (R.obj M)) ≫ lam.app (L.obj (R.obj M))) ≫
      T.map (P.map (adj.counit.app M)) = lam.app M
    rw [Category.assoc, ← hn, ← Category.assoc, ← S.map_comp,
      adj.right_triangle_components]
    erw [S.map_id, Category.id_comp]
  have hi : IsIso (cbcOpenLocalizedCounit g B U) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [hb]
    infer_instance
  refine ⟨hi, hl, alpha, ha, hb, ?_, ?_, ?_⟩
  · intro F W s
    exact localizedUnit_formula (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U) F (op W) s
  · intro M W s
    have ht := congrArg (fun f ↦ f.val.app (op W) s) (adj.right_triangle_components M)
    change (adj.counit.app M).val.app (op W.left)
      ((adj.unit.app (R.obj M)).val.app (op W) s) = s at ht
    rw [localizedUnit_formula] at ht
    exact ht
  · intro M V phi W psi s b
    let t := (cbcOpenExtensionGenerator Y B U (R.obj M)).app (op V)
      (DirectSum.lof ((cbcOpenModelCoefficient Y B).obj.obj (op V))
        (V ⟶ AsSmall.up.obj U) (fun a ↦ (R.obj M).val.obj (op (Over.mk a))) phi s)
    have ht := congrArg (fun f ↦ f.val.app (op (Over.mk phi)) s)
      (adj.right_triangle_components M)
    change (adj.counit.app M).val.app (op V)
      ((adj.unit.app (R.obj M)).val.app (op (Over.mk phi)) s) = s at ht
    rw [localizedUnit_formula] at ht
    change (adj.counit.app M).val.app (op V) t = s at ht
    exact (pullbackGenerator_naturality g B (adj.counit.app M) V W.left psi.left t b).trans
      (congrArg (fun x ↦ cbcOpenPullbackGenerator g B M V W.left psi.left x b) ht)

end AlgebraicGeometry.Scheme
