module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.OrdinaryCompletedIntegralPullback
import all Sheaf.Paper.StrictPerfectRingedPullbackModel
import all Sheaf.Paper.ScalarPerfectFiniteFree
import all Sheaf.Paper.OrdinaryIntegralPullbackConstruction
import Mathlib.RingTheory.Finiteness.Projective
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients

/-!
# Normalized finite-projective models under ordinary pullback

Source: Stacks Project, Tags 08H3, 06YQ and 06YY; Modules on Sites, Section 03EK;
Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15.
(blueprint: lem-tw-finite-projective-model-pullback).

All tensors and derived functors here are ordinary, before completion. The limit
coefficient sheaf and its quotient projections are the published constructions.
The scalar ring and module pullback are the published ordinary integral constructions.
Schemes and the coefficient extension are in universe u; their small pro-etale
sites retain object universe u+1 and morphism universe u.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralTowerHasDerivedCategory
attribute [-instance] WeilConjectures.integralCoefficientRingSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures.FiniteProjectivePullback

private theorem proofCommSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} T

private theorem proofAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} T

private theorem proofAbWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  (proofAbSheafify T).isRightAdjoint

private theorem proofAbLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} T

private theorem proofCompose (T : Scheme.{u}) :
    (ProEt.topology T).HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  infer_instance

attribute [local instance] proofCommSheafify proofAbSheafify proofAbWeakSheafify
  proofAbLocallyBijective proofCompose

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical constant scalar map, retaining commutativity for sheaf tensors.
Source: the limit lift of the constant quotient cone
(blueprint: lem-tw-finite-projective-model-pullback). -/
def scalar (T : Scheme.{u}) :
    SheafOfModules.scalarPerfectRing.{u + 1, u, u + 1}
      (ProEt.topology T) (PbcIntegralRing l E) ⟶
      completedIntegralCommRingSheafUnrestricted.{u, u} l E T :=
  (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
    (integralConstantToCompletionOfUniverses.{u, u} l E T)

/-- Ordinary constant realization P ↦ B_T tensor_R underline P, including linear maps.
Source: Stacks 03CY and 03EK; Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-finite-projective-model-pullback). -/
def model (T : Scheme.{u}) :
    ModuleCat.{u + 1} (PbcIntegralRing l E) ⥤ integralTowerModules.{u, u} l E T :=
  SheafOfModules.scalarPerfectFunctor.{u + 1, u, u + 1}
    (ProEt.topology T) (PbcIntegralRing l E) (scalar l E T)

/-- A pure tensor b tensor x, using the actual constant and tensor sheafification units.
Source: Stacks 03CY and 03EK
(blueprint: lem-tw-finite-projective-model-pullback). -/
def modelSection (T : Scheme.{u}) (P : ModuleCat.{u + 1} (PbcIntegralRing l E))
    (W : T.ProEtᵒᵖ) (b : (completedIntegralCommRingSheafUnrestricted.{u, u} l E T).obj.obj W)
    (x : P) : ((model l E T).obj P).val.obj W :=
  SheafOfModules.scalarExtensionSection (scalar l E T)
    ((SheafOfModules.scalarPerfectConstantFunctor.{u + 1, u, u + 1} (ProEt.topology T)
      (PbcIntegralRing l E)).obj P) W b
    (SheafOfModules.scalarPerfectConstantSection.{u + 1, u, u + 1} (ProEt.topology T)
      (PbcIntegralRing l E) P W x)

private theorem retract_naturality {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : C} (i : X ⟶ Y) (p : Y ⟶ X)
    (h : i ≫ p = 𝟙 X) :
    e.hom.app X = F.map i ≫ e.hom.app Y ≫ G.map p ∧
    e.inv.app X = G.map i ≫ e.inv.app Y ≫ F.map p ∧
    e.hom.app X ≫ G.map i = F.map i ≫ e.hom.app Y := by
  refine ⟨?_, ?_, (e.hom.naturality i).symm⟩
  · rw [e.hom.naturality_assoc, ← G.map_comp, h, G.map_id, Category.comp_id]
  · rw [e.inv.naturality_assoc, ← F.map_comp, h, F.map_id, Category.comp_id]

private theorem modelSection_smul (T : Scheme.{u})
    (P : ModuleCat.{u + 1} (PbcIntegralRing l E)) (W : T.ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted.{u, u} l E T).obj.obj W) (x : P) :
    modelSection l E T P W b x = b • modelSection l E T P W 1 x := by
  dsimp only [model, SheafOfModules.scalarPerfectFunctor, Functor.comp_obj,
    SheafOfModules.scalarPerfectExtensionFunctor, modelSection]
  simpa only [mul_one] using
    (SheafOfModules.scalarExtensionSection_smul (scalar l E T) _ W b 1 _).symm

/-- Additivity of the published constant realization.
Source: Stacks 03CY and 03EK
(blueprint: lem-tw-finite-projective-model-pullback).
Proof: compose the additive constant-module and scalar-extension functors. -/
@[instance] theorem model_additive (T : Scheme.{u}) : (model l E T).Additive := by
  exact SheafOfModules.scalarPerfectFunctor_additive _ _ _

/-- The inverse-image generator 1 tensor m from the specified adjunction unit.
Source: Stacks 03D2
(blueprint: lem-tw-finite-projective-model-pullback). -/
def generator {V U : Scheme.{u}} (v : V ⟶ U) (M : integralTowerModules.{u, u} l E U)
    (W : U.ProEt) (x : M.val.obj (op W)) :
    ((ordinaryIntegralModulePull l E v).obj M).val.obj (op ((proEtaleBaseChange v).obj W)) :=
  (((ordinaryIntegralModuleAdjunction l E v).unit.app M).val.app (op W)) x

/-- The existing full subcategory of finite projective scalar modules.
Source: Stacks 08G5, finite-free direct summands
(blueprint: lem-tw-finite-projective-model-pullback). -/
abbrev Projectives := ObjectProperty.FullSubcategory
  (fun P : ModuleCat.{u + 1} (PbcIntegralRing l E) ↦
    Module.Finite (PbcIntegralRing l E) P ∧ Module.Projective (PbcIntegralRing l E) P)

/-- Restrict the scalar realization to finite projective modules, with every linear map.
Source: Stacks 03EK and 08H3
(blueprint: lem-tw-finite-projective-model-pullback). -/
def projectiveModel (T : Scheme.{u}) : Projectives l E ⥤ integralTowerModules.{u, u} l E T :=
  ObjectProperty.ι _ ⋙ model l E T

private def modelUnitIso (T : Scheme.{u}) :
    (model l E T).obj (ModuleCat.of (PbcIntegralRing l E) (PbcIntegralRing l E)) ≅
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T) := by
  have := SheafOfModules.constantUnitHom_isIso (ProEt.topology T) (PbcIntegralRing l E)
  exact (SheafOfModules.scalarPerfectExtensionFunctor (ProEt.topology T)
    (scalar l E T)).mapIso
      (asIso (SheafOfModules.constantUnitHom (ProEt.topology T) (PbcIntegralRing l E))) ≪≫
        SheafOfModules.scalarExtensionUnitIso (scalar l E T)

private def modelFreeIso (T : Scheme.{u}) (n : ℕ) :
    (model l E T).obj (ModuleCat.of (PbcIntegralRing l E) (Fin n → PbcIntegralRing l E)) ≅
      ∏ᶜ fun _ : Fin n ↦
        SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T) :=
  (model l E T).mapIso (ModuleCat.piIsoPi
    (fun _ : Fin n ↦ ModuleCat.of (PbcIntegralRing l E) (PbcIntegralRing l E))).symm ≪≫
      PreservesProduct.iso (model l E T)
        (fun _ : Fin n ↦ ModuleCat.of (PbcIntegralRing l E) (PbcIntegralRing l E)) ≪≫
      Pi.mapIso (fun _ : Fin n ↦ modelUnitIso l E T)

private def constantSections (T : Scheme.{u}) (W : T.ProEt) :
    SheafOfModules.{u + 1} (integralConstantRingOfUniverses.{u, u} l E T) ⥤
      ModuleCat.{u + 1} (PbcIntegralRing l E) :=
  SheafOfModules.forget (integralConstantRingOfUniverses.{u, u} l E T) ⋙
    PresheafOfModules.restrictScalars
      (SheafOfModules.scalarPerfectRingUnit (ProEt.topology T) (PbcIntegralRing l E)) ⋙
      PresheafOfModules.evaluation _ (op W)

private def constantPresheafHomEquiv (T : Scheme.{u}) (W : T.ProEt)
    (hW : IsTerminal W) (M : ModuleCat.{u + 1} (PbcIntegralRing l E))
    (P : PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (PbcIntegralRing l E)))) :
    ((SheafOfModules.scalarPerfectConstantPresheaf (C := T.ProEt)
      (PbcIntegralRing l E)).obj M ⟶ P) ≃ (M ⟶ P.obj (op W)) where
  toFun h := h.app _
  invFun h :=
    { app := fun U ↦ h ≫ P.map (hW.from U.unop).op
      naturality := by
        intro U V a
        ext m
        change P.map (hW.from V.unop).op (h m) =
          P.map a (P.map (hW.from U.unop).op (h m))
        rw [← P.map_comp_apply]
        have he : (hW.from V.unop).op = (hW.from U.unop).op ≫ a :=
          congrArg Quiver.Hom.op (hW.hom_ext (hW.from V.unop)
            (a.unop ≫ hW.from U.unop))
        rw [he] }
  left_inv h := by
    ext U m
    exact (PresheafOfModules.naturality_apply h (hW.from U.unop).op m).symm
  right_inv h := by
    ext m
    change P.map (hW.from W).op (h m) = h m
    rw [show hW.from W = 𝟙 W from hW.hom_ext _ _, op_id]
    exact ConcreteCategory.congr_hom (P.presheaf.map_id _) (h m)

private def constantAdjunction (T : Scheme.{u}) (W : T.ProEt) (hW : IsTerminal W) :
    SheafOfModules.scalarPerfectConstantFunctor (ProEt.topology T) (PbcIntegralRing l E) ⊣
      constantSections l E T W := by
  have := (SheafOfModules.scalarPerfectRingUnit_locallyBijective
    (ProEt.topology T) (PbcIntegralRing l E)).1
  have := (SheafOfModules.scalarPerfectRingUnit_locallyBijective
    (ProEt.topology T) (PbcIntegralRing l E)).2
  let adj : SheafOfModules.scalarPerfectConstantPresheaf (C := T.ProEt)
      (PbcIntegralRing l E) ⊣ PresheafOfModules.evaluation _ (op W) :=
    Adjunction.mkOfHomEquiv
      { homEquiv := constantPresheafHomEquiv l E T W hW
        homEquiv_naturality_left_symm := by intros; ext U m; rfl
        homEquiv_naturality_right := by intros; rfl }
  exact adj.comp (PresheafOfModules.sheafificationAdjunction
    (SheafOfModules.scalarPerfectRingUnit (ProEt.topology T) (PbcIntegralRing l E)))

attribute [local irreducible] SheafOfModules.changeOfRingsMapOfUniverses

namespace ScalarAdjunction
open SheafOfModules
open scoped TensorProduct ChangeOfRings
universe a b r
variable {D : Type a} [Category.{b} D] [EssentiallySmall.{r} D]
  {K : GrothendieckTopology D} [HasSheafify K CommRingCat.{r}]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]

private abbrev ringSheaf (A : Sheaf K CommRingCat.{r}) :=
  (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj A

private noncomputable abbrev restriction
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (ringSheaf S) ⥤ SheafOfModules.{r} (ringSheaf A) :=
  SheafOfModules.restrictScalars.{r}
    ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).map c)

omit [HasSheafify K CommRingCat.{r}] [EssentiallySmall.{r} D] in
private theorem tensorRestriction_tmul
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) (M : SheafOfModules.{r} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheafOfUniverses.{b, a, r, r} c M).map i
        (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  changeOfRingsMap_tmulOfUniverses c M i s m

private noncomputable def tensorPresheafFunctor
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (ringSheaf A) ⥤ PresheafOfModules.{r} (ringSheaf S).obj where
  obj M := changeOfRingsPresheafOfUniverses.{b, a, r, r} c M
  map {M N} f :=
    show changeOfRingsPresheafOfUniverses.{b, a, r, r} c M ⟶
      changeOfRingsPresheafOfUniverses.{b, a, r, r} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturalityOfUniverses.{b, a, r, r} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (ringSheaf A) ⥤ SheafOfModules.{r} (ringSheaf S) :=
  scalarPerfectExtensionFunctor.{a, b, r} K c

private noncomputable def tensorToRestriction
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (H : SheafOfModules.{r} (ringSheaf S))
    (f : changeOfRingsPresheafOfUniverses.{b, a, r, r} c M ⟶ H.val) :
    M ⟶ (restriction c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (H : SheafOfModules.{r} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) :
    changeOfRingsPresheafOfUniverses.{b, a, r, r} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheafOfUniverses.{b, a, r, r} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (H : SheafOfModules.{r} (ringSheaf S)) :
    (changeOfRingsPresheafOfUniverses.{b, a, r, r} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (H : SheafOfModules.{r} (ringSheaf S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

-- These are naturality statements for the explicit universe-aware presheaf
-- changeOfRingsPresheafOfUniverses and scalarPerfectExtensionFunctor. The older
-- CoefficientOrdinaryProof and ScalarReductionProof use changeOfRingsPresheaf.
private theorem tensorHomEquiv_naturality_left
    {D : Type a} [Category.{b} D] [EssentiallySmall.{r} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    {M N : SheafOfModules.{r} (ringSheaf A)} (a : M ⟶ N)
    (H : SheafOfModules.{r} (ringSheaf S))
    (f : (scalarPerfectExtensionFunctor.{a, b, r} K c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv
    (changeOfRingsPresheafOfUniverses.{b, a, r, r} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {D : Type a} [Category.{b} D] [EssentiallySmall.{r} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A))
    {H H' : SheafOfModules.{r} (ringSheaf S)}
    (f : (scalarPerfectExtensionFunctor.{a, b, r} K c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (restriction c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def tensorAdjunction
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) : tensorFunctor c ⊣ restriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }


end ScalarAdjunction

private def modelSections (T : Scheme.{u}) (W : T.ProEt) :
    integralTowerModules.{u, u} l E T ⥤ ModuleCat.{u + 1} (PbcIntegralRing l E) :=
  ScalarAdjunction.restriction.{u + 1, u, u + 1}
      (D := T.ProEt) (K := ProEt.topology T) (scalar l E T) ⋙ constantSections l E T W

private def modelAdjunction (T : Scheme.{u}) (W : T.ProEt) (hW : IsTerminal W) :
    model l E T ⊣ modelSections l E T W :=
  (constantAdjunction l E T W hW).comp
    (ScalarAdjunction.tensorAdjunction.{u + 1, u, u + 1} (scalar l E T))

attribute [local irreducible] ordinaryIntegralModulePull ordinaryIntegralDirectRingMap
  SheafOfModules.changeOfRingsOfUniverses SheafOfModules.changeOfRingsHomOfUniverses
  constantSheaf HasDerivedCategory.standard

private theorem ordinaryPull_preserves_good_quasiIso {V U : Scheme.{u}} (v : V ⟶ U)
    {P Q : CochainComplex (integralTowerModules.{u, u} l E U) ℤ} (f : P ⟶ Q)
    (hp : integralOperationsGoodComplex l E U P)
    (hq : integralOperationsGoodComplex l E U Q) (hf : QuasiIso f) :
    QuasiIso (((ordinaryIntegralModulePull l E v).mapHomologicalComplex (.up ℤ)).map f) := by
  let := HasDerivedCategory.standard (integralTowerModules.{u, u} l E U)
  let := HasDerivedCategory.standard (integralTowerModules.{u, u} l E V)
  have hP := ordinaryIntegralPullComplexCounit_isIso l E v ⟨P, hp⟩
  have hQ := ordinaryIntegralPullComplexCounit_isIso l E v ⟨Q, hq⟩
  have := hf
  let c := SheafOfModules.ringedPullbackComplexComparison
    (ordinaryIntegralModulePull l E v) (ordinaryIntegralDerivedPull l E v)
    (ordinaryIntegralPullCounit l E v)
  have hn := c.naturality f
  dsimp only [Functor.comp_map] at hn
  have : IsIso (c.app P) := hP
  have : IsIso (c.app Q) := hQ
  have : IsIso (c.app P ≫ DerivedCategory.Q.map
      (((ordinaryIntegralModulePull l E v).mapHomologicalComplex (.up ℤ)).map f)) := by
    rw [← hn]
    infer_instance
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
    (IsIso.of_isIso_comp_left (c.app P) _)

private theorem ordinaryPull_comparison_iso {V U : Scheme.{u}} (v : V ⟶ U)
    [HasDerivedCategory.{w} (integralTowerModules.{u, u} l E U)]
    [HasDerivedCategory.{w} (integralTowerModules.{u, u} l E V)]
    (LF : DerivedCategory (integralTowerModules.{u, u} l E U) ⥤
      DerivedCategory (integralTowerModules.{u, u} l E V))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      (ordinaryIntegralModulePull l E v).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (integralTowerModules.{u, u} l E U) (.up ℤ))]
    (P : CochainComplex (integralTowerModules.{u, u} l E U) ℤ)
    (hp : integralOperationsGoodComplex l E U P) :
    IsIso ((SheafOfModules.ringedPullbackComplexComparison
      (ordinaryIntegralModulePull l E v) LF ε).app P) := by
  classical
  let A := integralTowerModules.{u, u} l E U
  let B := integralTowerModules.{u, u} l E V
  let H := HomotopyCategory.quotient A (.up ℤ)
  let F := (ordinaryIntegralModulePull l E v).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let K : Set (HomotopyCategory A (.up ℤ)) :=
    {X | ∃ P : CochainComplex A ℤ, H.obj P = X ∧ integralOperationsGoodComplex l E U P}
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (a : X' ⟶ X),
        X' ∈ K ∧ HomotopyCategory.quasiIso A (.up ℤ) a := by
    intro X
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Q, f, hq, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
    refine ⟨H.obj Q, H.map f, ⟨Q, rfl, hq, ?_⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
    intro n
    exact (CategoryTheory.exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E U) (Q.X n)).symm (hflat n)
  have hinv : ∀ (X X' : HomotopyCategory A (.up ℤ)) (a : X ⟶ X'),
      X ∈ K → X' ∈ K → HomotopyCategory.quasiIso A (.up ℤ) a → IsIso (F.map a) := by
    intro X X' a hX hX' ha
    obtain ⟨Q, rfl, hq⟩ := hX
    obtain ⟨Q', rfl, hq'⟩ := hX'
    obtain ⟨a, rfl⟩ := H.map_surjective a
    have ht := ordinaryPull_preserves_good_quasiIso l E v a hq hq'
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 ha)
    change IsIso (DerivedCategory.Qh.map
      (((ordinaryIntegralModulePull l E v).mapHomotopyCategory (.up ℤ)).map (H.map a)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
  obtain ⟨_, LF', ε', hLF', _, hε'⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F K hres hinv
  have := hLF'
  let e := Functor.leftDerivedNatIso LF' LF ε' ε
    (HomotopyCategory.quasiIso A (.up ℤ)) (Iso.refl F)
  have : IsIso (ε'.app (H.obj P)) := hε' (H.obj P) ⟨P, rfl, hp⟩
  have hfac : e.hom.app (DerivedCategory.Qh.obj (H.obj P)) ≫ ε.app (H.obj P) =
      ε'.app (H.obj P) := by
    simp [e, Functor.leftDerivedNatIso, Functor.leftDerivedNatTrans_app]
  have heps : IsIso (ε.app (H.obj P)) := by
    have : IsIso (e.hom.app (DerivedCategory.Qh.obj (H.obj P)) ≫ ε.app (H.obj P)) := by
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (e.hom.app (DerivedCategory.Qh.obj (H.obj P))) (ε.app (H.obj P))
  dsimp only [SheafOfModules.ringedPullbackComplexComparison, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

private theorem model_flat (T : Scheme.{u})
    (P : ModuleCat.{u + 1} (PbcIntegralRing l E))
    [Module.Finite (PbcIntegralRing l E) P]
    [Module.Projective (PbcIntegralRing l E) P] :
    SheafOfModules.IsFlatOnSite
      (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      ((model l E T).obj P) := by
  obtain ⟨n, p, i, _, _, h⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (PbcIntegralRing l E) P
  let i' : P ⟶ ModuleCat.of (PbcIntegralRing l E) (Fin n → PbcIntegralRing l E) :=
    ModuleCat.ofHom i
  let p' : ModuleCat.of (PbcIntegralRing l E) (Fin n → PbcIntegralRing l E) ⟶ P :=
    ModuleCat.ofHom p
  have hip : i' ≫ p' = 𝟙 P := ModuleCat.hom_ext h
  apply SheafOfModules.flat_finiteFree_retract
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E T) _ n
    ((model l E T).map i' ≫ (modelFreeIso l E T n).hom)
    ((modelFreeIso l E T n).inv ≫ (model l E T).map p')
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hip]
  exact (model l E T).map_id P

private theorem scalar_square {V U : Scheme.{u}} (v : V ⟶ U) :
    integralConstantToCompletionOfUniverses.{u, u} l E U ≫
        ordinaryIntegralDirectRingMap l E v =
      (sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (coefficientProEtaleDirectRingMap.{u, u} v (CommRingCat.of (PbcIntegralRing l E))) ≫
      (proEtaleSheafDirectImage v RingCat.{u + 1}).map
        (integralConstantToCompletionOfUniverses.{u, u} l E V) := by
  let G := proEtaleSheafDirectImage v RingCat.{u + 1}
  apply (isLimitOfPreserves G (limit.isLimit (integralCoefficientSheafSystem l E V))).hom_ext
  intro n
  have hρ := (ordinaryIntegralDirectRingMap_existsUnique l E v).exists.choose_spec n.unop
  have hρ' : ordinaryIntegralDirectRingMap l E v ≫
      G.map (limit.π (integralCoefficientSheafSystem l E V) n) =
    limit.π (integralCoefficientSheafSystem l E U) n ≫
      ordinaryIntegralFiniteDirectRingMap l E v n.unop := by
    unfold ordinaryIntegralDirectRingMap
    exact hρ
  change _ ≫ G.map (limit.π (integralCoefficientSheafSystem l E V) n) =
    _ ≫ G.map (limit.π (integralCoefficientSheafSystem l E V) n)
  rw [Category.assoc, hρ', ← Category.assoc]
  have hq (T : Scheme.{u}) : integralConstantToCompletionOfUniverses l E T ≫
      limit.π (integralCoefficientSheafSystem l E T) n =
      integralConstantQuotientOfUniverses l E T n.unop := limit.lift_π _ _
  rw [hq U, Category.assoc, ← G.map_comp, hq V]
  have hh := congrArg
    ((sheafCompose (ProEt.topology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
    (ordinaryConstantMap_naturality v (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1))).comp
          (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))))
  simp only [Functor.map_comp] at hh
  ext W x
  exact congrArg (fun f ↦ f.hom.app W x) hh

attribute [local irreducible] limit
attribute [local semireducible] constantSheaf

private theorem scalar_constant_square {V U : Scheme.{u}} (v : V ⟶ U)
    (W : U.ProEt) (r : PbcIntegralRing l E) :
    (ordinaryIntegralDirectRingMap l E v).hom.app (op W)
      ((scalar l E U).hom.app (op W)
        ((SheafOfModules.scalarPerfectRingUnit (ProEt.topology U)
          (PbcIntegralRing l E)).app (op W) r)) =
      (scalar l E V).hom.app (op ((proEtaleBaseChange v).obj W))
        ((SheafOfModules.scalarPerfectRingUnit (ProEt.topology V)
          (PbcIntegralRing l E)).app (op ((proEtaleBaseChange v).obj W)) r) := by
  have hs (T : Scheme.{u}) :
      (sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalar l E T) =
        integralConstantToCompletionOfUniverses l E T := Functor.map_preimage _ _
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app (op W)) (scalar_square l E v))
    ((SheafOfModules.scalarPerfectRingUnit (ProEt.topology U)
      (PbcIntegralRing l E)).app (op W) r)
  have hu := congrArg (fun f : CommRingCat.of (PbcIntegralRing l E) ⟶
      ((constantSheaf (ProEt.topology V) CommRingCat.{u + 1}).obj
        (CommRingCat.of (PbcIntegralRing l E))).obj.obj
          (op ((proEtaleBaseChange v).obj W)) ↦ f.hom r)
    (ordinaryConstantUnit v (CommRingCat.of (PbcIntegralRing l E)) (op W))
  change (ordinaryIntegralDirectRingMap l E v).hom.app (op W)
      ((integralConstantToCompletionOfUniverses l E U).hom.app (op W) _) =
    (integralConstantToCompletionOfUniverses l E V).hom.app
      (op ((proEtaleBaseChange v).obj W)) _ at h
  rw [← hs U, ← hs V] at h
  exact h.trans (congrArg ((scalar l E V).hom.app
    (op ((proEtaleBaseChange v).obj W))) hu)

attribute [local irreducible] constantSheaf

private def modelSectionsPushIso {V U : Scheme.{u}} (v : V ⟶ U) (W : U.ProEt) :
    ordinaryIntegralModulePush l E v ⋙ modelSections l E U W ≅
      modelSections l E V ((proEtaleBaseChange v).obj W) :=
  NatIso.ofComponents (fun M ↦
    (show ((ordinaryIntegralModulePush l E v ⋙ modelSections l E U W).obj M :
        Type (u + 1)) ≃ₗ[PbcIntegralRing l E]
        (modelSections l E V ((proEtaleBaseChange v).obj W)).obj M from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ congrArg (fun a ↦ a • (show M.val.obj
          (op ((proEtaleBaseChange v).obj W)) from x))
          (scalar_constant_square l E v W r) }).toModuleIso)
    (by intros; ext x; rfl)

private theorem modelAdjunction_apply (T : Scheme.{u}) (W : T.ProEt)
    (hW : IsTerminal W) (P : ModuleCat.{u + 1} (PbcIntegralRing l E))
    (M : integralTowerModules.{u, u} l E T) (f : (model l E T).obj P ⟶ M) (x : P) :
    (modelAdjunction l E T W hW).homEquiv P M f x =
      f.val.app (op W) (modelSection l E T P (op W) 1 x) := by
  rfl

attribute [local irreducible] SheafOfModules.scalarExtensionSection

private def allComparison {V U : Scheme.{u}} (v : V ⟶ U) :
    model l E U ⋙ ordinaryIntegralModulePull l E v ≅ model l E V :=
  Adjunction.leftAdjointUniq
    ((modelAdjunction l E U (⊤_ U.ProEt) terminalIsTerminal).comp
      (ordinaryIntegralModuleAdjunction l E v))
    ((modelAdjunction l E V ((proEtaleBaseChange v).obj (⊤_ U.ProEt))
      (terminalIsTerminal.isTerminalObj (proEtaleBaseChange v) (⊤_ U.ProEt))).ofNatIsoRight
      (modelSectionsPushIso l E v (⊤_ U.ProEt)).symm)

private theorem modelSection_restrict (T : Scheme.{u})
    (P : ModuleCat.{u + 1} (PbcIntegralRing l E))
    {W W' : T.ProEtᵒᵖ} (f : W ⟶ W') (x : P) :
    ((model l E T).obj P).val.map f (modelSection l E T P W 1 x) =
      modelSection l E T P W' 1 x := by
  have := (SheafOfModules.scalarPerfectRingUnit_locallyBijective
    (ProEt.topology T) (PbcIntegralRing l E)).1
  have := (SheafOfModules.scalarPerfectRingUnit_locallyBijective
    (ProEt.topology T) (PbcIntegralRing l E)).2
  have h := SheafOfModules.scalarExtensionSection_naturality (scalar l E T)
    ((SheafOfModules.scalarPerfectConstantFunctor (ProEt.topology T)
      (PbcIntegralRing l E)).obj P) f 1
    (SheafOfModules.scalarPerfectConstantSection (ProEt.topology T)
      (PbcIntegralRing l E) P W x)
  have hc := PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction
      (SheafOfModules.scalarPerfectRingUnit (ProEt.topology T) (PbcIntegralRing l E))).unit.app
      ((SheafOfModules.scalarPerfectConstantPresheaf (C := T.ProEt)
        (PbcIntegralRing l E)).obj P)) f x
  change SheafOfModules.scalarPerfectConstantSection (ProEt.topology T)
      (PbcIntegralRing l E) P W' x =
    ((SheafOfModules.scalarPerfectConstantFunctor (ProEt.topology T)
      (PbcIntegralRing l E)).obj P).val.map f
      (SheafOfModules.scalarPerfectConstantSection (ProEt.topology T)
        (PbcIntegralRing l E) P W x) at hc
  rw [map_one] at h
  exact h.trans (congrArg (SheafOfModules.scalarExtensionSection (scalar l E T)
    ((SheafOfModules.scalarPerfectConstantFunctor (ProEt.topology T)
      (PbcIntegralRing l E)).obj P) W' 1) hc.symm)

private theorem allComparison_terminal {V U : Scheme.{u}} (v : V ⟶ U)
    (P : ModuleCat.{u + 1} (PbcIntegralRing l E)) (x : P) :
    (((allComparison l E v).hom.app P).val.app
      (op ((proEtaleBaseChange v).obj (⊤_ U.ProEt))))
      (generator l E v ((model l E U).obj P) (⊤_ U.ProEt)
        (modelSection l E U P (op (⊤_ U.ProEt)) 1 x)) =
      modelSection l E V P (op ((proEtaleBaseChange v).obj (⊤_ U.ProEt))) 1 x := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((modelAdjunction l E U (⊤_ U.ProEt) terminalIsTerminal).comp
      (ordinaryIntegralModuleAdjunction l E v))
    ((modelAdjunction l E V ((proEtaleBaseChange v).obj (⊤_ U.ProEt))
      (terminalIsTerminal.isTerminalObj (proEtaleBaseChange v) (⊤_ U.ProEt))).ofNatIsoRight
      (modelSectionsPushIso l E v (⊤_ U.ProEt)).symm) P
  rw [← Adjunction.homEquiv_id, Adjunction.comp_homEquiv,
    Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have hx := congrArg (fun f ↦ f x) h
  change (modelAdjunction l E U (⊤_ U.ProEt) terminalIsTerminal).homEquiv _ _
    ((ordinaryIntegralModuleAdjunction l E v).homEquiv _ _
      ((allComparison l E v).hom.app P)) x = _ at hx
  rw [modelAdjunction_apply] at hx
  simp only [ModuleCat.comp_apply, modelAdjunction_apply] at hx
  change _ = modelSection l E V P
    (op ((proEtaleBaseChange v).obj (⊤_ U.ProEt))) 1 x at hx
  rw [Adjunction.homEquiv_unit] at hx
  exact hx

private theorem allComparison_normalized {V U : Scheme.{u}} (v : V ⟶ U)
    (P : ModuleCat.{u + 1} (PbcIntegralRing l E)) (W : U.ProEt) (x : P) :
    (((allComparison l E v).hom.app P).val.app (op ((proEtaleBaseChange v).obj W)))
      (generator l E v ((model l E U).obj P) W
        (modelSection l E U P (op W) 1 x)) =
      modelSection l E V P (op ((proEtaleBaseChange v).obj W)) 1 x := by
  let β := (ordinaryIntegralModuleAdjunction l E v).homEquiv _ _
    ((allComparison l E v).hom.app P)
  have h := PresheafOfModules.naturality_apply β.val (terminal.from W).op
    (modelSection l E U P (op (⊤_ U.ProEt)) 1 x)
  change β.val.app (op W)
    (((model l E U).obj P).val.map (terminal.from W).op _) =
      ((model l E V).obj P).val.map ((proEtaleBaseChange v).map (terminal.from W)).op
        (β.val.app (op (⊤_ U.ProEt)) _) at h
  rw [modelSection_restrict] at h
  change _ = ((model l E V).obj P).val.map _
    ((((allComparison l E v).hom.app P).val.app _)
      (generator l E v ((model l E U).obj P) (⊤_ U.ProEt)
        (modelSection l E U P (op (⊤_ U.ProEt)) 1 x))) at h
  rw [allComparison_terminal, modelSection_restrict] at h
  exact h

/-- The canonical comparison is uniquely fixed on constant tensor generators.
Source: Stacks 08H3 and 03EK; the item's balanced-tensor and matrix argument
(blueprint: lem-tw-finite-projective-model-pullback).
Proof: the projection equations show that the completed structural map preserves
constant R-scalars. The explicit constant-module and scalar-extension adjunctions
identify maps out of each model with R-linear maps to its terminal sections.
Scalar compatibility identifies these right adjoints after ordinary pushforward.
Uniqueness of left adjoints therefore gives the comparison, even for arbitrary
R-modules. The hom-equivalence equation gives its normalized formula at a terminal
object. Restriction gives the formula on every object, and injectivity of the
hom-equivalences proves that this formula determines the comparison uniquely. -/
theorem comparison_existsUnique {V U : Scheme.{u}} (v : V ⟶ U) :
    ∃! γ : projectiveModel l E U ⋙ ordinaryIntegralModulePull l E v ≅ projectiveModel l E V,
      ∀ (P : Projectives l E) (W : U.ProEt) (x : P.obj),
        ((γ.hom.app P).val.app (op ((proEtaleBaseChange v).obj W)))
          (generator l E v ((model l E U).obj P.obj) W
            (modelSection l E U P.obj (op W) 1 x)) =
          modelSection l E V P.obj (op ((proEtaleBaseChange v).obj W)) 1 x := by
  let e : projectiveModel l E U ⋙ ordinaryIntegralModulePull l E v ≅
      projectiveModel l E V := Functor.isoWhiskerLeft (ObjectProperty.ι _) (allComparison l E v)
  refine ⟨e, ?_, ?_⟩
  · intro P W x
    exact allComparison_normalized l E v P.obj W x
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext P
    apply ((ordinaryIntegralModuleAdjunction l E v).homEquiv _ _).injective
    apply ((modelAdjunction l E U (⊤_ U.ProEt) terminalIsTerminal).homEquiv _ _).injective
    ext x
    rw [modelAdjunction_apply, modelAdjunction_apply]
    exact (he' P (⊤_ U.ProEt) x).trans
      (allComparison_normalized l E v P.obj (⊤_ U.ProEt) x).symm

/-- The unique normalized comparison; no splitting is chosen in this definition.
Source: Stacks 08H3 and 03EK
(blueprint: lem-tw-finite-projective-model-pullback). -/
def comparison {V U : Scheme.{u}} (v : V ⟶ U) :
    projectiveModel l E U ⋙ ordinaryIntegralModulePull l E v ≅ projectiveModel l E V :=
  (comparison_existsUnique l E v).exists.choose

/-- The standard finite free scalar module, including rank zero.
Source: Stacks 08G5, with the standard coordinate basis
(blueprint: lem-tw-finite-projective-model-pullback). -/
def free (r : ℕ) : Projectives l E :=
  ⟨ModuleCat.of (PbcIntegralRing l E) (Fin r → PbcIntegralRing l E), inferInstance, inferInstance⟩

/-- Both specified basis formulas for the finite-free comparison.
The direct-image section ordinaryIntegralDirectRingMap(a) represents c_v(a).
Source: Stacks 03EK and 08H3, balanced pure-tensor calculation
(blueprint: lem-tw-finite-projective-model-pullback).
Proof: apply the normalized comparison to the jth basis generator. Linearity moves
b outside. The tensor balancing identity moves a through the coefficient map,
giving b c_v(a). Apply the inverse equation at a=1 to obtain the inverse formula.
All operations commute with restrictions; inverse-image sections are locally
represented by such sections, so the equations give the sheaf pure-tensor formulas. -/
theorem comparison_free {V U : Scheme.{u}} (v : V ⟶ U) (r : ℕ)
    (W : U.ProEt) (j : Fin r)
    (a : (completedIntegralCommRingSheafUnrestricted.{u, u} l E U).obj.obj (op W))
    (b : (completedIntegralCommRingSheafUnrestricted.{u, u} l E V).obj.obj
      (op ((proEtaleBaseChange v).obj W))) :
    (((comparison l E v).hom.app (free l E r)).val.app
      (op ((proEtaleBaseChange v).obj W)))
        (b • generator l E v ((model l E U).obj (free l E r).obj) W
          (modelSection l E U (free l E r).obj (op W) a (Pi.single j 1))) =
      modelSection l E V (free l E r).obj (op ((proEtaleBaseChange v).obj W))
        (b * @id ((completedIntegralCommRingSheafUnrestricted.{u, u} l E V).obj.obj
          (op ((proEtaleBaseChange v).obj W)))
          (((ordinaryIntegralDirectRingMap l E v).hom.app (op W)) a)) (Pi.single j 1) ∧
    (((comparison l E v).inv.app (free l E r)).val.app
      (op ((proEtaleBaseChange v).obj W)))
        (modelSection l E V (free l E r).obj (op ((proEtaleBaseChange v).obj W))
          b (Pi.single j 1)) =
      b • generator l E v ((model l E U).obj (free l E r).obj) W
        (modelSection l E U (free l E r).obj (op W) 1 (Pi.single j 1)) := by
  have hn := (comparison_existsUnique l E v).exists.choose_spec
    (free l E r) W (Pi.single j 1)
  change ((comparison l E v).hom.app (free l E r)).val.app _
    (generator l E v ((model l E U).obj (free l E r).obj) W
      (modelSection l E U (free l E r).obj (op W) 1 (Pi.single j 1))) = _ at hn
  have hg : generator l E v ((model l E U).obj (free l E r).obj) W
      (modelSection l E U (free l E r).obj (op W) a (Pi.single j 1)) =
      ((ordinaryIntegralDirectRingMap l E v).hom.app (op W) a) •
        generator l E v ((model l E U).obj (free l E r).obj) W
          (modelSection l E U (free l E r).obj (op W) 1 (Pi.single j 1)) := by
    rw [modelSection_smul]
    exact (((ordinaryIntegralModuleAdjunction l E v).unit.app
      ((model l E U).obj (free l E r).obj)).val.app (op W)).hom.map_smul _ _
  constructor
  · rw [hg, map_smul, map_smul]
    erw [hn]
    simpa only [id_eq, smul_smul] using
      (modelSection_smul l E V (free l E r).obj
        (op ((proEtaleBaseChange v).obj W))
        (b * @id ((completedIntegralCommRingSheafUnrestricted.{u, u} l E V).obj.obj
          (op ((proEtaleBaseChange v).obj W)))
          ((ordinaryIntegralDirectRingMap l E v).hom.app (op W) a))
        (Pi.single j 1)).symm
  · have hinv := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.val.app (op ((proEtaleBaseChange v).obj W)))
        ((comparison l E v).app (free l E r)).hom_inv_id)
      (generator l E v ((model l E U).obj (free l E r).obj) W
        (modelSection l E U (free l E r).obj (op W) 1 (Pi.single j 1)))
    change ((comparison l E v).inv.app (free l E r)).val.app _
      (((comparison l E v).hom.app (free l E r)).val.app _ _) = _ at hinv
    erw [hn] at hinv
    rw [modelSection_smul, map_smul]
    exact congrArg (fun x ↦ b • x) hinv

/-- Every specified splitting gives exactly the restriction to the same scalar idempotent.
The comparison itself is independent of that splitting and natural in all linear maps,
as expressed by its natural-isomorphism type.
Source: Stacks 08H3; the item's retract and rectangular-matrix calculation
(blueprint: lem-tw-finite-projective-model-pullback).
Proof: put e=i p. The free comparison intertwines e. The composites
J_V gamma_r v^*I_U and v^*J_U gamma_r^{-1} I_V are inverse by p i=1 and e^2=e.
For h:P → P' the matrix i' h p intertwines these comparisons. Taking h=1 with
two splittings proves independence. The inclusion equation identifies the image
with exactly the same idempotent, rather than an unspecified isomorphic summand. -/
theorem comparison_retract {V U : Scheme.{u}} (v : V ⟶ U)
    (P : Projectives l E) (r : ℕ) (i : P.obj ⟶ (free l E r).obj)
    (p : (free l E r).obj ⟶ P.obj) (_h : i ≫ p = 𝟙 P.obj) :
    (comparison l E v).hom.app P =
      (ordinaryIntegralModulePull l E v).map ((model l E U).map i) ≫
        (comparison l E v).hom.app (free l E r) ≫ (model l E V).map p ∧
    (comparison l E v).inv.app P =
      (model l E V).map i ≫ (comparison l E v).inv.app (free l E r) ≫
        (ordinaryIntegralModulePull l E v).map ((model l E U).map p) ∧
    (comparison l E v).hom.app P ≫ (model l E V).map i =
      (ordinaryIntegralModulePull l E v).map ((model l E U).map i) ≫
        (comparison l E v).hom.app (free l E r) := by
  let i' : P ⟶ free l E r := ⟨i⟩
  let p' : free l E r ⟶ P := ⟨p⟩
  have h' : i' ≫ p' = 𝟙 P := ObjectProperty.hom_ext _ _h
  exact retract_naturality (comparison l E v) i' p' h'

/-- The specified termwise scalar realization, including the original differential.
Source: Stacks 03CY and 03EK; Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-finite-projective-model-pullback). -/
def modelComplex (T : Scheme.{u}) :=
  (model l E T).mapHomologicalComplex (.up ℤ)

/-- Naturality in each scalar differential is the chain-map equation.
Source: Stacks 08H3; the item's step 5
(blueprint: lem-tw-finite-projective-model-pullback).
Proof: regard d(i,j) as a morphism in the full finite-projective subcategory.
The naturality equation for comparison is exactly the displayed equality. -/
theorem comparison_differential {V U : Scheme.{u}} (v : V ⟶ U)
    (L : CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ)
    (hL : ∀ q : ℤ, Module.Finite (PbcIntegralRing l E) (L.X q) ∧
      Module.Projective (PbcIntegralRing l E) (L.X q)) (i j : ℤ) :
    (comparison l E v).hom.app ⟨L.X i, hL i⟩ ≫ (model l E V).map (L.d i j) =
      (ordinaryIntegralModulePull l E v).map ((model l E U).map (L.d i j)) ≫
        (comparison l E v).hom.app ⟨L.X j, hL j⟩ := by
  exact ((comparison l E v).hom.naturality
    (show (⟨L.X i, hL i⟩ : Projectives l E) ⟶ ⟨L.X j, hL j⟩ from ⟨L.d i j⟩)).symm

/-- The normalized isomorphism of complexes, with its actual degreewise comparison maps.
Source: Stacks 08H3; the item's step 5
(blueprint: lem-tw-finite-projective-model-pullback). -/
def complexComparison {V U : Scheme.{u}} (v : V ⟶ U)
    (L : CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ)
    (hL : ∀ q : ℤ, Module.Finite (PbcIntegralRing l E) (L.X q) ∧
      Module.Projective (PbcIntegralRing l E) (L.X q)) :
    ((ordinaryIntegralModulePull l E v).mapHomologicalComplex (.up ℤ)).obj
      ((modelComplex l E U).obj L) ≅
      (modelComplex l E V).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (comparison l E v).app ⟨L.X q, hL q⟩)
    (fun i j _ ↦ comparison_differential l E v L hL i j)

/-- Flat terms, K-flatness and the prescribed ordinary derived model comparison.
The LF and epsilon binders are a presentation of the given left derived functor,
with its universal counit, rather than an extra flatness or exactness hypothesis.
Source: Stacks 06YQ, 06YY and 08H3; Bhatt--Scholze, Proposition 6.6.11
and Remark 6.8.15 (blueprint: lem-tw-finite-projective-model-pullback).
Proof:
1. At each finite quotient the structural map preserves constant R-sections.
   Limit projections are jointly monic, so it preserves the constant scalar map.
2. The constant-module and scalar-extension adjunctions identify the models before
   and after ordinary pullback. Uniqueness of left adjoints gives the normalized
   comparison; naturality gives its retract and differential identities.
3. Realize a splitting of every L^q into a finite free scalar module. The realization
   of R is the unit, and finite products are preserved. Thus the realization is a
   retract of B_U^r. Finite-free retracts are flat, with no flatness of B_U/R.
4. Constant realization preserves zero, so the model is bounded above. The theorem
   for bounded-above complexes with flat terms gives K-flatness.
5. The canonical ordinary computation counit is invertible on good complexes.
   Its naturality implies preservation of quasi-isomorphisms on this resolving class.
   Apply the resolving-class theorem and uniqueness of derived functors to obtain
   invertibility for the specified LF and epsilon, in their given universe.
6. Localize complexComparison and compose the two isomorphisms.
   No completion or flatness of the structural map is used. -/
theorem finiteProjectiveModelPullback {V U : Scheme.{u}} (v : V ⟶ U)
    [HasDerivedCategory.{w} (integralTowerModules.{u, u} l E U)]
    [HasDerivedCategory.{w} (integralTowerModules.{u, u} l E V)]
    (LF : DerivedCategory (integralTowerModules.{u, u} l E U) ⥤
      DerivedCategory (integralTowerModules.{u, u} l E V))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      (ordinaryIntegralModulePull l E v).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (integralTowerModules.{u, u} l E U) (.up ℤ))]
    (L : CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ)
    (hL : ∀ q : ℤ, Module.Finite (PbcIntegralRing l E) (L.X q) ∧
      Module.Projective (PbcIntegralRing l E) (L.X q))
    (a b : ℤ) (_hbounded : ∀ q : ℤ, q < a ∨ b < q → IsZero (L.X q)) :
    (∀ q : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology U) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E U)
      (((modelComplex l E U).obj L).X q)) ∧
    CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology U) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E U)
      ((modelComplex l E U).obj L) ∧
    IsIso (LF.map ((DerivedCategory.quotientCompQhIso _).inv.app ((modelComplex l E U).obj L)) ≫
      epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj ((modelComplex l E U).obj L)) ≫
      DerivedCategory.Qh.map
        (((ordinaryIntegralModulePull l E v).mapHomotopyCategoryFactors (.up ℤ)).hom.app
          ((modelComplex l E U).obj L)) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        (((ordinaryIntegralModulePull l E v).mapHomologicalComplex (.up ℤ)).obj
          ((modelComplex l E U).obj L))) ∧
    IsIso (LF.map ((DerivedCategory.quotientCompQhIso _).inv.app ((modelComplex l E U).obj L)) ≫
      epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj ((modelComplex l E U).obj L)) ≫
      DerivedCategory.Qh.map
        (((ordinaryIntegralModulePull l E v).mapHomotopyCategoryFactors (.up ℤ)).hom.app
          ((modelComplex l E U).obj L)) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        (((ordinaryIntegralModulePull l E v).mapHomologicalComplex (.up ℤ)).obj
          ((modelComplex l E U).obj L)) ≫
        DerivedCategory.Q.map (complexComparison l E v L hL).hom) := by
  have hflat (q : ℤ) : SheafOfModules.IsFlatOnSite
      (J := ProEt.topology U) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E U)
      (((modelComplex l E U).obj L).X q) := by
    have := (hL q).1
    have := (hL q).2
    exact model_flat l E U (L.X q)
  have hb : CochainComplex.IsStrictlyLE ((modelComplex l E U).obj L) b :=
    (CochainComplex.isStrictlyLE_iff ((modelComplex l E U).obj L) b).2
      (fun q hq ↦ (model l E U).map_isZero (_hbounded q (Or.inr hq)))
  have hk := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E U)
    ((modelComplex l E U).obj L) b hflat
  have hi := ordinaryPull_comparison_iso l E v LF epsilon
    ((modelComplex l E U).obj L) ⟨hk, hflat⟩
  refine ⟨hflat, hk, hi, ?_⟩
  have : IsIso ((SheafOfModules.ringedPullbackComplexComparison
      (ordinaryIntegralModulePull l E v) LF epsilon).app ((modelComplex l E U).obj L) ≫
      DerivedCategory.Q.map (complexComparison l E v L hL).hom) := inferInstance
  simpa only [SheafOfModules.ringedPullbackComplexComparison, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using this

end WeilConjectures.FiniteProjectivePullback
