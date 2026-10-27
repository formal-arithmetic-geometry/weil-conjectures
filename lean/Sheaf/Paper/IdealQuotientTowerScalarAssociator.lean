/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IdealModuleQuotients
public import Sheaf.Paper.RingedScalarExtensionComplexAdjunction
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Functor.OfSequence
import all Sheaf.Paper.SheafTensorIdealQuotient

/-! # Balanced scalar associativity for ideal quotient towers

Source: Stacks Project, Modules on Sites, Tags 03EK and 03CY; the explicit balanced
quotient calculation in DAG proof steps 1--11.
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator).

Tower index `n : ℕ` denotes the positive index `n + 1` of the source. All tensors
and ring quotients below are the existing sheafified constructions.
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped ChangeOfRings
namespace CategoryTheory.RingedSiteIdeal
set_option autoImplicit false
attribute [local implicit_reducible] quotientTensor SheafOfModules.cochainModulesMonoidal
  sheafCompose
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- Right tensoring with the existing quotient coefficient module.
Source: Stacks 03EK (blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
abbrev idealTensorFunctor {R : Sheaf J CommRingCat.{u}} (I : RingedSiteIdeal R) :
    SheafOfModules.{u} (siteModuleRings R) ⥤ SheafOfModules.{u} (siteModuleRings R) :=
  tensorRight (quotientCoefficient I)

/-- The image of an original scalar-extension tensor under the sheafification unit.
The order of the sectionwise factors in Mathlib is scalar first.
Source: Stacks 03CY, 03EK
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def idealScalarPure {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (p : M.val.obj W) (s : S.obj.obj W) :
    ((SheafOfModules.RingedTensor.tensorFunctor a).obj M).val.obj W :=
  (toSheafify J (SheafOfModules.changeOfRingsPresheaf a M).presheaf).app W
    (s ⊗ₜ[R.obj.obj W, (a.hom.app W).hom] p)

/-- The actual quotient transition applied termwise to an unbounded cochain complex.
Here `t` is the coefficient map whose value is the sheafified ring transition.
Source: Stacks 03CY, 03EK
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def idealComplexTransition {R : Sheaf J CommRingCat.{u}} {I' I : RingedSiteIdeal R}
    (t : quotientCoefficient I' ⟶ quotientCoefficient I)
    (P : CochainComplex (SheafOfModules.{u} (siteModuleRings R)) ℤ) :
    ((idealTensorFunctor I').mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((idealTensorFunctor I).mapHomologicalComplex (.up ℤ)).obj P :=
  (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map t) (.up ℤ)).app P

/-- The strict tower with the actual quotient transitions. The coefficient maps
are specified on every section by `ringTransition` in the main theorem.
Source: Stacks 03CY, 03EK
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def idealComplexTower {R : Sheaf J CommRingCat.{u}} (I : ℕ → RingedSiteIdeal R)
    (t : ∀ n, quotientCoefficient (I (n + 1)) ⟶ quotientCoefficient (I n))
    (P : CochainComplex (SheafOfModules.{u} (siteModuleRings R)) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} (siteModuleRings R)) ℤ :=
  Functor.ofOpSequence
    (X := fun n ↦ ((idealTensorFunctor (I n)).mapHomologicalComplex (.up ℤ)).obj P)
    (fun n ↦ idealComplexTransition (t n) P)

attribute [local irreducible]
  SheafOfModules.RingedTensor.tensorAdjunction
set_option backward.isDefEq.respectTransparency.types false

private abbrev Res {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) : SheafOfModules.{u} (siteModuleRings
    S) ⥤ SheafOfModules.{u} (siteModuleRings R) :=
  SheafOfModules.RingedTensor.restriction a

-- The equality predicate fixes the chosen object uniquely, and its proof is complete.
private instance scalarZeroLiteral {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    (SheafOfModules.RingedTensor.tensorFunctor a).PreservesZeroMorphisms := by
  have := CategoryTheory.scalarExtension_additive a
  infer_instance

private def frozen {T : Sort*} (x : T) : T :=
  Classical.choose (show ∃ y, y = x from ⟨x, rfl⟩)

private lemma frozen_eq {T : Sort*} (x : T) : frozen x = x :=
  Classical.choose_spec (show ∃ y, y = x from ⟨x, rfl⟩)

private def scalarUnit {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (M : SheafOfModules.{u} (siteModuleRings R)) : M ⟶ (Res a).obj
        ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) :=
  (SheafOfModules.RingedTensor.tensorAdjunction a).unit.app M

private lemma scalarUnit_apply {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ) (p : M.val.obj W) :
    (scalarUnit a M).val.app W p = idealScalarPure a M W p 1 := by
  unfold scalarUnit
  rw [← Adjunction.homEquiv_id]
  have he : (SheafOfModules.RingedTensor.tensorAdjunction a).homEquiv M
      ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) =
      SheafOfModules.RingedTensor.tensorHomEquiv a M
        ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) := by
    unfold SheafOfModules.RingedTensor.tensorAdjunction
    rw [Adjunction.mkOfHomEquiv_homEquiv]
  rw [he]
  rfl

private lemma scalar_ext {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    {M : SheafOfModules.{u} (siteModuleRings R)} {H : SheafOfModules.{u} (siteModuleRings S)} {f g :
        (SheafOfModules.RingedTensor.tensorFunctor a).obj M ⟶ H}
    (h : ∀ W p, f.val.app W (idealScalarPure a M W p 1) =
      g.val.app W (idealScalarPure a M W p 1)) : f = g := by
  apply ((SheafOfModules.RingedTensor.tensorAdjunction a).homEquiv M H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext W p
  change f.val.app W ((scalarUnit a M).val.app W p) =
    g.val.app W ((scalarUnit a M).val.app W p)
  rw [scalarUnit_apply]
  exact h W p

private def scalarLift {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    {M : SheafOfModules.{u} (siteModuleRings R)} {H : SheafOfModules.{u} (siteModuleRings S)} (f : M
        ⟶ (Res a).obj H) : (SheafOfModules.RingedTensor.tensorFunctor a).obj M ⟶ H :=
  ((SheafOfModules.RingedTensor.tensorAdjunction a).homEquiv M H).symm f

private lemma scalarLift_one {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    {M : SheafOfModules.{u} (siteModuleRings R)} {H : SheafOfModules.{u} (siteModuleRings S)} (f : M
        ⟶ (Res a).obj H) (W : Cᵒᵖ) (p : M.val.obj W) :
    (scalarLift a f).val.app W (idealScalarPure a M W p 1) = f.val.app W p := by
  rw [← scalarUnit_apply]
  have h := ((SheafOfModules.RingedTensor.tensorAdjunction a).homEquiv M H).apply_symm_apply f
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.val.app W p) h

attribute [local irreducible] scalarLift

private lemma scalarPure_smul {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ) (p : M.val.obj W) (s t : S.obj.obj W) :
    idealScalarPure a M W p (s * t) = s • idealScalarPure a M W p t := by
  unfold idealScalarPure
  change (((PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} a M)).app W) ((s * t) ⊗ₜ[R.obj.obj W,
      (a.hom.app W).hom] p) = _
  rw [← ModuleCat.ExtendScalars.smul_tmul (f := (a.hom.app W).hom)]
  exact (((PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} a M)).app W).hom.map_smul s _

attribute [local irreducible] SheafOfModules.RingedTensor.tensorFunctor

private lemma scalarLift_pure {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    {M : SheafOfModules.{u} (siteModuleRings R)} {H : SheafOfModules.{u} (siteModuleRings S)} (f : M
        ⟶ (Res a).obj H) (W : Cᵒᵖ)
    (p : M.val.obj W) (s : S.obj.obj W) :
    (scalarLift a f).val.app W (idealScalarPure a M W p s) =
      s • (show H.val.obj W from f.val.app W p) := by
  calc
    _ = (scalarLift a f).val.app W (s • idealScalarPure a M W p 1) := by
      rw [← scalarPure_smul, mul_one]
    _ = s • (show H.val.obj W from f.val.app W p) := by
      rw [((scalarLift a f).val.app W).hom.map_smul, scalarLift_one]

private lemma scalarPure_map {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    {M N : SheafOfModules.{u} (siteModuleRings R)} (f : M ⟶ N) (W : Cᵒᵖ) (p : M.val.obj W) (s :
        S.obj.obj W) :
    ((SheafOfModules.RingedTensor.tensorFunctor a).map f).val.app W (idealScalarPure a M W p s) =
      idealScalarPure a N W (f.val.app W p) s := by
  have h := congrArg (fun k ↦ k.val.app W p)
    ((SheafOfModules.RingedTensor.tensorAdjunction a).unit.naturality f)
  change (scalarUnit a N).val.app W (f.val.app W p) =
    ((SheafOfModules.RingedTensor.tensorFunctor a).map f).val.app W ((scalarUnit a M).val.app W p)
        at h
  rw [scalarUnit_apply, scalarUnit_apply] at h
  calc
    _ = ((SheafOfModules.RingedTensor.tensorFunctor a).map f).val.app W (s • idealScalarPure a M W p
        1) := by
      rw [← scalarPure_smul, mul_one]
    _ = s • idealScalarPure a N W (f.val.app W p) 1 := by
      rw [(((SheafOfModules.RingedTensor.tensorFunctor a).map f).val.app W).hom.map_smul, ← h]
    _ = _ := by rw [← scalarPure_smul, mul_one]

private lemma extension_spec {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (U : C) (s : S.obj.obj (op U)) :
    s ∈ (I.extension a).sections U ↔
      ∃ T : Sieve U, T ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), T g →
        S.obj.map g.op s ∈
          Ideal.span (Set.range (fun i : I.sections V ↦ a.hom.app (op V) i)) :=
  Classical.choose_spec (existsUnique_extension I a).exists U s

private lemma ideal_ext {R : Sheaf J CommRingCat.{u}} {I K : RingedSiteIdeal R}
    (h : ∀ U, I.sections U = K.sections U) : I = K := by
  have h' : I.sections = K.sections := funext h
  cases I
  cases K
  cases h'
  rfl

private lemma extension_image {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (U : C) (r : R.obj.obj (op U)) (hr : r ∈ I.sections U) :
    a.hom.app (op U) r ∈ (I.extension a).sections U := by
  apply (extension_spec a I U _).mpr
  refine ⟨⊤, J.top_mem U, ?_⟩
  intro V g _
  rw [← a.hom.naturality_apply]
  exact Ideal.subset_span ⟨⟨_, I.restriction g r hr⟩, rfl⟩

private lemma extension_le {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (K : RingedSiteIdeal S)
    (h : ∀ U r, r ∈ I.sections U → a.hom.app (op U) r ∈ K.sections U) :
    IsContained (I.extension a) K := by
  intro U s hs
  obtain ⟨T, hT, ht⟩ := (extension_spec a I U s).mp hs
  apply K.local_mem U s T hT
  intro V g hg
  apply (show Ideal.span (Set.range (fun i : I.sections V ↦ a.hom.app (op V) i)) ≤
    K.sections V from Ideal.span_le.mpr ?_) (ht V g hg)
  rintro _ ⟨i, rfl⟩
  exact h V i i.property

private lemma extension_mono {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I' I : RingedSiteIdeal R) (h : IsContained I' I) :
    IsContained (I'.extension a) (I.extension a) :=
  extension_le a I' (I.extension a) fun U r hr ↦ extension_image a I U r (h U hr)

private lemma extension_id {R : Sheaf J CommRingCat.{u}} (I : RingedSiteIdeal R) :
    I.extension (𝟙 R) = I := by
  apply ideal_ext
  intro U
  apply le_antisymm
  · exact extension_le (𝟙 R) I I (fun _ _ h ↦ h) U
  · intro r hr
    exact extension_image (𝟙 R) I U r hr

private lemma extension_comp {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) (I : RingedSiteIdeal R) :
    (I.extension a).extension b = I.extension (a ≫ b) := by
  let K : RingedSiteIdeal S :=
    { sections := fun U ↦ Ideal.comap (b.hom.app (op U)).hom
        ((I.extension (a ≫ b)).sections U)
      restriction := fun g s hs ↦ by
        change b.hom.app _ (S.obj.map g.op s) ∈
          (I.extension (a ≫ b)).sections _
        rw [b.hom.naturality_apply]
        exact (I.extension (a ≫ b)).restriction g _ hs
      local_mem := fun U s T hT hs ↦ by
        apply (I.extension (a ≫ b)).local_mem U _ T hT
        intro W g hg
        rw [← b.hom.naturality_apply]
        exact hs W g hg }
  have ha : IsContained (I.extension a) K :=
    extension_le a I K (fun U r hr ↦ extension_image (a ≫ b) I U r hr)
  apply ideal_ext
  intro U
  apply le_antisymm
  · exact extension_le b (I.extension a) (I.extension (a ≫ b))
      (fun U s hs ↦ ha U hs) U
  · exact extension_le (a ≫ b) I ((I.extension a).extension b)
      (fun U r hr ↦ extension_image b (I.extension a) U _ (extension_image a I U r hr)) U

variable {R : Sheaf J CommRingCat.{u}}

private def tensorAug {R : Sheaf J CommRingCat.{u}} (I : RingedSiteIdeal R)
    (M : SheafOfModules.{u} (siteModuleRings R)) : M ⟶ (idealTensorFunctor I).obj M := tensorUnitMap
        I M

private lemma tensorAug_smul {R : Sheaf J CommRingCat.{u}} (I : RingedSiteIdeal R)
    (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ) (r : R.obj.obj W) (p : M.val.obj W) :
    (tensorAug I M).val.app W (r • p) =
      SheafOfModules.RingedTensor.pure R M (quotientCoefficient I) W p
        ((ringProjection I).hom.app W r) := tensorUnitMap_smul I M W r p

private lemma tensorAug_natural {R : Sheaf J CommRingCat.{u}} (I : RingedSiteIdeal R)
    {M N : SheafOfModules.{u} (siteModuleRings R)} (f : M ⟶ N) :
    f ≫ tensorAug I N = tensorAug I M ≫ (idealTensorFunctor I).map f := by
  change f ≫ tensorUnitMap I N =
    tensorUnitMap I M ≫ (SheafOfModules.monoidalCategory R).whiskerRight f _
  exact (tensorUnit_natural I f).symm.trans
    (congrArg (tensorUnitMap I M ≫ ·) (tensorHom_id f _))

private lemma tensorAug_transition {R : Sheaf J CommRingCat.{u}}
    {I' I : RingedSiteIdeal R} (h : IsContained I' I) (M : SheafOfModules.{u} (siteModuleRings R)) :
    tensorAug I' M ≫
      (((curriedTensor _).flip.map (quotientCoefficientTransition h)).app M) =
        tensorAug I M := by
  change tensorUnitMap I' M ≫
    (SheafOfModules.monoidalCategory R).whiskerLeft M _ = tensorUnitMap I M
  rw [← id_tensorHom]
  exact tensorUnit_transition h M

private def quotientUnit {R : Sheaf J CommRingCat.{u}} (I : RingedSiteIdeal R) :
    𝟭 (SheafOfModules.{u} (siteModuleRings R)) ⟶ idealTensorFunctor I where
  app := tensorAug I
  naturality {_ _} f := tensorAug_natural I f

private def scalarCompositeUnit {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) (M : SheafOfModules.{u} (siteModuleRings R)) :
    M ⟶ (Res (a ≫ b)).obj ((SheafOfModules.RingedTensor.tensorFunctor b).obj
        ((SheafOfModules.RingedTensor.tensorFunctor a).obj M)) where
  val :=
    { app W := ModuleCat.ofHom (X := M.val.obj W)
        (Y := ((Res (a ≫ b)).obj ((SheafOfModules.RingedTensor.tensorFunctor b).obj
            ((SheafOfModules.RingedTensor.tensorFunctor a).obj M))).val.obj W)
        { toFun := fun p ↦ (scalarUnit b _).val.app W ((scalarUnit a M).val.app W p)
          map_add' := by intros; simp only [map_add]
          map_smul' := by
            intro r p
            rw [((scalarUnit a M).val.app W).hom.map_smul]
            change (scalarUnit b _).val.app W
              (a.hom.app W r •
                (show ((SheafOfModules.RingedTensor.tensorFunctor a).obj M).val.obj W from
                    (scalarUnit a M).val.app W p)) = _
            rw [((scalarUnit b _).val.app W).hom.map_smul]
            rfl }
      naturality := by
        intro W Z g
        ext p
        exact (congrArg ((scalarUnit b _).val.app Z)
          (PresheafOfModules.naturality_apply (scalarUnit a M).val g p)).trans
          (PresheafOfModules.naturality_apply (scalarUnit b _).val g _) }

private lemma scalarCompositeUnit_apply {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ) (p : M.val.obj W)
        :
    (scalarCompositeUnit a b M).val.app W p =
      idealScalarPure b _ W (idealScalarPure a M W p 1) 1 := by
  change (scalarUnit b _).val.app W ((scalarUnit a M).val.app W p) = _
  rw [scalarUnit_apply, scalarUnit_apply]

private def restrictionDoubleHom {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) {M : SheafOfModules.{u} (siteModuleRings R)} {H : SheafOfModules.{u}
        (siteModuleRings V)}
    (f : M ⟶ (Res (a ≫ b)).obj H) : M ⟶ (Res a).obj ((Res b).obj H) where
  val :=
    { app W := ModuleCat.ofHom (X := M.val.obj W)
        (Y := ((Res a).obj ((Res b).obj H)).val.obj W)
        { toFun := f.val.app W
          map_add' := map_add _
          map_smul' := fun r p ↦ (f.val.app W).hom.map_smul r p }
      naturality := by
        intro W Z g
        ext p
        exact PresheafOfModules.naturality_apply f.val g p }

private lemma scalarDouble_ext {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) {M : SheafOfModules.{u} (siteModuleRings R)} {H : SheafOfModules.{u}
        (siteModuleRings V)}
    {f g : (SheafOfModules.RingedTensor.tensorFunctor b).obj
        ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) ⟶ H}
    (h : ∀ W p, f.val.app W
      (idealScalarPure b _ W (idealScalarPure a M W p 1) 1) =
      g.val.app W (idealScalarPure b _ W (idealScalarPure a M W p 1) 1)) : f = g := by
  apply scalar_ext b
  intro W x
  have he : scalarUnit b _ ≫ (Res b).map f = scalarUnit b _ ≫ (Res b).map g := by
    apply scalar_ext a
    intro Z p
    change f.val.app Z ((scalarUnit b _).val.app Z (idealScalarPure a M Z p 1)) =
      g.val.app Z ((scalarUnit b _).val.app Z (idealScalarPure a M Z p 1))
    rw [scalarUnit_apply]
    exact h Z p
  have hx := congrArg (fun k ↦ k.val.app W x) he
  change f.val.app W ((scalarUnit b _).val.app W x) =
    g.val.app W ((scalarUnit b _).val.app W x) at hx
  rw [scalarUnit_apply] at hx
  exact hx

private def scalarCompositeLift {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) {M : SheafOfModules.{u} (siteModuleRings R)} {H : SheafOfModules.{u}
        (siteModuleRings V)}
    (f : M ⟶ (Res (a ≫ b)).obj H) : (SheafOfModules.RingedTensor.tensorFunctor b).obj
        ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) ⟶ H :=
  scalarLift b (scalarLift a (restrictionDoubleHom a b f))

private lemma scalarCompositeLift_pure {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) {M : SheafOfModules.{u} (siteModuleRings R)} {H : SheafOfModules.{u}
        (siteModuleRings V)}
    (f : M ⟶ (Res (a ≫ b)).obj H) (W : Cᵒᵖ)
    (p : M.val.obj W) (s : S.obj.obj W) (v : V.obj.obj W) :
    (scalarCompositeLift a b f).val.app W
      (idealScalarPure b _ W (idealScalarPure a M W p s) v) =
        v • (b.hom.app W s • (show H.val.obj W from f.val.app W p)) := by
  rw [scalarCompositeLift, scalarLift_pure, scalarLift_pure]
  rfl

private def scalarAssocHom {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (SheafOfModules.RingedTensor.tensorFunctor b).obj ((SheafOfModules.RingedTensor.tensorFunctor
        a).obj M) ⟶ (SheafOfModules.RingedTensor.tensorFunctor (a ≫ b)).obj M :=
  scalarCompositeLift a b (scalarUnit (a ≫ b) M)

private lemma scalarAssocHom_pure {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (p : M.val.obj W) (s : S.obj.obj W) (v : V.obj.obj W) :
    (scalarAssocHom a b M).val.app W
      (idealScalarPure b _ W (idealScalarPure a M W p s) v) =
        idealScalarPure (a ≫ b) M W p (b.hom.app W s * v) := by
  rw [scalarAssocHom, scalarCompositeLift_pure, scalarUnit_apply, smul_smul,
    mul_comm v, ← scalarPure_smul, mul_one]

private def scalarAssocInv {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (SheafOfModules.RingedTensor.tensorFunctor (a ≫ b)).obj M ⟶
        (SheafOfModules.RingedTensor.tensorFunctor b).obj
        ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) :=
  scalarLift (a ≫ b) (scalarCompositeUnit a b M)

private def scalarAssoc {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) : SheafOfModules.RingedTensor.tensorFunctor a ⋙
        SheafOfModules.RingedTensor.tensorFunctor b ≅ SheafOfModules.RingedTensor.tensorFunctor (a ≫
        b) :=
  NatIso.ofComponents (fun M ↦
    { hom := scalarAssocHom a b M
      inv := scalarAssocInv a b M
      hom_inv_id := by
        apply scalarDouble_ext a b
        intro W p
        change (scalarAssocInv a b M).val.app W
          ((scalarAssocHom a b M).val.app W
            (idealScalarPure b _ W (idealScalarPure a M W p 1) 1)) =
          idealScalarPure b _ W (idealScalarPure a M W p 1) 1
        rw [scalarAssocHom_pure, map_one, one_mul, scalarAssocInv,
          scalarLift_one, scalarCompositeUnit_apply]
      inv_hom_id := by
        apply scalar_ext (a ≫ b)
        intro W p
        change (scalarAssocHom a b M).val.app W
          ((scalarAssocInv a b M).val.app W (idealScalarPure (a ≫ b) M W p 1)) =
          idealScalarPure (a ≫ b) M W p 1
        rw [scalarAssocInv, scalarLift_one, scalarCompositeUnit_apply,
          scalarAssocHom_pure, map_one, one_mul] }) (by
    intro M N f
    apply scalarDouble_ext a b
    intro W p
    change (scalarAssocHom a b N).val.app W
      (((SheafOfModules.RingedTensor.tensorFunctor b).map
          ((SheafOfModules.RingedTensor.tensorFunctor a).map f)).val.app W
        (idealScalarPure b _ W (idealScalarPure a M W p 1) 1)) =
      ((SheafOfModules.RingedTensor.tensorFunctor (a ≫ b)).map f).val.app W
        ((scalarAssocHom a b M).val.app W
          (idealScalarPure b _ W (idealScalarPure a M W p 1) 1))
    rw [scalarPure_map, scalarPure_map, scalarAssocHom_pure,
      scalarAssocHom_pure, map_one, one_mul, scalarPure_map])

private def homKernel {R : Sheaf J CommRingCat.{u}} {F H : SheafOfModules.{u} (siteModuleRings R)}
    (f : F ⟶ H) : F.val.Submodule where
  obj W := (f.val.app W).hom.ker
  map {W Z} g := by
    intro x hx
    change f.val.app Z (show F.val.obj Z from F.val.map g x) = 0
    rw [PresheafOfModules.naturality_apply, show f.val.app _ x = 0 from hx, map_zero]

private lemma homKernel_saturated {R : Sheaf J CommRingCat.{u}} {F H : SheafOfModules.{u}
    (siteModuleRings R)}
    (f : F ⟶ H) : IsSaturated F (homKernel f) := by
  intro U x T hT hx
  apply H.isSheaf.isSeparated _ _ hT
  intro V g hg
  change H.val.map g.op (f.val.app (op U) x) = H.val.map g.op 0
  rw [← PresheafOfModules.naturality_apply, map_zero]
  exact hx V g hg

private lemma kills_localProduct {R : Sheaf J CommRingCat.{u}} (I : RingedSiteIdeal R)
    {F H : SheafOfModules.{u} (siteModuleRings R)} (f : F ⟶ H)
    (h : ∀ (W : Cᵒᵖ) (r : R.obj.obj W), r ∈ I.sections W.unop → ∀ p, f.val.app W (r • p) = 0) :
    ∀ W p, p ∈ (localProduct I F).obj W → f.val.app W p = 0 := by
  have he : localProduct I F ≤ homKernel f := by
    apply sInf_le
    refine ⟨homKernel_saturated f, ?_⟩
    intro U p hp
    exact Submodule.smul_induction_on hp
      (fun r hr x _ ↦ h (op U) r hr x)
      (fun x y hx hy ↦ by
        change f.val.app (op U) (x + y) = 0
        rw [map_add, hx, hy, add_zero])
  exact fun W p hp ↦ he W hp

private def moduleQuotientDesc {R : Sheaf J CommRingCat.{u}} (I : RingedSiteIdeal R)
    {F H : SheafOfModules.{u} (siteModuleRings R)} (f : F ⟶ H)
    (h : ∀ (W : Cᵒᵖ) (r : R.obj.obj W), r ∈ I.sections W.unop → ∀ p, f.val.app W (r • p) = 0) :
    moduleQuotient I F ⟶ H :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (siteModuleRings R).obj)).symm
    (cokernel.desc (localProduct I F).ι f.val (by
      apply PresheafOfModules.hom_ext
      intro W
      apply ModuleCat.hom_ext
      ext p
      exact kills_localProduct I f h W p.val p.property))

private lemma moduleQuotientDesc_projection {R : Sheaf J CommRingCat.{u}}
    (I : RingedSiteIdeal R) {F H : SheafOfModules.{u} (siteModuleRings R)} (f : F ⟶ H)
    (h : ∀ (W : Cᵒᵖ) (r : R.obj.obj W), r ∈ I.sections W.unop → ∀ p, f.val.app W (r • p) = 0) :
    moduleProjection I F ≫ moduleQuotientDesc I f h = f := by
  let g := cokernel.desc (localProduct I F).ι f.val (by
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    ext p
    exact kills_localProduct I f h W p.val p.property)
  have he := (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (siteModuleRings R).obj) (F := H)).apply_symm_apply g
  apply SheafOfModules.hom_ext
  change (cokernel.π (localProduct I F).ι ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings R).obj)).unit.app
      (moduleQuotientPresheaf I F)) ≫ _ = _
  rw [Category.assoc]
  change cokernel.π (localProduct I F).ι ≫
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (siteModuleRings R).obj)
      (F := H)) ((PresheafOfModules.sheafificationHomEquiv
        (𝟙 (siteModuleRings R).obj) (F := H)).symm g) = _
  rw [he]
  exact cokernel.π_desc _ _ _

private lemma tensorUnit_epi {R : Sheaf J CommRingCat.{u}} (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) : Epi (tensorAug I F) := by
  change Epi (tensorUnitMap I F)
  rw [← projection_tensorIso_inv]
  have := projection_epi I F
  infer_instance

private def tensorQuotientDesc {R : Sheaf J CommRingCat.{u}} (I : RingedSiteIdeal R)
    {F H : SheafOfModules.{u} (siteModuleRings R)} (f : F ⟶ H)
    (h : ∀ (W : Cᵒᵖ) (r : R.obj.obj W), r ∈ I.sections W.unop → ∀ p, f.val.app W (r • p) = 0) :
    (idealTensorFunctor I).obj F ⟶ H :=
  (quotientTensorIso I F).hom ≫ moduleQuotientDesc I f h

private lemma tensorQuotientDesc_unit {R : Sheaf J CommRingCat.{u}}
    (I : RingedSiteIdeal R) {F H : SheafOfModules.{u} (siteModuleRings R)} (f : F ⟶ H)
    (h : ∀ (W : Cᵒᵖ) (r : R.obj.obj W), r ∈ I.sections W.unop → ∀ p, f.val.app W (r • p) = 0) :
    tensorAug I F ≫ tensorQuotientDesc I f h = f := by
  dsimp only [tensorQuotientDesc, tensorAug]
  rw [← Category.assoc, tensorUnit_comparison_iso, moduleQuotientDesc_projection]

private def betaUnit {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    M ⟶ (Res a).obj ((idealTensorFunctor (I.extension a)).obj
        ((SheafOfModules.RingedTensor.tensorFunctor a).obj M)) :=
  scalarUnit a M ≫ (Res a).map (tensorAug (I.extension a)
      ((SheafOfModules.RingedTensor.tensorFunctor a).obj M))

private lemma betaUnit_ideal {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    ∀ (W : Cᵒᵖ) (r : R.obj.obj W), r ∈ I.sections W.unop →
      ∀ p, (betaUnit a I M).val.app W (r • p) = 0 := by
  intro W r hr p
  change (tensorAug (I.extension a) ((SheafOfModules.RingedTensor.tensorFunctor a).obj M)).val.app W
    ((scalarUnit a M).val.app W (r • p)) = 0
  rw [((scalarUnit a M).val.app W).hom.map_smul]
  change (tensorAug (I.extension a) ((SheafOfModules.RingedTensor.tensorFunctor a).obj M)).val.app W
    (a.hom.app W r •
      (show ((SheafOfModules.RingedTensor.tensorFunctor a).obj M).val.obj W from (scalarUnit a
          M).val.app W p)) = 0
  rw [tensorAug_smul, ringProjection_ideal _ _ _ (extension_image a I W.unop r hr)]
  exact (SheafOfModules.RingedTensor.pureBilin S _ _ W _).map_zero

attribute [local irreducible] tensorQuotientDesc

private def betaHom {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (SheafOfModules.RingedTensor.tensorFunctor a).obj ((idealTensorFunctor I).obj M) ⟶
      (idealTensorFunctor (I.extension a)).obj ((SheafOfModules.RingedTensor.tensorFunctor a).obj M)
          :=
  scalarLift a (tensorQuotientDesc I (betaUnit a I M) (betaUnit_ideal a I M))

private lemma betaHom_unit {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I M) ≫ betaHom a I M =
      tensorAug (I.extension a) ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) := by
  apply scalar_ext a
  intro W p
  change (betaHom a I M).val.app W
    (((SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I M)).val.app W (idealScalarPure
        a M W p 1)) = _
  rw [scalarPure_map, betaHom]
  rw [scalarLift_one]
  have h := congrArg (fun k ↦ k.val.app W p)
    (tensorQuotientDesc_unit I (betaUnit a I M) (betaUnit_ideal a I M))
  change (tensorQuotientDesc I (betaUnit a I M) (betaUnit_ideal a I M)).val.app W
    ((tensorAug I M).val.app W p) =
      (tensorAug (I.extension a) ((SheafOfModules.RingedTensor.tensorFunctor a).obj M)).val.app W
        ((scalarUnit a M).val.app W p) at h
  rw [scalarUnit_apply] at h
  exact h

attribute [local irreducible] betaHom

private def inverseUnit {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    M ⟶ (Res a).obj ((SheafOfModules.RingedTensor.tensorFunctor a).obj ((idealTensorFunctor I).obj
        M)) :=
  tensorAug I M ≫ scalarUnit a ((idealTensorFunctor I).obj M)

private def inverseMap {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (SheafOfModules.RingedTensor.tensorFunctor a).obj M ⟶ (SheafOfModules.RingedTensor.tensorFunctor
        a).obj ((idealTensorFunctor I).obj M) :=
  scalarLift a (inverseUnit a I M)

attribute [local semireducible] SheafOfModules.RingedTensor.tensorFunctor

private lemma inverseMap_image {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (r : R.obj.obj W) (hr : r ∈ I.sections W.unop) (x : ((SheafOfModules.RingedTensor.tensorFunctor
        a).obj M).val.obj W) :
    (inverseMap a I M).val.app W (a.hom.app W r • x) = 0 := by
  -- Multiplication by a local ideal section is a morphism on the slice over W.
  -- Use local tensor representatives to reduce to original module sections.
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u, u} a M
  let η := toSheafify J P.presheaf
  let H := (SheafOfModules.RingedTensor.tensorFunctor a).obj ((idealTensorFunctor I).obj M)
  have hη : Presheaf.IsLocallySurjective J η :=
    (J.W_toSheafify P.presheaf).isLocallySurjective
  let x' : (sheafify J P.presheaf).obj W := x
  apply H.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J η x')
  rintro V g ⟨z, hz⟩
  change H.val.map g.op ((inverseMap a I M).val.app W (a.hom.app W r • x)) =
    H.val.map g.op 0
  rw [← PresheafOfModules.naturality_apply, ((SheafOfModules.RingedTensor.tensorFunctor a).obj
      M).val.map_smul, map_zero]
  change (inverseMap a I M).val.app (op V)
    (S.obj.map g.op (a.hom.app W r) • ((SheafOfModules.RingedTensor.tensorFunctor a).obj M).val.map
        g.op x) = 0
  rw [← a.hom.naturality_apply]
  change η.app (op V) z = ((SheafOfModules.RingedTensor.tensorFunctor a).obj M).val.presheaf.map
      g.op x at hz
  erw [← hz]
  clear hz
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add z z' hz hz' => simp only [map_add, smul_add, hz, hz', add_zero]
  | tmul s₀ p =>
    let s : S.obj.obj (op V) := s₀
    change (inverseMap a I M).val.app (op V)
      (a.hom.app (op V) (R.obj.map g.op r) • idealScalarPure a M (op V) p s) = 0
    rw [((inverseMap a I M).val.app (op V)).hom.map_smul,
      inverseMap, scalarLift_pure]
    change a.hom.app (op V) (R.obj.map g.op r) •
      (s • (show ((SheafOfModules.RingedTensor.tensorFunctor a).obj ((idealTensorFunctor I).obj
          M)).val.obj (op V) from
        (scalarUnit a ((idealTensorFunctor I).obj M)).val.app (op V)
          ((tensorAug I M).val.app (op V) p))) = 0
    rw [smul_comm]
    have hu := ((scalarUnit a ((idealTensorFunctor I).obj M)).val.app (op V)).hom.map_smul
      (R.obj.map g.op r) ((tensorAug I M).val.app (op V) p)
    change (scalarUnit a ((idealTensorFunctor I).obj M)).val.app (op V)
      ((R.obj.map g.op r) • (tensorAug I M).val.app (op V) p) =
        a.hom.app (op V) (R.obj.map g.op r) •
          (show ((SheafOfModules.RingedTensor.tensorFunctor a).obj ((idealTensorFunctor I).obj
              M)).val.obj (op V) from
            (scalarUnit a ((idealTensorFunctor I).obj M)).val.app (op V)
              ((tensorAug I M).val.app (op V) p)) at hu
    rw [← hu]
    rw [← ((tensorAug I M).val.app (op V)).hom.map_smul,
      tensorAug_smul, ringProjection_ideal I _ _ (I.restriction g r hr)]
    have hp : SheafOfModules.RingedTensor.pure R M (quotientCoefficient I)
        (op V) p 0 = 0 :=
      (SheafOfModules.RingedTensor.pureBilin R M (quotientCoefficient I) (op V) p).map_zero
    rw [hp, map_zero, smul_zero]

attribute [local irreducible] SheafOfModules.RingedTensor.tensorFunctor

private lemma inverseMap_ideal {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    ∀ (W : Cᵒᵖ) (s : S.obj.obj W), s ∈ (I.extension a).sections W.unop → ∀ x,
      (inverseMap a I M).val.app W (s • x) = 0 := by
  intro W s hs x
  obtain ⟨T, hT, ht⟩ :=
    ((Classical.choose_spec (existsUnique_extension I a).exists) W.unop s).mp hs
  let H := (SheafOfModules.RingedTensor.tensorFunctor a).obj ((idealTensorFunctor I).obj M)
  apply H.isSheaf.isSeparated _ _ hT
  intro V g hg
  change H.val.map g.op ((inverseMap a I M).val.app W (s • x)) = H.val.map g.op 0
  erw [← PresheafOfModules.naturality_apply, ((SheafOfModules.RingedTensor.tensorFunctor a).obj
      M).val.map_smul, map_zero]
  let K : Ideal (S.obj.obj (op V)) :=
    { carrier := {t | ∀ y, (inverseMap a I M).val.app (op V) (t • y) = 0}
      zero_mem' := fun y ↦ by rw [zero_smul, map_zero]
      add_mem' := fun {t t'} h h' y ↦ by rw [add_smul, map_add, h, h', add_zero]
      smul_mem' := fun t {t'} h y ↦ by
        rw [smul_eq_mul, mul_smul, ((inverseMap a I M).val.app (op V)).hom.map_smul,
          h, smul_zero] }
  apply (show Ideal.span _ ≤ K from Ideal.span_le.mpr ?_) (ht V g hg)
  rintro _ ⟨r, rfl⟩
  exact inverseMap_image a I M (op V) r.val r.property

private def betaInv {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (idealTensorFunctor (I.extension a)).obj ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) ⟶
      (SheafOfModules.RingedTensor.tensorFunctor a).obj ((idealTensorFunctor I).obj M) :=
  tensorQuotientDesc (I.extension a) (inverseMap a I M) (inverseMap_ideal a I M)

private lemma betaInv_unit {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    tensorAug (I.extension a) ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) ≫ betaInv a I M
        =
      (SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I M) := by
  rw [betaInv, tensorQuotientDesc_unit]
  apply scalar_ext a
  intro W p
  rw [inverseMap, scalarLift_one]
  change (scalarUnit a ((idealTensorFunctor I).obj M)).val.app W
    ((tensorAug I M).val.app W p) = _
  rw [scalarUnit_apply]
  exact (scalarPure_map a (tensorAug I M) W p 1).symm

attribute [local irreducible] inverseMap betaInv

private def betaIso {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (SheafOfModules.RingedTensor.tensorFunctor a).obj ((idealTensorFunctor I).obj M) ≅
      (idealTensorFunctor (I.extension a)).obj ((SheafOfModules.RingedTensor.tensorFunctor a).obj M)
          where
  hom := betaHom a I M
  inv := betaInv a I M
  hom_inv_id := by
    have := tensorUnit_epi I M
    have := (SheafOfModules.RingedTensor.tensorAdjunction a).isLeftAdjoint
    apply (cancel_epi ((SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I M))).mp
    rw [← Category.assoc, betaHom_unit, betaInv_unit]
    exact (Category.comp_id _).symm
  inv_hom_id := by
    have := tensorUnit_epi (I.extension a) ((SheafOfModules.RingedTensor.tensorFunctor a).obj M)
    apply (cancel_epi (tensorAug (I.extension a) ((SheafOfModules.RingedTensor.tensorFunctor a).obj
        M))).mp
    rw [← Category.assoc, betaInv_unit, betaHom_unit]
    exact (Category.comp_id _).symm

private def beta {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) : idealTensorFunctor I ⋙ SheafOfModules.RingedTensor.tensorFunctor a ≅
        SheafOfModules.RingedTensor.tensorFunctor a ⋙
      idealTensorFunctor (I.extension a) :=
  NatIso.ofComponents (betaIso a I) (by
    intro M N f
    have := tensorUnit_epi I M
    have := (SheafOfModules.RingedTensor.tensorAdjunction a).isLeftAdjoint
    apply (cancel_epi ((SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I M))).mp
    change (SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I M) ≫
        (SheafOfModules.RingedTensor.tensorFunctor a).map ((idealTensorFunctor I).map f) ≫ betaHom a
            I N =
      (SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I M) ≫ betaHom a I M ≫
        (idealTensorFunctor (I.extension a)).map ((SheafOfModules.RingedTensor.tensorFunctor a).map
            f)
    rw [← Functor.map_comp_assoc, ← tensorAug_natural I f,
      Functor.map_comp, Category.assoc, betaHom_unit, ← Category.assoc, betaHom_unit]
    exact tensorAug_natural (I.extension a) ((SheafOfModules.RingedTensor.tensorFunctor a).map f))

private lemma scalarPure_module {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ) (r : R.obj.obj W) (p : M.val.obj W) (s :
        S.obj.obj W) :
    idealScalarPure a M W (r • p) s = a.hom.app W r • idealScalarPure a M W p s := by
  have h := ((scalarUnit a M).val.app W).hom.map_smul r p
  change (scalarUnit a M).val.app W (r • p) =
    a.hom.app W r •
      (show ((SheafOfModules.RingedTensor.tensorFunctor a).obj M).val.obj W from (scalarUnit a
          M).val.app W p) at h
  rw [scalarUnit_apply, scalarUnit_apply] at h
  calc
    _ = s • idealScalarPure a M W (r • p) 1 := by
      rw [← scalarPure_smul, mul_one]
    _ = s • (a.hom.app W r • idealScalarPure a M W p 1) := congrArg (s • ·) h
    _ = a.hom.app W r • (s • idealScalarPure a M W p 1) := smul_comm _ _ _
    _ = _ := by rw [← scalarPure_smul, mul_one]

private lemma beta_pure {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (p : M.val.obj W) (r : R.obj.obj W) (s : S.obj.obj W) :
    (betaHom a I M).val.app W
      (idealScalarPure a _ W
        (SheafOfModules.RingedTensor.pure R M (quotientCoefficient I) W p
          ((ringProjection I).hom.app W r)) s) =
      SheafOfModules.RingedTensor.pure S _ (quotientCoefficient (I.extension a)) W
        (idealScalarPure a M W p s)
        ((ringProjection (I.extension a)).hom.app W (a.hom.app W r)) := by
  have h := congrArg (fun k ↦ k.val.app W (idealScalarPure a M W (r • p) s))
    (betaHom_unit a I M)
  change (betaHom a I M).val.app W
    (((SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I M)).val.app W _) = _ at h
  rw [scalarPure_map, tensorAug_smul, scalarPure_module] at h
  exact h.trans (tensorAug_smul (I.extension a) ((SheafOfModules.RingedTensor.tensorFunctor a).obj
      M) W _ _)

private def identityMap (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (siteModuleRings R)) :
    M ⟶ (Res (𝟙 R)).obj M where
  val :=
    { app W := ModuleCat.ofHom (X := M.val.obj W)
        (Y := ((Res (𝟙 R)).obj M).val.obj W)
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl }

private def scalarIdentityInv (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (siteModuleRings
    R)) :
    M ⟶ (SheafOfModules.RingedTensor.tensorFunctor (𝟙 R)).obj M where
  val :=
    { app W := ModuleCat.ofHom (X := M.val.obj W)
        (Y := ((SheafOfModules.RingedTensor.tensorFunctor (𝟙 R)).obj M).val.obj W)
        { toFun := (scalarUnit (𝟙 R) M).val.app W
          map_add' := map_add _
          map_smul' := fun r p ↦ ((scalarUnit (𝟙 R) M).val.app W).hom.map_smul r p }
      naturality := by
        intro W Z g
        ext p
        exact PresheafOfModules.naturality_apply (scalarUnit (𝟙 R) M).val g p }

private def scalarIdentity (R : Sheaf J CommRingCat.{u}) : SheafOfModules.RingedTensor.tensorFunctor
    (𝟙 R) ≅ 𝟭 (SheafOfModules.{u} (siteModuleRings R)) :=
  NatIso.ofComponents (fun M ↦
    { hom := scalarLift (𝟙 R) (identityMap R M)
      inv := scalarIdentityInv R M
      hom_inv_id := by
        apply scalar_ext (𝟙 R)
        intro W p
        change (scalarUnit (𝟙 R) M).val.app W
          ((scalarLift (𝟙 R) (identityMap R M)).val.app W
            (idealScalarPure (𝟙 R) M W p 1)) = _
        rw [scalarLift_one]
        change (scalarUnit (𝟙 R) M).val.app W p = idealScalarPure (𝟙 R) M W p 1
        exact scalarUnit_apply (𝟙 R) M W p
      inv_hom_id := by
        ext W p
        change (scalarLift (𝟙 R) (identityMap R M)).val.app W
          ((scalarUnit (𝟙 R) M).val.app W p) = p
        rw [scalarUnit_apply]
        exact scalarLift_one (𝟙 R) (identityMap R M) W p }) (by
    intro M N f
    apply scalar_ext (𝟙 R)
    intro W p
    change (scalarLift (𝟙 R) (identityMap R N)).val.app W
      (((SheafOfModules.RingedTensor.tensorFunctor (𝟙 R)).map f).val.app W (idealScalarPure (𝟙 R) M
          W p 1)) = _
    rw [scalarPure_map, scalarLift_one]
    change _ = f.val.app W
      ((scalarLift (𝟙 R) (identityMap R M)).val.app W
        (idealScalarPure (𝟙 R) M W p 1))
    rw [scalarLift_one]
    rfl)

private lemma scalar_map_epi {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    {M N : SheafOfModules.{u} (siteModuleRings R)} (f : M ⟶ N) [Epi f] : Epi
        ((SheafOfModules.RingedTensor.tensorFunctor a).map f) where
  left_cancellation g h w := by
    apply ((SheafOfModules.RingedTensor.tensorAdjunction a).homEquiv N _).injective
    apply (cancel_epi f).mp
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left, w]

private lemma beta_augmentation {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I M) ≫ betaHom a I M =
      tensorAug (I.extension a) ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) :=
          betaHom_unit a I M

private lemma scalarAssoc_pure {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (p : M.val.obj W) (s : S.obj.obj W) (v : V.obj.obj W) :
    (scalarAssocHom a b M).val.app W
      (idealScalarPure b _ W (idealScalarPure a M W p s) v) =
        idealScalarPure (a ≫ b) M W p (b.hom.app W s * v) :=
  scalarAssocHom_pure a b M W p s v

private lemma scalarIdentity_pure (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u}
    (siteModuleRings R))
    (W : Cᵒᵖ) (p : M.val.obj W) (r : R.obj.obj W) :
    (scalarLift (𝟙 R) (identityMap R M)).val.app W (idealScalarPure (𝟙 R) M W p r) = r • p :=
  scalarLift_pure (𝟙 R) (identityMap R M) W p r

private lemma beta_hom {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (beta a I).hom.app M = betaHom a I M := rfl

private lemma scalarAssoc_hom {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (scalarAssoc a b).hom.app M = scalarAssocHom a b M := rfl

private lemma scalarIdentity_hom (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u}
    (siteModuleRings R)) :
    (scalarIdentity R).hom.app M = scalarLift (𝟙 R) (identityMap R M) := rfl

attribute [local irreducible] beta scalarAssoc scalarIdentity

private lemma beta_transition {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I' I : RingedSiteIdeal R) (h : IsContained I' I) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (SheafOfModules.RingedTensor.tensorFunctor a).map (((curriedTensor _).flip.map
        (quotientCoefficientTransition h)).app M) ≫
        betaHom a I M =
      betaHom a I' M ≫
        (((curriedTensor _).flip.map
          (quotientCoefficientTransition (extension_mono a I' I h))).app
              ((SheafOfModules.RingedTensor.tensorFunctor a).obj M)) := by
  have := tensorUnit_epi I' M
  have : Epi ((SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I' M)) := scalar_map_epi
      a _
  apply (cancel_epi ((SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I' M))).mp
  change (SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I' M) ≫
      (SheafOfModules.RingedTensor.tensorFunctor a).map _ ≫ betaHom a I M =
    (SheafOfModules.RingedTensor.tensorFunctor a).map (tensorAug I' M) ≫ betaHom a I' M ≫ _
  rw [← Functor.map_comp_assoc]
  have ht : tensorAug I' M ≫
      (((curriedTensor _).flip.map (quotientCoefficientTransition h)).app M) =
        tensorAug I M := by
    exact tensorAug_transition h M
  rw [ht, beta_augmentation, ← Category.assoc, beta_augmentation]
  exact (tensorAug_transition (extension_mono a I' I h) ((SheafOfModules.RingedTensor.tensorFunctor
      a).obj M)).symm

attribute [local irreducible] extension

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private def sealedBeta {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) : idealTensorFunctor I ⋙ SheafOfModules.RingedTensor.tensorFunctor a ≅
      SheafOfModules.RingedTensor.tensorFunctor a ⋙ idealTensorFunctor (I.extension a) := frozen
          (beta a I)

private def sealedAssoc {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) : SheafOfModules.RingedTensor.tensorFunctor a ⋙
        SheafOfModules.RingedTensor.tensorFunctor b ≅ SheafOfModules.RingedTensor.tensorFunctor (a ≫
        b) := frozen (scalarAssoc a b)

private def sealedIdentity (R : Sheaf J CommRingCat.{u}) :
    SheafOfModules.RingedTensor.tensorFunctor (𝟙 R) ≅ 𝟭 (SheafOfModules.{u} (siteModuleRings R)) :=
        frozen (scalarIdentity R)

private lemma sealedBeta_hom {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (sealedBeta a I).hom.app M = betaHom a I M := by
  unfold sealedBeta
  rw [frozen_eq, beta_hom]

private lemma sealedAssoc_hom {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (sealedAssoc a b).hom.app M = scalarAssocHom a b M := by
  unfold sealedAssoc
  rw [frozen_eq, scalarAssoc_hom]

private lemma sealedIdentity_hom (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u}
    (siteModuleRings R)) :
    (sealedIdentity R).hom.app M = scalarLift (𝟙 R) (identityMap R M) := by
  unfold sealedIdentity
  rw [frozen_eq, scalarIdentity_hom]

attribute [local irreducible] sealedBeta sealedAssoc sealedIdentity frozen

private lemma sealedTransition {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I' I : RingedSiteIdeal R) (h : IsContained I' I) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (SheafOfModules.RingedTensor.tensorFunctor a).map (((curriedTensor _).flip.map
        (quotientCoefficientTransition h)).app M) ≫
        (sealedBeta a I).hom.app M =
      (sealedBeta a I').hom.app M ≫
        (((curriedTensor _).flip.map
          (quotientCoefficientTransition (extension_mono a I' I h))).app
              ((SheafOfModules.RingedTensor.tensorFunctor a).obj M)) := by
  rw [sealedBeta_hom, sealedBeta_hom]
  exact beta_transition a I' I h M

private def opSequenceIso {D : Type*} [Category D] {F G : ℕᵒᵖ ⥤ D}
    (e : ∀ n : ℕ, F.obj (op n) ≅ G.obj (op n))
    (h : ∀ n, F.map (homOfLE (Nat.le_add_right n 1)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ G.map (homOfLE (Nat.le_add_right n 1)).op) : F ≅ G := by
  let f : F ⟶ G := NatTrans.ofOpSequence (fun n ↦ (e n).hom) h
  exact NatIso.ofComponents (fun n ↦ e n.unop) (fun g ↦ f.naturality g)

private def towerComparison {D D₂ : Type*} [Category D] [Category D₂]
    [HasZeroMorphisms D] [HasZeroMorphisms D₂]
    (A : D ⥤ D₂) [A.PreservesZeroMorphisms]
    (Q : ℕ → D ⥤ D) [∀ n, (Q n).PreservesZeroMorphisms]
    (T : ℕ → D₂ ⥤ D₂) [∀ n, (T n).PreservesZeroMorphisms]
    (q : ∀ n, Q (n + 1) ⟶ Q n) (t : ∀ n, T (n + 1) ⟶ T n)
    (e : ∀ n, Q n ⋙ A ≅ A ⋙ T n)
    (he : ∀ n M, A.map ((q n).app M) ≫ (e n).hom.app M =
      (e (n + 1)).hom.app M ≫ (t n).app (A.obj M))
    (P : CochainComplex D ℤ) :
    Functor.ofOpSequence
      (X := fun n ↦ ((Q n).mapHomologicalComplex (.up ℤ)).obj P)
      (fun n ↦ (NatTrans.mapHomologicalComplex (q n) (.up ℤ)).app P) ⋙
        A.mapHomologicalComplex (.up ℤ) ≅
    Functor.ofOpSequence
      (X := fun n ↦ ((T n).mapHomologicalComplex (.up ℤ)).obj
        ((A.mapHomologicalComplex (.up ℤ)).obj P))
      (fun n ↦ (NatTrans.mapHomologicalComplex (t n) (.up ℤ)).app
        ((A.mapHomologicalComplex (.up ℤ)).obj P)) := by
  apply opSequenceIso (fun n ↦ (NatIso.mapHomologicalComplex (e n) (.up ℤ)).app P)
  intro n
  simp only [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ]
  ext k : 1
  exact he n (P.X k)

private theorem towerComparison_exists {D D₂ : Type*} [Category D] [Category D₂]
    [HasZeroMorphisms D] [HasZeroMorphisms D₂]
    (A : D ⥤ D₂) [A.PreservesZeroMorphisms]
    (Q : ℕ → D ⥤ D) [∀ n, (Q n).PreservesZeroMorphisms]
    (T : ℕ → D₂ ⥤ D₂) [∀ n, (T n).PreservesZeroMorphisms]
    (q : ∀ n, Q (n + 1) ⟶ Q n) (t : ∀ n, T (n + 1) ⟶ T n)
    (e : ∀ n, Q n ⋙ A ≅ A ⋙ T n)
    (he : ∀ n M, A.map ((q n).app M) ≫ (e n).hom.app M =
      (e (n + 1)).hom.app M ≫ (t n).app (A.obj M))
 :
    ∃ B : ∀ P : CochainComplex D ℤ,
    Functor.ofOpSequence
      (X := fun n ↦ ((Q n).mapHomologicalComplex (.up ℤ)).obj P)
      (fun n ↦ (NatTrans.mapHomologicalComplex (q n) (.up ℤ)).app P) ⋙
        A.mapHomologicalComplex (.up ℤ) ≅
    Functor.ofOpSequence
      (X := fun n ↦ ((T n).mapHomologicalComplex (.up ℤ)).obj
        ((A.mapHomologicalComplex (.up ℤ)).obj P))
      (fun n ↦ (NatTrans.mapHomologicalComplex (t n) (.up ℤ)).app
        ((A.mapHomologicalComplex (.up ℤ)).obj P)),
      (∀ (P : CochainComplex D ℤ) (n : ℕ) (k : ℤ),
        ((B P).hom.app (op n)).f k = (e n).hom.app (P.X k)) ∧
      (∀ (P P' : CochainComplex D ℤ) (f : P ⟶ P') (n : ℕ),
        (A.mapHomologicalComplex (.up ℤ)).map
          (((Q n).mapHomologicalComplex (.up ℤ)).map f) ≫ (B P').hom.app (op n) =
        (B P).hom.app (op n) ≫
          ((T n).mapHomologicalComplex (.up ℤ)).map
            ((A.mapHomologicalComplex (.up ℤ)).map f)) := by
  refine ⟨fun P ↦ towerComparison A Q T q t e he P, ?_, ?_⟩
  · intro P n k
    rfl
  · intro P P' f n
    ext k : 1
    change A.map ((Q n).map (f.f k)) ≫ (e n).hom.app (P'.X k) =
      (e n).hom.app (P.X k) ≫ (T n).map (A.map (f.f k))
    exact (e n).hom.naturality (f.f k)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true


private lemma scalarAssoc_formula {R S V : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ V) (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (p : M.val.obj W) (s : S.obj.obj W) (v : V.obj.obj W) :
    let f : (SheafOfModules.RingedTensor.tensorFunctor b).obj
        ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) ⟶
        (SheafOfModules.RingedTensor.tensorFunctor (a ≫ b)).obj M := (sealedAssoc a b).hom.app M
    f.val.app W (idealScalarPure b _ W (idealScalarPure a M W p s) v) =
      idealScalarPure (a ≫ b) M W p (b.hom.app W s * v) := by
  dsimp only
  rw [sealedAssoc_hom]
  exact scalarAssoc_pure a b M W p s v

private lemma scalarIdentity_formula (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ) (p : M.val.obj W) (r : R.obj.obj W) :
    let f : (SheafOfModules.RingedTensor.tensorFunctor (𝟙 R)).obj M ⟶ M := (sealedIdentity
        R).hom.app M
    f.val.app W (idealScalarPure (𝟙 R) M W p r) = r • p := by
  dsimp only
  rw [sealedIdentity_hom]
  exact scalarIdentity_pure R M W p r

private lemma beta_formula {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (p : M.val.obj W) (r : R.obj.obj W) (s : S.obj.obj W) :
    let f : (SheafOfModules.RingedTensor.tensorFunctor a).obj ((idealTensorFunctor I).obj M) ⟶
        (idealTensorFunctor (I.extension a)).obj ((SheafOfModules.RingedTensor.tensorFunctor a).obj
            M) := (sealedBeta a I).hom.app M
    f.val.app W (idealScalarPure a _ W
      (SheafOfModules.RingedTensor.pure R M (quotientCoefficient I) W p
        ((ringProjection I).hom.app W r)) s) =
      SheafOfModules.RingedTensor.pure S _ (quotientCoefficient (I.extension a)) W
        (idealScalarPure a M W p s)
        ((ringProjection (I.extension a)).hom.app W (a.hom.app W r)) := by
  dsimp only
  rw [sealedBeta_hom]
  exact beta_pure a I M W p r s

private lemma beta_augmentation_formula {R S : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (SheafOfModules.RingedTensor.tensorFunctor a).map ((quotientUnit I).app M) ≫ (sealedBeta a
        I).hom.app M =
      (quotientUnit (I.extension a)).app ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) := by
  rw [sealedBeta_hom]
  exact beta_augmentation a I M


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The quotient coefficient transition has the actual ring-quotient section formula.
Source: Stacks 03EK, 03CY; clause of the balanced quotient calculation.
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def IdealScalarTransitionFormula
    (q : ∀ (R : Sheaf J CommRingCat.{u}) (I' I : RingedSiteIdeal R),
        IsContained I' I → (quotientCoefficient I' ⟶ quotientCoefficient I)) : Prop :=
  (∀ (R : Sheaf J CommRingCat.{u}) (I' I : RingedSiteIdeal R) (h : IsContained I' I)
      (W : Cᵒᵖ) (s : (ringQuotient I').obj.obj W),
      (q R I' I h).val.app W s = (ringTransition h).hom.app W s)

/-- The quotient augmentation has the original-section tensor formula.
Source: Stacks 03EK, 03CY; clause of the balanced quotient calculation.
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def IdealScalarUnitFormula
    (uMap : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        𝟭 (SheafOfModules.{u} (siteModuleRings R)) ⟶ idealTensorFunctor I) : Prop :=
  (∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R)
      (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ) (p : M.val.obj W),
      ((uMap R I).app M).val.app W p =
        SheafOfModules.RingedTensor.pure R M (quotientCoefficient I) W p
          (1 : (ringQuotient I).obj.obj W))

/-- The balanced scalar associator has its prescribed original-section formula.
Source: Stacks 03EK, 03CY; clause of the balanced quotient calculation.
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def IdealScalarAssociatorFormula
    (α : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V),
        SheafOfModules.RingedTensor.tensorFunctor a ⋙
          SheafOfModules.RingedTensor.tensorFunctor b ≅
            SheafOfModules.RingedTensor.tensorFunctor (a ≫ b)) : Prop :=
  (∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V)
      (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
      (p : M.val.obj W) (s : S.obj.obj W) (v : V.obj.obj W),
      ((α R S V a b).hom.app M).val.app W
        (idealScalarPure b _ W (idealScalarPure a M W p s) v) =
          idealScalarPure (a ≫ b) M W p (b.hom.app W s * v))

/-- Scalar extension along the identity is identified by multiplication.
Source: Stacks 03EK, 03CY; clause of the balanced quotient calculation.
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def IdealScalarIdentityFormula
    (ε : ∀ R : Sheaf J CommRingCat.{u},
        SheafOfModules.RingedTensor.tensorFunctor (𝟙 R) ≅
          𝟭 (SheafOfModules.{u} (siteModuleRings R))) : Prop :=
  (∀ (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (siteModuleRings R))
      (W : Cᵒᵖ) (p : M.val.obj W) (r : R.obj.obj W),
      ((ε R).hom.app M).val.app W (idealScalarPure (𝟙 R) M W p r) = r • p)

/-- The scalar/quotient comparison has its prescribed balanced tensor formula.
Source: Stacks 03EK, 03CY; clause of the balanced quotient calculation.
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def IdealScalarQuotientFormula
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        idealTensorFunctor I ⋙ SheafOfModules.RingedTensor.tensorFunctor a ≅
          SheafOfModules.RingedTensor.tensorFunctor a ⋙ idealTensorFunctor (I.extension a)) : Prop
              :=
  (∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R)
      (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
      (p : M.val.obj W) (r : R.obj.obj W) (s : S.obj.obj W),
      ((β R S a I).hom.app M).val.app W
        (idealScalarPure a _ W
          (SheafOfModules.RingedTensor.pure R M (quotientCoefficient I) W p
            ((ringProjection I).hom.app W r)) s) =
      SheafOfModules.RingedTensor.pure S _ (quotientCoefficient (I.extension a)) W
        (idealScalarPure a M W p s)
        ((ringProjection (I.extension a)).hom.app W (a.hom.app W r)))



private theorem unitTransport {D : Type*} [Category D] {T : Type*}
    (F : T → D ⥤ D) (u : ∀ i, 𝟭 D ⟶ F i) (i j : T) (h : i = j) (M : D) :
    (u i).app M ≫ eqToHom (congrArg (fun x ↦ (F x).obj M) h) = (u j).app M := by
  subst h
  simp

/-- A component of the scalar/quotient compatibility calculation.
Source: Stacks 03EK, 03CY
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def ScalarQuotientAugmentationLaw
    (F : ∀ {R S : Sheaf J CommRingCat.{u}}, (R ⟶ S) → SheafOfModules.{u} (siteModuleRings R) ⥤
        SheafOfModules.{u} (siteModuleRings S))
    (Q : ∀ {R : Sheaf J CommRingCat.{u}}, RingedSiteIdeal R → SheafOfModules.{u} (siteModuleRings R)
        ⥤ SheafOfModules.{u} (siteModuleRings R))
    (uMap : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        𝟭 (SheafOfModules.{u} (siteModuleRings R)) ⟶ Q I)
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        Q I ⋙ F a ≅
          F a ⋙ Q (I.extension a)) : Prop :=
  (∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R)
      (M : SheafOfModules.{u} (siteModuleRings R)),
      (F a).map ((uMap R I).app M) ≫
        (β R S a I).hom.app M =
      (uMap S (I.extension a)).app ((F a).obj M))

/-- A component of the scalar/quotient compatibility calculation.
Source: Stacks 03EK, 03CY
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def ScalarQuotientCompositionLaw
    (F : ∀ {R S : Sheaf J CommRingCat.{u}}, (R ⟶ S) → SheafOfModules.{u} (siteModuleRings R) ⥤
        SheafOfModules.{u} (siteModuleRings S))
    (Q : ∀ {R : Sheaf J CommRingCat.{u}}, RingedSiteIdeal R → SheafOfModules.{u} (siteModuleRings R)
        ⥤ SheafOfModules.{u} (siteModuleRings R))
    (hcomp : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V)
        (I : RingedSiteIdeal R), (I.extension a).extension b = I.extension (a ≫ b))
    (α : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V),
        F a ⋙
          F b ≅
            F (a ≫ b))
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        Q I ⋙ F a ≅
          F a ⋙ Q (I.extension a)) : Prop :=
  (∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V)
      (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)),
      (F b).map ((β R S a I).hom.app M) ≫
        (β S V b (I.extension a)).hom.app
          ((F a).obj M) ≫
        eqToHom (congrArg (fun L ↦ (Q L).obj
          ((F b).obj
            ((F a).obj M))) (hcomp R S V a b I)) ≫
        (Q (I.extension (a ≫ b))).map ((α R S V a b).hom.app M) =
      (α R S V a b).hom.app ((Q I).obj M) ≫
        (β R V (a ≫ b) I).hom.app M)

/-- A component of the scalar/quotient compatibility calculation.
Source: Stacks 03EK, 03CY
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def ScalarQuotientIdentityLaw
    (F : ∀ {R S : Sheaf J CommRingCat.{u}}, (R ⟶ S) → SheafOfModules.{u} (siteModuleRings R) ⥤
        SheafOfModules.{u} (siteModuleRings S))
    (Q : ∀ {R : Sheaf J CommRingCat.{u}}, RingedSiteIdeal R → SheafOfModules.{u} (siteModuleRings R)
        ⥤ SheafOfModules.{u} (siteModuleRings R))
    (hid : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        I.extension (𝟙 R) = I)
    (ε : ∀ R : Sheaf J CommRingCat.{u},
        F (𝟙 R) ≅
          𝟭 (SheafOfModules.{u} (siteModuleRings R)))
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        Q I ⋙ F a ≅
          F a ⋙ Q (I.extension a)) : Prop :=
  (∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R)
      (M : SheafOfModules.{u} (siteModuleRings R)),
      (β R R (𝟙 R) I).hom.app M ≫
        (Q (I.extension (𝟙 R))).map ((ε R).hom.app M) ≫
        eqToHom (congrArg (fun L ↦ (Q L).obj M) (hid R I)) =
      (ε R).hom.app ((Q I).obj M))

private theorem familyLaw8
    (F : ∀ {R S : Sheaf J CommRingCat.{u}}, (R ⟶ S) → SheafOfModules.{u} (siteModuleRings R) ⥤
        SheafOfModules.{u} (siteModuleRings S))
    (Q : ∀ {R : Sheaf J CommRingCat.{u}}, RingedSiteIdeal R → SheafOfModules.{u} (siteModuleRings R)
        ⥤ SheafOfModules.{u} (siteModuleRings R))
    (hcomp : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V)
        (I : RingedSiteIdeal R), (I.extension a).extension b = I.extension (a ≫ b))
    (uMap : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        𝟭 (SheafOfModules.{u} (siteModuleRings R)) ⟶ Q I)
    (α : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V),
        F a ⋙
          F b ≅
            F (a ≫ b))
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        Q I ⋙ F a ≅
          F a ⋙ Q (I.extension a))
    (hmap : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
      {M N : SheafOfModules.{u} (siteModuleRings R)} (f : M ⟶ N), Epi f → Epi ((F a).map f))
    (h6 : ScalarQuotientAugmentationLaw F Q uMap β)
    (hepi : ∀ R (I : RingedSiteIdeal R) M, Epi ((uMap R I).app M)) :
    ScalarQuotientCompositionLaw F Q hcomp α β := by
  intro R S V a b I M
  have := hepi R I M
  have : Epi ((F a).map ((uMap R I).app M)) := hmap a _ inferInstance
  have : Epi ((F b).map ((F a).map ((uMap R I).app M))) := hmap b _ inferInstance
  apply (cancel_epi ((F b).map ((F a).map ((uMap R I).app M)))).mp
  rw [← Functor.map_comp_assoc, h6 R S a I M,
    ← Category.assoc, h6 S V b (I.extension a) ((F a).obj M)]
  have hn := congrArg (fun f ↦ f ≫ (β R V (a ≫ b) I).hom.app M)
    ((α R S V a b).hom.naturality ((uMap R I).app M))
  simp only [Functor.comp_map, Category.assoc] at hn
  rw [h6 R V (a ≫ b) I M] at hn
  rw [hn]
  rw [← Category.assoc,
    unitTransport (fun L : RingedSiteIdeal V ↦ Q L) (uMap V)
      _ _ (hcomp R S V a b I)]
  exact ((uMap V (I.extension (a ≫ b))).naturality ((α R S V a b).hom.app M)).symm


private theorem familyLaw9
    (F : ∀ {R S : Sheaf J CommRingCat.{u}}, (R ⟶ S) → SheafOfModules.{u} (siteModuleRings R) ⥤
        SheafOfModules.{u} (siteModuleRings S))
    (Q : ∀ {R : Sheaf J CommRingCat.{u}}, RingedSiteIdeal R → SheafOfModules.{u} (siteModuleRings R)
        ⥤ SheafOfModules.{u} (siteModuleRings R))
    (hid : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        I.extension (𝟙 R) = I)
    (uMap : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        𝟭 (SheafOfModules.{u} (siteModuleRings R)) ⟶ Q I)
    (ε : ∀ R : Sheaf J CommRingCat.{u},
        F (𝟙 R) ≅
          𝟭 (SheafOfModules.{u} (siteModuleRings R)))
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        Q I ⋙ F a ≅
          F a ⋙ Q (I.extension a))
    (hmap : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
      {M N : SheafOfModules.{u} (siteModuleRings R)} (f : M ⟶ N), Epi f → Epi ((F a).map f))
    (h6 : ScalarQuotientAugmentationLaw F Q uMap β)
    (hepi : ∀ R (I : RingedSiteIdeal R) M, Epi ((uMap R I).app M)) :
    ScalarQuotientIdentityLaw F Q hid ε β := by
  intro R I M
  have := hepi R I M
  have : Epi ((F (𝟙 R)).map ((uMap R I).app M)) := hmap (𝟙 R) _ inferInstance
  apply (cancel_epi ((F (𝟙 R)).map ((uMap R I).app M))).mp
  rw [← Category.assoc, h6 R R (𝟙 R) I M]
  rw [← reassoc_of% ((uMap R (I.extension (𝟙 R))).naturality ((ε R).hom.app M))]
  rw [unitTransport (fun L : RingedSiteIdeal R ↦ Q L) (uMap R)
    _ _ (hid R I)]
  exact ((ε R).hom.naturality ((uMap R I).app M)).symm


/-- A component of the scalar/quotient compatibility calculation.
Source: Stacks 03EK, 03CY
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def scalarQuotientComplexTransition
    (F : ∀ {R : Sheaf J CommRingCat.{u}}, RingedSiteIdeal R → SheafOfModules.{u} (siteModuleRings R)
        ⥤ SheafOfModules.{u} (siteModuleRings R))
    [∀ {R} (I : RingedSiteIdeal R), (F I).PreservesZeroMorphisms]
    (tr : ∀ {R} {I' I : RingedSiteIdeal R},
      (quotientCoefficient I' ⟶ quotientCoefficient I) → (F I' ⟶ F I))
    {R : Sheaf J CommRingCat.{u}} {I' I : RingedSiteIdeal R}
    (t : quotientCoefficient I' ⟶ quotientCoefficient I) (P : CochainComplex (SheafOfModules.{u}
        (siteModuleRings R)) ℤ) :
    ((F I').mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((F I).mapHomologicalComplex (.up ℤ)).obj P :=
  (NatTrans.mapHomologicalComplex (tr t) (.up ℤ)).app P

/-- A component of the scalar/quotient compatibility calculation.
Source: Stacks 03EK, 03CY
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def scalarQuotientComplexTower
    (F : ∀ {R : Sheaf J CommRingCat.{u}}, RingedSiteIdeal R → SheafOfModules.{u} (siteModuleRings R)
        ⥤ SheafOfModules.{u} (siteModuleRings R))
    [∀ {R} (I : RingedSiteIdeal R), (F I).PreservesZeroMorphisms]
    (tr : ∀ {R} {I' I : RingedSiteIdeal R},
      (quotientCoefficient I' ⟶ quotientCoefficient I) → (F I' ⟶ F I))
    {R : Sheaf J CommRingCat.{u}} (I : ℕ → RingedSiteIdeal R)
    (t : ∀ n, quotientCoefficient (I (n + 1)) ⟶ quotientCoefficient (I n))
    (P : CochainComplex (SheafOfModules.{u} (siteModuleRings R)) ℤ) : ℕᵒᵖ ⥤ CochainComplex
        (SheafOfModules.{u} (siteModuleRings R)) ℤ :=
  Functor.ofOpSequence
    (X := fun n ↦ ((F (I n)).mapHomologicalComplex (.up ℤ)).obj P)
    (fun n ↦ scalarQuotientComplexTransition F tr (t n) P)

/-- A component of the scalar/quotient compatibility calculation.
Source: Stacks 03EK, 03CY
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
theorem scalarZeroFamily :
    ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S), (SheafOfModules.RingedTensor.tensorFunctor
        a).PreservesZeroMorphisms := by
  intro R S a
  have := CategoryTheory.scalarExtension_additive a
  infer_instance

/-- A component of the scalar/quotient compatibility calculation.
Source: Stacks 03EK, 03CY
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
theorem quotientZeroFamily :
    ∀ {R : Sheaf J CommRingCat.{u}} (I : RingedSiteIdeal R),
      (idealTensorFunctor I).PreservesZeroMorphisms := by
  intro R I
  infer_instance

/-- A component of the scalar/quotient compatibility calculation.
Source: Stacks 03EK, 03CY
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def ScalarQuotientTransitionLaw
    (F : ∀ {R S : Sheaf J CommRingCat.{u}}, (R ⟶ S) → SheafOfModules.{u} (siteModuleRings R) ⥤
        SheafOfModules.{u} (siteModuleRings S))
    (Q : ∀ {R : Sheaf J CommRingCat.{u}}, RingedSiteIdeal R → SheafOfModules.{u} (siteModuleRings R)
        ⥤ SheafOfModules.{u} (siteModuleRings R))
    (tr : ∀ {R} {I' I : RingedSiteIdeal R},
      (quotientCoefficient I' ⟶ quotientCoefficient I) → (Q I' ⟶ Q I))
    (q : ∀ (R : Sheaf J CommRingCat.{u}) (I' I : RingedSiteIdeal R),
        IsContained I' I → (quotientCoefficient I' ⟶ quotientCoefficient I))
    (hmono : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S)
        (I' I : RingedSiteIdeal R), IsContained I' I →
          IsContained (I'.extension a) (I.extension a))
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        Q I ⋙ F a ≅
          F a ⋙ Q (I.extension a)) : Prop :=
  (∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I' I : RingedSiteIdeal R)
      (h : IsContained I' I) (M : SheafOfModules.{u} (siteModuleRings R)),
      (F a).map
          ((tr (q R I' I h)).app M) ≫
        (β R S a I).hom.app M =
      (β R S a I').hom.app M ≫
        ((tr
          (q S (I'.extension a) (I.extension a) (hmono R S a I' I h))).app
            ((F a).obj M)))

/-- A component of the scalar/quotient compatibility calculation.
Source: Stacks 03EK, 03CY
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def ScalarQuotientTowerLaw
    (F : ∀ {R S : Sheaf J CommRingCat.{u}}, (R ⟶ S) → SheafOfModules.{u} (siteModuleRings R) ⥤
        SheafOfModules.{u} (siteModuleRings S))
    [Fzero : ∀ {R S} (a : R ⟶ S), (F a).PreservesZeroMorphisms]
    (Q : ∀ {R : Sheaf J CommRingCat.{u}}, RingedSiteIdeal R → SheafOfModules.{u} (siteModuleRings R)
        ⥤ SheafOfModules.{u} (siteModuleRings R))
    [Qzero : ∀ {R} (I : RingedSiteIdeal R), (Q I).PreservesZeroMorphisms]
    (tr : ∀ {R} {I' I : RingedSiteIdeal R},
      (quotientCoefficient I' ⟶ quotientCoefficient I) → (Q I' ⟶ Q I))
    (q : ∀ (R : Sheaf J CommRingCat.{u}) (I' I : RingedSiteIdeal R),
        IsContained I' I → (quotientCoefficient I' ⟶ quotientCoefficient I))
    (hmono : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S)
        (I' I : RingedSiteIdeal R), IsContained I' I →
          IsContained (I'.extension a) (I.extension a))
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        Q I ⋙ F a ≅
          F a ⋙ Q (I.extension a)) : Prop :=
  (∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S)
      (I : ℕ → RingedSiteIdeal R) (hI : ∀ n, IsContained (I (n + 1)) (I n)),
      ∃ B : ∀ P : CochainComplex (SheafOfModules.{u} (siteModuleRings R)) ℤ,
        scalarQuotientComplexTower Q tr I (fun n ↦ q R _ _ (hI n)) P ⋙
            (F a).mapHomologicalComplex (.up ℤ) ≅
          scalarQuotientComplexTower Q tr (fun n ↦ (I n).extension a)
            (fun n ↦ q S _ _ (hmono R S a _ _ (hI n)))
            (((F a).mapHomologicalComplex
              (.up ℤ)).obj P),
      (∀ (P : CochainComplex (SheafOfModules.{u} (siteModuleRings R)) ℤ) (n : ℕ) (k : ℤ),
        ((B P).hom.app (op n)).f k = (β R S a (I n)).hom.app (P.X k)) ∧
      (∀ (P P' : CochainComplex (SheafOfModules.{u} (siteModuleRings R)) ℤ)
        (f : P ⟶ P') (n : ℕ),
        ((F a).mapHomologicalComplex (.up ℤ)).map
          (((Q (I n)).mapHomologicalComplex (.up ℤ)).map f) ≫
            (B P').hom.app (op n) =
          (B P).hom.app (op n) ≫
            ((Q ((I n).extension a)).mapHomologicalComplex (.up ℤ)).map
              (((F a).mapHomologicalComplex
                (.up ℤ)).map f)))

private theorem familyLaw10
    (F : ∀ {R S : Sheaf J CommRingCat.{u}}, (R ⟶ S) → SheafOfModules.{u} (siteModuleRings R) ⥤
        SheafOfModules.{u} (siteModuleRings S))
    [Fzero : ∀ {R S} (a : R ⟶ S), (F a).PreservesZeroMorphisms]
    (Q : ∀ {R : Sheaf J CommRingCat.{u}}, RingedSiteIdeal R → SheafOfModules.{u} (siteModuleRings R)
        ⥤ SheafOfModules.{u} (siteModuleRings R))
    [Qzero : ∀ {R} (I : RingedSiteIdeal R), (Q I).PreservesZeroMorphisms]
    (tr : ∀ {R} {I' I : RingedSiteIdeal R},
      (quotientCoefficient I' ⟶ quotientCoefficient I) → (Q I' ⟶ Q I))
    (q : ∀ (R : Sheaf J CommRingCat.{u}) (I' I : RingedSiteIdeal R),
        IsContained I' I → (quotientCoefficient I' ⟶ quotientCoefficient I))
    (hmono : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S)
        (I' I : RingedSiteIdeal R), IsContained I' I →
          IsContained (I'.extension a) (I.extension a))
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        Q I ⋙ F a ≅
          F a ⋙ Q (I.extension a))
    (h7 : ScalarQuotientTransitionLaw F Q tr q hmono β) : ScalarQuotientTowerLaw F Q tr q hmono β :=
        by
  intro R S a I hI
  exact towerComparison_exists (F a) (fun n ↦ Q (I n))
    (fun n ↦ Q ((I n).extension a))
    (fun n ↦ tr (q R _ _ (hI n)))
    (fun n ↦ tr (q S _ _ (hmono R S a _ _ (hI n))))
    (fun n ↦ β R S a (I n)) (fun n M ↦ h7 R S a _ _ (hI n) M)

/-- The scalar/quotient comparisons commute with composition of scalar extension.
Source: Stacks 03EK, 03CY; clause of the balanced quotient calculation.
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def IdealScalarCompositionCompatibility
    (hcomp : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V)
        (I : RingedSiteIdeal R), (I.extension a).extension b = I.extension (a ≫ b))
    (α : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V),
        SheafOfModules.RingedTensor.tensorFunctor a ⋙
          SheafOfModules.RingedTensor.tensorFunctor b ≅
            SheafOfModules.RingedTensor.tensorFunctor (a ≫ b))
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        idealTensorFunctor I ⋙ SheafOfModules.RingedTensor.tensorFunctor a ≅
          SheafOfModules.RingedTensor.tensorFunctor a ⋙ idealTensorFunctor (I.extension a)) : Prop
              :=
  ScalarQuotientCompositionLaw (fun a ↦ SheafOfModules.RingedTensor.tensorFunctor a) (fun I ↦
      idealTensorFunctor I) hcomp α β

/-- The scalar/quotient comparison commutes with identity scalar extension.
Source: Stacks 03EK, 03CY; clause of the balanced quotient calculation.
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def IdealScalarIdentityCompatibility
    (hid : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        I.extension (𝟙 R) = I)
    (ε : ∀ R : Sheaf J CommRingCat.{u},
        SheafOfModules.RingedTensor.tensorFunctor (𝟙 R) ≅
          𝟭 (SheafOfModules.{u} (siteModuleRings R)))
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        idealTensorFunctor I ⋙ SheafOfModules.RingedTensor.tensorFunctor a ≅
          SheafOfModules.RingedTensor.tensorFunctor a ⋙ idealTensorFunctor (I.extension a)) : Prop
              :=
  ScalarQuotientIdentityLaw (fun a ↦ SheafOfModules.RingedTensor.tensorFunctor a) (fun I ↦
      idealTensorFunctor I) hid ε β

/-- The scalar/quotient comparison extends to the actual strict towers of complexes.
Source: Stacks 03EK, 03CY; clause of the balanced quotient calculation.
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def IdealScalarTowerCompatibility
    (q : ∀ (R : Sheaf J CommRingCat.{u}) (I' I : RingedSiteIdeal R),
        IsContained I' I → (quotientCoefficient I' ⟶ quotientCoefficient I))
    (hmono : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S)
        (I' I : RingedSiteIdeal R), IsContained I' I →
          IsContained (I'.extension a) (I.extension a))
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        idealTensorFunctor I ⋙ SheafOfModules.RingedTensor.tensorFunctor a ≅
          SheafOfModules.RingedTensor.tensorFunctor a ⋙ idealTensorFunctor (I.extension a)) : Prop
              :=
  ScalarQuotientTowerLaw (Fzero := scalarZeroFamily) (Qzero := quotientZeroFamily)
    (fun a ↦ SheafOfModules.RingedTensor.tensorFunctor a) (fun I ↦ idealTensorFunctor I) (fun t ↦
        (curriedTensor _).flip.map t) q hmono β

/-- The scalar/quotient comparison preserves quotient augmentations.
Source: Stacks 03EK, 03CY; clause of the balanced quotient calculation.
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def IdealScalarAugmentationCompatibility
    (uMap : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        𝟭 (SheafOfModules.{u} (siteModuleRings R)) ⟶ idealTensorFunctor I)
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        idealTensorFunctor I ⋙ SheafOfModules.RingedTensor.tensorFunctor a ≅
          SheafOfModules.RingedTensor.tensorFunctor a ⋙ idealTensorFunctor (I.extension a)) : Prop
              :=
  ScalarQuotientAugmentationLaw (fun a ↦ SheafOfModules.RingedTensor.tensorFunctor a) (fun I ↦
      idealTensorFunctor I) uMap β

/-- The scalar/quotient comparison respects the actual quotient transitions.
Source: Stacks 03EK, 03CY; clause of the balanced quotient calculation.
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator). -/
def IdealScalarTransitionCompatibility
    (q : ∀ (R : Sheaf J CommRingCat.{u}) (I' I : RingedSiteIdeal R),
        IsContained I' I → (quotientCoefficient I' ⟶ quotientCoefficient I))
    (hmono : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S)
        (I' I : RingedSiteIdeal R), IsContained I' I →
          IsContained (I'.extension a) (I.extension a))
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        idealTensorFunctor I ⋙ SheafOfModules.RingedTensor.tensorFunctor a ≅
          SheafOfModules.RingedTensor.tensorFunctor a ⋙ idealTensorFunctor (I.extension a)) : Prop
              :=
  ScalarQuotientTransitionLaw
    (fun a ↦ SheafOfModules.RingedTensor.tensorFunctor a) (fun I ↦ idealTensorFunctor I) (fun t ↦
        (curriedTensor _).flip.map t) q hmono β

private theorem scalarLaw1 : IdealScalarTransitionFormula (J := J)
    (fun _ _ _ h ↦ quotientCoefficientTransition h) := by
  unfold IdealScalarTransitionFormula
  exact fun _ _ _ _ _ _ ↦ rfl

private theorem scalarLaw2 : IdealScalarUnitFormula (J := J)
    (fun _ I ↦ quotientUnit I) := by
  unfold IdealScalarUnitFormula
  exact fun _ _ _ _ _ ↦ rfl

private theorem scalarLaw3 : IdealScalarAssociatorFormula (J := J)
    (fun _ _ _ a b ↦ sealedAssoc a b) := by
  unfold IdealScalarAssociatorFormula
  exact fun _ _ _ a b M W p s v ↦ scalarAssoc_formula a b M W p s v

private theorem scalarLaw4 : IdealScalarIdentityFormula (J := J)
    sealedIdentity := by
  unfold IdealScalarIdentityFormula
  exact fun R M W p r ↦ scalarIdentity_formula R M W p r

private theorem scalarLaw5 : IdealScalarQuotientFormula (J := J)
    (fun _ _ a I ↦ sealedBeta a I) := by
  unfold IdealScalarQuotientFormula
  exact fun _ _ a I M W p r s ↦ beta_formula a I M W p r s

private theorem scalarLaw6 : IdealScalarAugmentationCompatibility (J := J)
    (fun _ I ↦ quotientUnit I)
    (fun _ _ a I ↦ sealedBeta a I) := by
  unfold IdealScalarAugmentationCompatibility ScalarQuotientAugmentationLaw
  exact fun _ _ a I M ↦ beta_augmentation_formula a I M

private theorem scalarLaw7 : IdealScalarTransitionCompatibility (J := J)
    (fun _ _ _ h ↦ quotientCoefficientTransition h)
    (fun _ _ a I' I h ↦ extension_mono a I' I h)
    (fun _ _ a I ↦ sealedBeta a I) := by
  unfold IdealScalarTransitionCompatibility ScalarQuotientTransitionLaw
  exact fun _ _ a I' I h M ↦ sealedTransition a I' I h M

private theorem augmentation_epi (R : Sheaf J CommRingCat.{u})
    (I : RingedSiteIdeal R) M : Epi ((quotientUnit I).app M) := by
  with_unfolding_all exact tensorUnit_epi I M

private theorem assembleSeven
    (q : ∀ (R : Sheaf J CommRingCat.{u}) (I' I : RingedSiteIdeal R),
        IsContained I' I → (quotientCoefficient I' ⟶ quotientCoefficient I))
    (hmono : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S)
        (I' I : RingedSiteIdeal R), IsContained I' I →
          IsContained (I'.extension a) (I.extension a))
    (hcomp : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V)
        (I : RingedSiteIdeal R), (I.extension a).extension b = I.extension (a ≫ b))
    (hid : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        I.extension (𝟙 R) = I)
    (uMap : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        𝟭 (SheafOfModules.{u} (siteModuleRings R)) ⟶ idealTensorFunctor I)
    (α : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V),
        SheafOfModules.RingedTensor.tensorFunctor a ⋙
          SheafOfModules.RingedTensor.tensorFunctor b ≅
            SheafOfModules.RingedTensor.tensorFunctor (a ≫ b))
    (ε : ∀ R : Sheaf J CommRingCat.{u},
        SheafOfModules.RingedTensor.tensorFunctor (𝟙 R) ≅
          𝟭 (SheafOfModules.{u} (siteModuleRings R)))
    (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        idealTensorFunctor I ⋙ SheafOfModules.RingedTensor.tensorFunctor a ≅
          SheafOfModules.RingedTensor.tensorFunctor a ⋙ idealTensorFunctor (I.extension a))
    (h1 : IdealScalarTransitionFormula q)
    (h2 : IdealScalarUnitFormula uMap)
    (h3 : IdealScalarAssociatorFormula α)
    (h4 : IdealScalarIdentityFormula ε)
    (h5 : IdealScalarQuotientFormula β)
    (h6 : IdealScalarAugmentationCompatibility uMap β)
    (h7 : IdealScalarTransitionCompatibility q hmono β)
    (hepi : ∀ R (I : RingedSiteIdeal R) M, Epi ((uMap R I).app M)) :
    IdealScalarTransitionFormula q ∧
    IdealScalarUnitFormula uMap ∧
    IdealScalarAssociatorFormula α ∧
    IdealScalarIdentityFormula ε ∧
    IdealScalarQuotientFormula β ∧
    IdealScalarAugmentationCompatibility uMap β ∧
    IdealScalarTransitionCompatibility q hmono β ∧
    IdealScalarCompositionCompatibility hcomp α β ∧
    IdealScalarIdentityCompatibility hid ε β ∧
    IdealScalarTowerCompatibility q hmono β := by
  exact ⟨h1, h2, h3, h4, h5, h6, h7,
    familyLaw8 (fun a ↦ SheafOfModules.RingedTensor.tensorFunctor a) (fun I ↦ idealTensorFunctor I)
        hcomp uMap α β
      (by intro R S a M N f hf; have := hf; exact scalar_map_epi a f) h6 hepi,
    familyLaw9 (fun a ↦ SheafOfModules.RingedTensor.tensorFunctor a) (fun I ↦ idealTensorFunctor I)
        hid uMap ε β
      (by intro R S a M N f hf; have := hf; exact scalar_map_epi a f) h6 hepi, familyLaw10 (Fzero :=
          scalarZeroFamily) (Qzero := quotientZeroFamily)
    (fun a ↦ SheafOfModules.RingedTensor.tensorFunctor a) (fun I ↦ idealTensorFunctor I)
      (fun t ↦ (curriedTensor _).flip.map t) q hmono β h7⟩

/-- Balanced scalar associativity for ideal quotient towers, including the local
formulas, augmentation, identity, and composition constraints. `q` and `u` are
uniquely fixed by their displayed section formulas; they are not replacement
transitions or arbitrary augmentations. The final clause gives actual
isomorphisms of towers of unbounded complexes, natural for all cochain maps.

Source: Stacks Project, Modules on Sites, Tags 03EK and 03CY; agent-formulated
balanced quotient calculation, DAG proof steps 1--11.
(blueprint: lem-pur-ideal-quotient-tower-scalar-associator).

Proof plan:
1. The sectionwise balanced tensor universal property and unique sheafification
   factorization identify maps out of scalar extension with maps into restriction.
2. The tensor/ideal-quotient theorem identifies the quotient augmentation with
   the epic projection with kernel the locally saturated ideal product.
3. The map p to (p tensor 1) tensor 1 kills I. Factor it through the quotient
   augmentation and extend scalars to construct beta, with its displayed formula.
4. Extend p to (p tensor 1) tensor 1 in the other order. The resulting map kills
   the locally generated extension ideal, so it descends to the inverse of beta.
5. Maps out of either source are detected on these generating maps. The two
   composites are identities by the formulas, proving invertibility.
6. Apply the same detection to arbitrary module maps to prove naturality.
7. For I' contained in I, both transition composites take p to the same tensor;
   the tensor/ideal-quotient transition equations prove equality.
8. Apply the construction in every integer degree. Naturality for differentials
   makes it a cochain isomorphism; Step 7 makes it a strict tower isomorphism.
   Local generators show that extending an ideal twice equals direct extension.
9. Construct alpha by the scalar-extension universal property twice, with
   inverse p tensor q to (p tensor 1) tensor q. Detection proves the inverse laws.
10. On each original triple tensor, both composition routes give
    (p tensor b(s)q) tensor the image of r. Detection gives equality as maps;
    Step 8 gives equality of the strict tower cochain maps.
11. The formulas preserve the quotient augmentations. For the identity map,
    scalar multiplication identifies beta with the identity. These arguments
    require neither flatness nor a degree bound, and use no completion or limit. -/
theorem ideal_quotient_tower_scalar_associator :
    ∃ (q : ∀ (R : Sheaf J CommRingCat.{u}) (I' I : RingedSiteIdeal R),
        IsContained I' I → (quotientCoefficient I' ⟶ quotientCoefficient I))
      (hmono : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S)
        (I' I : RingedSiteIdeal R), IsContained I' I →
          IsContained (I'.extension a) (I.extension a))
      (hcomp : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V)
        (I : RingedSiteIdeal R), (I.extension a).extension b = I.extension (a ≫ b))
      (hid : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        I.extension (𝟙 R) = I)
      (uMap : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        𝟭 (SheafOfModules.{u} (siteModuleRings R)) ⟶ idealTensorFunctor I)
      (α : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V),
        SheafOfModules.RingedTensor.tensorFunctor a ⋙
          SheafOfModules.RingedTensor.tensorFunctor b ≅
            SheafOfModules.RingedTensor.tensorFunctor (a ≫ b))
      (ε : ∀ R : Sheaf J CommRingCat.{u},
        SheafOfModules.RingedTensor.tensorFunctor (𝟙 R) ≅
          𝟭 (SheafOfModules.{u} (siteModuleRings R)))
      (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        idealTensorFunctor I ⋙ SheafOfModules.RingedTensor.tensorFunctor a ≅
          SheafOfModules.RingedTensor.tensorFunctor a ⋙ idealTensorFunctor (I.extension a)),
    IdealScalarTransitionFormula q ∧
    IdealScalarUnitFormula uMap ∧
    IdealScalarAssociatorFormula α ∧
    IdealScalarIdentityFormula ε ∧
    IdealScalarQuotientFormula β ∧
    IdealScalarAugmentationCompatibility uMap β ∧
    IdealScalarTransitionCompatibility q hmono β ∧
    IdealScalarCompositionCompatibility hcomp α β ∧
    IdealScalarIdentityCompatibility hid ε β ∧
    IdealScalarTowerCompatibility q hmono β := by
  exact ⟨(fun _ _ _ h ↦ quotientCoefficientTransition h),
    (fun _ _ a I' I h ↦ extension_mono a I' I h),
    (fun _ _ _ a b I ↦ extension_comp a b I), (fun _ I ↦ extension_id I),
    (fun _ I ↦ quotientUnit I), (fun _ _ _ a b ↦ sealedAssoc a b), sealedIdentity,
    (fun _ _ a I ↦ sealedBeta a I),
    assembleSeven (J := J) (fun _ _ _ h ↦ quotientCoefficientTransition h)
      (fun _ _ a I' I h ↦ extension_mono a I' I h)
      (fun _ _ _ a b I ↦ extension_comp a b I) (fun _ I ↦ extension_id I)
      (fun _ I ↦ quotientUnit I) (fun _ _ _ a b ↦ sealedAssoc a b) sealedIdentity
      (fun _ _ a I ↦ sealedBeta a I)
      scalarLaw1 scalarLaw2 scalarLaw3 scalarLaw4 scalarLaw5 scalarLaw6 scalarLaw7
      (augmentation_epi (J := J))⟩

end CategoryTheory.RingedSiteIdeal
