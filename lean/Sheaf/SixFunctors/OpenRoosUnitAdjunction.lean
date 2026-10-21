/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.RoosIntrinsicCompletenessEquivalence
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.GroupTheory.Torsion
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.SixFunctors.IntegralRoosReflector
import Sheaf.SixFunctors.OpenRoosCoefficientOperations
import Sheaf.SixFunctors.OpenRoosFunctorTransport
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Mathlib.GroupTheory.OrderOfElement

/-! # Actual open completion units and the complete open adjunction

Source: Stacks Project, Tags 099M, 099N (2),(5), and 09BN; Bhatt--Scholze,
Proposition 3.5.1 and Definition 3.5.2, p.24
(blueprint: lem-sf-open-roos-unit-adjunction).

The quotient completion and its unit are the published strict augmented Roos
construction. The comparison is characterized uniquely by compatibility with this
unit; the normalized exact-product construction gives precisely that comparison.
The index n denotes the positive exponent n+1. Coefficient and site universes are
independent, and all derived categories and complexes are unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u c v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.OpenRoos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The published intrinsic Koszul-unit condition, specialized to the actual uniformizer.
Quantification over representatives avoids adding a choice to complete objects.
Source: Stacks 099B, 0A0E; the integral specialization of intrinsic completion in
RoosIntrinsicCompletenessEquivalence (blueprint: lem-sf-open-roos-unit-adjunction). -/
abbrev Intrinsic (T : Scheme.{t}) (K : IntegralOnSlice.D l E T none) : Prop :=
  ∀ (C : IntegralOnSlice.Cx l E T none) (e : DerivedCategory.Q.obj C ≅ K),
    IsIso (integralKoszulIntrinsicUnit l E T K C e)

/-- The four reflector assertions, all for the actual quotient-augmentation unit.
Source: Stacks 099M and 099B (blueprint: lem-sf-open-roos-unit-adjunction). -/
def ReflectorAssertions (T : Scheme.{t}) : Prop :=
  (∀ H : IntegralOnSlice.D l E T none,
    Intrinsic l E T ((IntegralOnSlice.completion l E T none).obj H)) ∧
  (∀ H L : IntegralOnSlice.D l E T none, Intrinsic l E T L →
    Function.Bijective (fun f : (IntegralOnSlice.completion l E T none).obj H ⟶ L ↦
      (IntegralOnSlice.completionUnit l E T none).app H ≫ f)) ∧
  (∀ H : IntegralOnSlice.D l E T none,
    IntegralOnSlice.IsComplete l E T none H ↔
      IsIso ((IntegralOnSlice.completionUnit l E T none).app H)) ∧
  (∀ H : IntegralOnSlice.D l E T none,
    IsIso ((IntegralOnSlice.completionUnit l E T none).app H) ↔ Intrinsic l E T H)

/-- The full complete category, using the recorded Roos-triangle predicate verbatim.
Source: Bhatt--Scholze Definition 3.5.2
(blueprint: lem-sf-open-roos-unit-adjunction). -/
abbrev Complete (T : Scheme.{t}) :=
  ObjectProperty.FullSubcategory (IntegralOnSlice.IsComplete l E T none)

variable {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
  (o : IntegralOpenReduction.Operations l E e)

/-- Literal restriction of the ordinary derived extension to complete objects.
Source: Stacks 09BN (blueprint: lem-sf-open-roos-unit-adjunction). -/
def completeExtension
    (h : ∀ M, IntegralOnSlice.IsComplete l E V none M →
      IntegralOnSlice.IsComplete l E W none ((IntegralOpenReduction.shriek l E e o).obj M)) :
    Complete l E V ⥤ Complete l E W :=
  ObjectProperty.lift _
    ((ObjectProperty.ι (IntegralOnSlice.IsComplete l E V none)) ⋙
      IntegralOpenReduction.shriek l E e o)
    (fun M ↦ h M.obj M.property)

/-- Literal restriction of ordinary derived open restriction to complete objects.
Source: Stacks 099N (2),(5) (blueprint: lem-sf-open-roos-unit-adjunction). -/
def completeRestriction
    (h : ∀ H, IntegralOnSlice.IsComplete l E W none H →
      IntegralOnSlice.IsComplete l E V none ((IntegralOpenReduction.star l E e o).obj H)) :
    Complete l E W ⥤ Complete l E V :=
  ObjectProperty.lift _
    ((ObjectProperty.ι (IntegralOnSlice.IsComplete l E W none)) ⋙
      IntegralOpenReduction.star l E e o)
    (fun H ↦ h H.obj H.property)

/-- The actual pulled quotient tower's Roos derived-limit model on good representatives.
The restriction is applied to the entire strict tower, retaining its transitions.
Source: Stacks 099N (5), 0941 (blueprint: lem-sf-open-roos-unit-adjunction). -/
def pulledRoos : (IntegralOnSlice.Good l E W none).FullSubcategory ⥤
    IntegralOnSlice.D l E V none :=
  (IntegralOnSlice.Good l E W none).ι ⋙ IntegralOnSlice.tower l E W none ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      ((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)) ⋙
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q

/-- The actual pulled augmentation: apply restriction to (gamma,0), then the map
which is the canonical product comparison in BOTH Roos coordinates.
Source: Stacks 099N (5), 0941 (blueprint: lem-sf-open-roos-unit-adjunction). -/
def pulledUnit (P : IntegralOnSlice.Cx l E W none) :=
  ((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)).map
      (IntegralOnSlice.roosUnit l E W none P) ≫
    scalarRoosMap (IntegralOpenReduction.restriction l E e o)
      ((IntegralOnSlice.tower l E W none).obj P)

section LocalUnit
open SheafOfModules
open Classical in
private theorem extensionRestrict_of
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max c v r}) (U : C)
    (F : SheafOfModules.{max c v r} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W)
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
private noncomputable def extensionSectionIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J RingCat.{max c v r}) (U V : C) [Subsingleton (V ⟶ U)] (φ : V ⟶ U)
    (F : SheafOfModules.{max c v r} (R.over U)) :
    F.val.obj (op (Over.mk φ)) ≅ (extensionByZeroPresheaf.{max c v r} R U).obj F |>.obj (op V) := by
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
private noncomputable def extensionRestrictionIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J RingCat.{max c v r}) (U : C)
    (hU : ∀ V : C, Subsingleton (V ⟶ U))
    (F : SheafOfModules.{max c v r} (R.over U)) :
    ((SheafOfModules.toSheaf (R.over U)).obj F).obj ≅
      (Over.forget U).op ⋙ ((extensionByZeroPresheaf.{max c v r} R U).obj F).presheaf := by
  refine NatIso.ofComponents (fun V ↦ ?_) ?_
  · let := hU V.unop.left
    exact (forget₂ (ModuleCat (R.obj.obj (op V.unop.left))) AddCommGrpCat).mapIso
      (extensionSectionIso.{c, v, r} R U V.unop.left V.unop.hom F)
  · intro V W a
    let := hU V.unop.left
    let := hU W.unop.left
    ext x
    change _ = extensionByZeroPresheafRestrictAdd R U F
      ((Over.forget U).op.map a) (DirectSum.of _ V.unop.hom x)
    erw [extensionRestrict_of.{c, v, r} R U F ((Over.forget U).op.map a)
      V.unop.hom W.unop.hom (by exact a.unop.w)]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem extensionSheafAdjunction_unit_isIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (B : Sheaf J CommRingCat.{max c v r})
    (U : C)
    (hU : ∀ V : C, Subsingleton (V ⟶ U))
    (F : SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj B).over U)) :
    IsIso ((SheafOfModules.localizedSystemAdjunction.{c, v, r} B U).unit.app F) := by
  let R := (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj B
  let P := ((extensionByZeroPresheaf.{max c v r} R U).obj F).presheaf
  let T := (Over.forget U).op ⋙ P
  have hT : Presheaf.IsSheaf (J.over U) T :=
    (Presheaf.isSheaf_of_iso_iff (extensionRestrictionIso.{c, v, r} R U hU F)).mp
      ((SheafOfModules.toSheaf.{max c v r} _).obj F).property
  have : IsIso (toSheafify (J.over U) T) := isIso_toSheafify _ hT
  have hh := (Over.forget U).toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat.{max c v r} (J.over U) J P
  have : IsIso (Functor.whiskerLeft (Over.forget U).op (toSheafify J P)) := by
    rw [← hh]
    infer_instance
  let η := (SheafOfModules.localizedSystemAdjunction.{c, v, r} B U).unit.app F
  have hη : ((SheafOfModules.toSheaf.{max c v r} _).map η).hom =
      (extensionRestrictionIso.{c, v, r} R U hU F).hom ≫
        Functor.whiskerLeft (Over.forget U).op (toSheafify J P) := by
    ext V x
    exact (SheafOfModules.localizedSystemAdjunction_existsUnique.{c, v, r}
      B U).exists.choose_spec F V x
  have : IsIso ((sheafToPresheaf (J.over U) AddCommGrpCat.{max c v r}).map
      ((SheafOfModules.toSheaf.{max c v r} _).map η)) := by
    change IsIso (((SheafOfModules.toSheaf.{max c v r} _).map η).hom)
    rw [hη]
    infer_instance
  have : IsIso ((SheafOfModules.toSheaf.{max c v r} _).map η) :=
    isIso_of_reflects_iso _ (sheafToPresheaf (J.over U) AddCommGrpCat.{max c v r})
  exact isIso_of_reflects_iso η (SheafOfModules.toSheaf.{max c v r} _)

end LocalUnit

private theorem openSubterminal (T : W.ProEt) :
    Subsingleton (T ⟶ IntegralOpenReduction.openObject e) := by
  constructor
  intro a b
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono e).mp
  exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm

private theorem ordinaryOpenUnit (M : scalarReductionSource l E V) :
    IsIso ((IntegralOpenReduction.ordinaryAdjunction l E e o).unit.app M) := by
  have h := extensionSheafAdjunction_unit_isIso.{t + 1, t, max u (t + 1)}
    (completedIntegralCommRingSheafUnrestricted l E W)
    (IntegralOpenReduction.openObject e) (openSubterminal e) (o.integral.functor.obj M)
  dsimp only [IntegralOpenReduction.ordinaryAdjunction]
  rw [Adjunction.comp_unit_app]
  infer_instance

private theorem derivedOpenUnit (M : IntegralOnSlice.D l E V none) :
    IsIso ((IntegralOpenReduction.openAdjunction l E e o).unit.app M) := by
  let a := IntegralOpenReduction.openAdjunction l E e o
  have hQ (P : IntegralOnSlice.Cx l E V none) :
      IsIso (a.unit.app (DerivedCategory.Q.obj P)) := by
    have hP : IsIso
        (((IntegralOpenReduction.ordinaryAdjunction l E e o).mapHomologicalComplex
          (.up ℤ)).unit.app P) := by
      have hn : ∀ n : ℤ, IsIso
          ((((IntegralOpenReduction.ordinaryAdjunction l E e o).mapHomologicalComplex
            (.up ℤ)).unit.app P).f n) := fun n ↦ ordinaryOpenUnit l E e o (P.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    have hu : a.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map
          (((IntegralOpenReduction.ordinaryAdjunction l E e o).mapHomologicalComplex
            (.up ℤ)).unit.app P) ≫
        (IntegralOpenReduction.restriction l E e o).mapDerivedCategoryFactors.inv.app _ ≫
        (IntegralOpenReduction.star l E e o).map
          ((IntegralOpenReduction.extension l E e o).mapDerivedCategoryFactors.inv.app P) := by
      simp only [a, IntegralOpenReduction.openAdjunction,
        SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction,
        Adjunction.localization_unit_app]
      rfl
    rw [hu]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso a.unit (DerivedCategory.Q.objObjPreimageIso M)).mp
    (hQ (DerivedCategory.Q.objPreimage M))

private theorem restrictedOpenAdjunction
    (hExtension : ∀ M, IntegralOnSlice.IsComplete l E V none M →
      IntegralOnSlice.IsComplete l E W none
        ((IntegralOpenReduction.shriek l E e o).obj M))
    (hRestriction : ∀ H, IntegralOnSlice.IsComplete l E W none H →
      IntegralOnSlice.IsComplete l E V none
        ((IntegralOpenReduction.star l E e o).obj H)) :
    Nonempty ((completeExtension l E e o hExtension).FullyFaithful) ∧
    ∃ a : completeExtension l E e o hExtension ⊣ completeRestriction l E e o hRestriction,
      (∀ M : Complete l E V,
        (a.unit.app M).hom = (IntegralOpenReduction.openAdjunction l E e o).unit.app M.obj) ∧
      (∀ H : Complete l E W,
        (a.counit.app H).hom =
          (IntegralOpenReduction.openAdjunction l E e o).counit.app H.obj) := by
  let iV := ObjectProperty.ι (IntegralOnSlice.IsComplete l E V none)
  let iW := ObjectProperty.ι (IntegralOnSlice.IsComplete l E W none)
  let a := (IntegralOpenReduction.openAdjunction l E e o).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (L := completeExtension l E e o hExtension)
    (R := completeRestriction l E e o hRestriction) (Iso.refl _) (Iso.refl _)
  have hu (M : Complete l E V) : (a.unit.app M).hom =
      (IntegralOpenReduction.openAdjunction l E e o).unit.app M.obj := by
    simpa using (IntegralOpenReduction.openAdjunction l E e o).map_restrictFullyFaithful_unit_app
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (L := completeExtension l E e o hExtension)
        (R := completeRestriction l E e o hRestriction) (Iso.refl _) (Iso.refl _) M
  have hc (H : Complete l E W) : (a.counit.app H).hom =
      (IntegralOpenReduction.openAdjunction l E e o).counit.app H.obj := by
    have h := (IntegralOpenReduction.openAdjunction l E e o).map_restrictFullyFaithful_counit_app
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (L := completeExtension l E e o hExtension)
      (R := completeRestriction l E e o hRestriction) (Iso.refl _) (Iso.refl _) H
    change (a.counit.app H).hom = 𝟙 _ ≫
      (IntegralOpenReduction.shriek l E e o).map (𝟙 _) ≫
      (IntegralOpenReduction.openAdjunction l E e o).counit.app H.obj at h
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp] at h
    exact h
  have hunit (M : Complete l E V) : IsIso (a.unit.app M) := by
    have : IsIso (iV.map (a.unit.app M)) := by
      change IsIso ((a.unit.app M).hom)
      rw [hu]
      exact derivedOpenUnit l E e o M.obj
    exact isIso_of_reflects_iso _ iV
  have : IsIso a.unit := NatIso.isIso_of_isIso_app _
  exact ⟨⟨a.fullyFaithfulLOfIsIsoUnit⟩, a, hu, hc⟩

private theorem finiteMapIsIso
    {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
    (o : IntegralOpenReduction.Operations l E e) (n : ℕ) : IsIso (o.finiteMap n) := by
  let U := IntegralOpenReduction.openObject e
  let F := IntegralOpenReduction.sliceSite e
  have : (ProEt.sliceEquiv W U).inverse.IsDenseSubsite
      (ProEt.topology V) ((ProEt.topology W).over U) := ProEt.sliceDense W U
  have : F.IsCocontinuous ((ProEt.topology W).over U) (ProEt.topology V) :=
    inferInstanceAs ((ProEt.sliceEquiv W U).functor.IsCocontinuous _ _)
  let : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  let : HasSheafify ((ProEt.topology W).over U) CommRingCat.{max u (t + 1)} :=
    hasSheafifyEssentiallySmallSite _ _
  let A := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let a := (Over.forget U).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)} ((ProEt.topology W).over U) (ProEt.topology W)
  let b := F.pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)} ((ProEt.topology W).over U) (ProEt.topology V)
  let aA := a.app ((Functor.const W.ProEtᵒᵖ).obj A)
  let bA := b.app ((Functor.const V.ProEtᵒᵖ).obj A)
  have h : aA.hom ≫ o.finiteMap n = bA.hom := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext
      (J := (ProEt.topology W).over U) _ _
      (((F.sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        ((ProEt.topology W).over U) (ProEt.topology V)).obj
          (integralCoefficientCommRingSheaf l E V n)).property)
    simp only [ObjectProperty.FullSubcategory.comp_hom]
    rw [← Category.assoc]
    erw [(Over.forget U).toSheafify_pullbackSheafificationCompatibility
      CommRingCat.{max u (t + 1)} ((ProEt.topology W).over U) (ProEt.topology W)]
    erw [F.toSheafify_pullbackSheafificationCompatibility
      CommRingCat.{max u (t + 1)} ((ProEt.topology W).over U) (ProEt.topology V)]
    apply NatTrans.ext
    funext T
    exact o.finiteConstants n T.unop
  have : IsIso (aA.hom ≫ o.finiteMap n) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left aA.hom (o.finiteMap n)

private theorem horizontal {C : Type (t + 1)} [Category.{t} C]
    (F : ℕᵒᵖ ⥤ Cᵒᵖ ⥤ CommRingCat.{max u (t + 1)})
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) :
    ((prodOpEquiv (C := ℕ) (D := C)).functor ⋙ Functor.uncurry.obj F).map
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op = (F.map (homOfLE h).op).app U := by
  dsimp
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem finiteTransitions
    {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
    (o : IntegralOpenReduction.Operations l E e) (n : ℕ) :
        o.finiteMap (n + 1) ≫
          ((IntegralOpenReduction.sliceSite e).sheafPushforwardContinuous
            CommRingCat.{max u (t + 1)} ((ProEt.topology W).over
              (IntegralOpenReduction.openObject e)) (ProEt.topology V)).map
                (coefficientSequenceCommRingTransition l E V n) =
        ((ProEt.topology W).overPullback CommRingCat.{max u (t + 1)}
          (IntegralOpenReduction.openObject e)).map
            (coefficientSequenceCommRingTransition l E W n) ≫ o.finiteMap n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  have h := o.systemMap.hom.naturality
    (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 T.unop)).op
  rw [o.systemComponents, o.systemComponents] at h
  symm at h
  change _ ≫ (coefficientSequenceCommRingPresheaf l E V).map
      (Prod.mkHom (homOfLE (Nat.le_succ n))
        (𝟙 ((IntegralOpenReduction.sliceSite e).obj T.unop))).op =
    (SemilinearSections.ringPresheaf _ _ _).map
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 T.unop)).op ≫ _ at h
  dsimp only [SemilinearSections.ringPresheaf, coefficientSequenceCommRingPresheaf] at h
  rw [horizontal, horizontal] at h
  dsimp only [SemilinearSections.rings, coefficientSequenceCommRingSystem] at h
  simp only [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ] at h
  exact h


private theorem completedMapIsIso
    {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
    (o : IntegralOpenReduction.Operations l E e) : IsIso o.completedMap := by
  let U := IntegralOpenReduction.openObject e
  let F := IntegralOpenReduction.sliceSite e
  let Φ := sheafCompose ((ProEt.topology W).over U)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  suffices IsIso (Φ.map o.completedMap) from isIso_of_reflects_iso _ Φ
  suffices IsIso ((sheafToPresheaf _ RingCat.{max u (t + 1)}).map
      (Φ.map o.completedMap)) from
    isIso_of_reflects_iso _ (sheafToPresheaf _ RingCat.{max u (t + 1)})
  have hcomp : ∀ T, IsIso (((sheafToPresheaf _ RingCat.{max u (t + 1)}).map
      (Φ.map o.completedMap)).app T) := by
    intro T
    let evW := sheafToPresheaf (ProEt.topology W) RingCat.{max u (t + 1)} ⋙
      (evaluation _ RingCat.{max u (t + 1)}).obj (op T.unop.left)
    let evV := sheafToPresheaf (ProEt.topology V) RingCat.{max u (t + 1)} ⋙
      (evaluation _ RingCat.{max u (t + 1)}).obj (op (F.obj T.unop))
    let DW := integralCoefficientSheafSystem l E W
    let DV := integralCoefficientSheafSystem l E V
    let α : DW ⋙ evW ⟶ DV ⋙ evV := NatTrans.ofOpSequence
      (fun n ↦ (forget₂ CommRingCat RingCat).map ((o.finiteMap n).hom.app T))
      (fun n ↦ by
        have h := congrArg (fun f ↦ (forget₂ CommRingCat RingCat).map (f.hom.app T))
          (finiteTransitions l E e o n)
        simp only [DW, DV, evW, evV, Functor.comp_map, integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
        apply RingCat.hom_ext
        ext x
        exact congrArg (fun f ↦ f.hom x) h.symm)
    have hα (n : ℕᵒᵖ) : IsIso (α.app n) := by
      have := finiteMapIsIso l E e o n.unop
      exact inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map
        (((sheafToPresheaf _ CommRingCat).map (o.finiteMap n.unop)).app T)))
    have : IsIso α := NatIso.isIso_of_isIso_app _
    let CW := evW.mapCone (limit.cone DW)
    let CV := evV.mapCone (limit.cone DV)
    have hCW : IsLimit CW := isLimitOfPreserves evW (limit.isLimit DW)
    have hCV : IsLimit CV := isLimitOfPreserves evV (limit.isLimit DV)
    let c : ((Cone.postcompose α).obj CW) ⟶ CV :=
      { hom := ((sheafToPresheaf _ RingCat).map (Φ.map o.completedMap)).app T
        w := by
          intro n
          have h := congrArg (fun f ↦ (forget₂ CommRingCat RingCat).map (f.hom.app T))
            (o.projections n.unop)
          exact h }
    have : IsIso c := ((IsLimit.postcomposeHomEquiv (asIso α) CW).symm hCW).hom_isIso hCV c
    exact (Cone.forget _).map_isIso c
  exact NatIso.isIso_of_isIso_app _


private theorem completeUnitIff
    (p : ℕ) [Fact p.Prime] (hpl : p ≠ l) (T : Scheme.{t})
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (H : IntegralOnSlice.D l E T none) :
    IntegralOnSlice.IsComplete l E T none H ↔
      IsIso ((IntegralOnSlice.completionUnit l E T none).app H) := by
  let : EssentiallySmall.{max u (t + 1)} (IntegralOnSlice.Site T none) :=
    essentiallySmallSelf _
  obtain ⟨P, f, hP, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (J := IntegralOnSlice.topology T none) (R := IntegralOnSlice.ring l E T none)
      (DerivedCategory.Q.objPreimage H)
  have hs : ∀ i, SheafOfModules.IsFlatOnSite
      (J := IntegralOnSlice.topology T none) (R := IntegralOnSlice.ring l E T none)
      (P.X i) := fun i ↦ (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (IntegralOnSlice.ring l E T none)
          (P.X i)).symm (hflat i)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := f)).2 hf
  exact (roosIntrinsicCompletenessEquivalence p l hpl E T d hd H ⟨P, hP, hs⟩
    (asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso H)).out 0 4

private theorem coefficientFacts :
    ∃ d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E),
      d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E} := by
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hpid : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
    h.2.2.2.2.2.2.2.2.1
  have hfinite (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  refine ⟨{
    ideal := Ideal.span {Padic.coefficientExtensionUniformizer l E}
    noetherian := inferInstance
    finitelyGenerated := Submodule.fg_span_singleton _
    quotientFinite := hfinite
    quotientTorsion := ?_
    quotientPerfect := ?_ }, rfl⟩
  · have : Finite (Padic.coefficientExtensionIntegers l E ⧸
        Ideal.span {Padic.coefficientExtensionUniformizer l E}) := by
      simpa only [Padic.coefficientExtensionRing, Padic.coefficientExtensionIdeal,
        Nat.zero_add, pow_one] using hfinite 0
    intro x
    exact (isOfFinAddOrder_of_finite x).exists_nsmul_eq_zero
  · intro n hn
    obtain ⟨P, hge, hle, hfree, _, hrest⟩ :=
      (AlgebraicGeometry.standard_quotients_perfect l n hn).2 E
    obtain ⟨_, _, _, φ, ε, hε, _, _, _⟩ := hrest
    have hqi : QuasiIso ε := by
      have hiso : IsIso (DerivedCategory.Q.map ε) := by
        rw [hε]
        infer_instance
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := ε)).1 hiso
    let := HasDerivedCategory.standard
      (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E))
    unfold adicQuotientPerfect
    refine ⟨P, -1, 0, hge, hle, ?_, ?_⟩
    · intro i
      have := (hfree i).1
      exact ⟨inferInstance, (hfree i).2⟩
    · exact ⟨(asIso (DerivedCategory.Q.map ε)).symm⟩

private theorem coefficientExact (n : ℕ) :
    Function.Injective (fun x : Padic.coefficientExtensionIntegers l E ↦
      Padic.coefficientExtensionUniformizer l E ^ (n + 1) * x) ∧
    Function.Exact (fun x : Padic.coefficientExtensionIntegers l E ↦
      Padic.coefficientExtensionUniformizer l E ^ (n + 1) * x)
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) ∧
    Function.Surjective
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have ht : Padic.coefficientExtensionUniformizer l E ≠ 0 := by
    intro ht
    have hz := h.2.2.2.2.2.2.2.2.2.1
    apply hz
    change Padic.coefficientExtensionMaximalIdeal l E = ⊥
    rw [← hgen, ht, Ideal.span_singleton_zero]
  refine ⟨mul_right_injective₀ (pow_ne_zero (n + 1) ht), ?_,
    Ideal.Quotient.mk_surjective⟩
  intro x
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change x ∈ (Ideal.span {Padic.coefficientExtensionUniformizer l E}) ^ (n + 1) ↔ _
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩

/-- Roos completeness, reflection by the actual unit, and the complete open adjunction.

Source: Stacks 099M, 099N (2),(5), 09BN; Bhatt--Scholze 3.5.1--3.5.2, p.24
(blueprint: lem-sf-open-roos-unit-adjunction).

Proof:
1. The extension-integers DVR theorem gives a Noetherian PID R and a nonzero
uniformizer. Finite DVR quotients are finite, hence A_1 is additive torsion.
Multiplication by t^(n+1) is injective with cokernel A_(n+1), giving the displayed
rank-one finite free resolution and every adic-datum hypothesis.
2. Finite type over the field gives Noetherian V,W, hence qcqs. Every open in a
Noetherian scheme is quasi-compact; therefore e is quasi-compact, including the empty open.
3. Weakly-etale localization identifies the open site with the slice. Constant
sections identify each finite coefficient. Quotient maps commute on constants;
immersion inverse image preserves the completed limit and every projection.
4. The ringed Koszul reflector and the unit-compatible completed Koszul/quotient
comparison identify the Koszul unit (u,0) with the actual strict quotient unit.
Strict Roos comparison preserves this augmentation. The Roos/intrinsic equivalence
then gives complete output, the stated Hom bijection and both predicate equivalences.
5. Take a flat-term K-flat representative. Exact ringed restriction preserves it.
The tensor restriction map sends each tensor to the same restricted tensor, commuting
with every quotient and with x mapped to x tensor 1. This yields one strict tower
comparison before localization, natural and independent of representatives.
6. Apply the normalized exact-product strict-limit comparison to that tower map.
Its augmentation clause proves rho composed with e*eta equals eta on e*H.
The reflector Hom bijection makes this unit-compatible natural isomorphism unique.
The pulledRoos model is the strict pulled quotient tower, and pulledUnit retains
both product coordinates. Descent supplies C,c,chi; b identifies it with completion
of restriction, and chi followed by b is exactly the actual completion unit.
Thus restriction preserves completeness and this comparison is invertible on
complete inputs.
7. Exact open extension preserves countable products since e is quasi-compact.
The simultaneous open semilinear tensor model commutes with reductions and their
augmentations. Exact-product strict limits therefore show it preserves completeness.
8. Restrict the actual exact open adjunction to the full complete subcategories.
Its unit and counit are those of the ambient adjunction, as the two formulas assert.
The slice unit is summand insertion, and collapse on the open is its inverse; hence
it is the identity under that section identification. Termwise localization gives
the representative formula below, and invertibility of the unit gives full faithfulness. -/
theorem openRoosUnitAdjunction
    (D : FiniteFieldDatum.{t}) (_hl : l ≠ D.p)
    [V.Over (Spec (CommRingCat.of D.k))] [W.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (V ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (W ↘ Spec (CommRingCat.of D.k))]
    [e.IsOver (Spec (CommRingCat.of D.k))] :
    IsNoetherian V ∧ IsNoetherian W ∧ CompactSpace V ∧ CompactSpace W ∧
    QuasiSeparatedSpace V ∧ QuasiSeparatedSpace W ∧ QuasiCompact e ∧
    IsNoetherianRing (Padic.coefficientExtensionIntegers l E) ∧
    IsAddTorsion (Padic.coefficientExtensionRing l E 1) ∧
    (∃ d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E),
      d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) ∧
    (∀ n : ℕ, Finite (Padic.coefficientExtensionRing l E (n + 1)) ∧
      Function.Injective (fun x : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ (n + 1) * x) ∧
      Function.Exact (fun x : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ (n + 1) * x)
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) ∧
      Function.Surjective
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))) ∧
    ReflectorAssertions l E W ∧ ReflectorAssertions l E V ∧
    ∃ o : IntegralOpenReduction.Operations l E e,
      (∀ n : ℕ, IsIso (o.finiteMap n)) ∧ IsIso o.completedMap ∧
      (∀ n : ℕ,
        o.finiteMap (n + 1) ≫
          ((IntegralOpenReduction.sliceSite e).sheafPushforwardContinuous
            CommRingCat.{max u (t + 1)} ((ProEt.topology W).over
              (IntegralOpenReduction.openObject e)) (ProEt.topology V)).map
                (coefficientSequenceCommRingTransition l E V n) =
        ((ProEt.topology W).overPullback CommRingCat.{max u (t + 1)}
          (IntegralOpenReduction.openObject e)).map
            (coefficientSequenceCommRingTransition l E W n) ≫ o.finiteMap n) ∧
      (∃! rho : IntegralOnSlice.completion l E W none ⋙ IntegralOpenReduction.star l E e o ≅
          IntegralOpenReduction.star l E e o ⋙ IntegralOnSlice.completion l E V none,
        ∀ H : IntegralOnSlice.D l E W none,
          (IntegralOpenReduction.star l E e o).map
              ((IntegralOnSlice.completionUnit l E W none).app H) ≫ rho.hom.app H =
            (IntegralOnSlice.completionUnit l E V none).app
              ((IntegralOpenReduction.star l E e o).obj H)) ∧
      (∃ (C : IntegralOnSlice.D l E W none ⥤ IntegralOnSlice.D l E V none)
        (c : IntegralOnSlice.qGood l E W none ⋙ C ≅ pulledRoos l E e o)
        (chi : IntegralOpenReduction.star l E e o ⟶ C)
        (b : C ≅ IntegralOpenReduction.star l E e o ⋙ IntegralOnSlice.completion l E V none),
        (∀ P : (IntegralOnSlice.Good l E W none).FullSubcategory,
          chi.app (DerivedCategory.Q.obj P.obj) ≫ c.hom.app P =
            (IntegralOpenReduction.restriction l E e o).mapDerivedCategoryFactors.hom.app P.obj ≫
              DerivedCategory.Q.map (pulledUnit l E e o P.obj)) ∧
        (∀ H : IntegralOnSlice.D l E W none,
          chi.app H ≫ b.hom.app H = (IntegralOnSlice.completionUnit l E V none).app
            ((IntegralOpenReduction.star l E e o).obj H))) ∧
      ∃ (hExtension : ∀ M, IntegralOnSlice.IsComplete l E V none M →
          IntegralOnSlice.IsComplete l E W none
            ((IntegralOpenReduction.shriek l E e o).obj M))
        (hRestriction : ∀ H, IntegralOnSlice.IsComplete l E W none H →
          IntegralOnSlice.IsComplete l E V none
            ((IntegralOpenReduction.star l E e o).obj H)),
        (∀ H : IntegralOnSlice.D l E W none, IntegralOnSlice.IsComplete l E W none H →
          IsIso ((IntegralOnSlice.completionUnit l E V none).app
            ((IntegralOpenReduction.star l E e o).obj H))) ∧
        (∀ M : IntegralOnSlice.D l E V none, IntegralOnSlice.IsComplete l E V none M →
          IsIso ((IntegralOpenReduction.openAdjunction l E e o).unit.app M)) ∧
        (∀ P : IntegralOnSlice.Cx l E V none,
          (IntegralOpenReduction.openAdjunction l E e o).unit.app (DerivedCategory.Q.obj P) =
            DerivedCategory.Q.map
              (((IntegralOpenReduction.ordinaryAdjunction l E e o).mapHomologicalComplex
                (.up ℤ)).unit.app P) ≫
            (IntegralOpenReduction.restriction l E e o).mapDerivedCategoryFactors.inv.app _ ≫
            (IntegralOpenReduction.star l E e o).map
              ((IntegralOpenReduction.extension l E e o).mapDerivedCategoryFactors.inv.app P)) ∧
        Nonempty ((completeExtension l E e o hExtension).FullyFaithful) ∧
        ∃ a : completeExtension l E e o hExtension ⊣ completeRestriction l E e o hRestriction,
          (∀ M : Complete l E V,
            (a.unit.app M).hom = (IntegralOpenReduction.openAdjunction l E e o).unit.app M.obj) ∧
          (∀ H : Complete l E W,
            (a.counit.app H).hom =
              (IntegralOpenReduction.openAdjunction l E e o).counit.app H.obj) := by
  let : IsLocallyNoetherian V :=
    LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (CommRingCat.of D.k))
  let : IsLocallyNoetherian W :=
    LocallyOfFiniteType.isLocallyNoetherian (W ↘ Spec (CommRingCat.of D.k))
  let : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace
    (V ↘ Spec (CommRingCat.of D.k))
  let : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace
    (W ↘ Spec (CommRingCat.of D.k))
  let : IsNoetherian V := ⟨⟩
  let : IsNoetherian W := ⟨⟩
  obtain ⟨d, hd⟩ := coefficientFacts l E
  have : IsNoetherianRing (Padic.coefficientExtensionIntegers l E) := d.noetherian
  have : Finite (Padic.coefficientExtensionRing l E 1) :=
    Padic.finite_coefficientExtensionRing l E 1 le_rfl
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, isAddTorsion_of_finite, ⟨d, hd⟩, ?_, ?_⟩
  · intro n
    exact ⟨Padic.finite_coefficientExtensionRing l E (n + 1) (by omega),
      coefficientExact l E n⟩
  · let : Fact D.p.Prime := ⟨D.prime⟩
    obtain ⟨hWout, hWhom, hWintrinsic⟩ := integralRoosReflector l E W d hd
    have hW : ReflectorAssertions l E W :=
      ⟨hWout, hWhom, completeUnitIff l E D.p _hl.symm W d hd, hWintrinsic⟩
    obtain ⟨hVout, hVhom, hVintrinsic⟩ := integralRoosReflector l E V d hd
    have hV : ReflectorAssertions l E V :=
      ⟨hVout, hVhom, completeUnitIff l E D.p _hl.symm V d hd, hVintrinsic⟩
    obtain ⟨o⟩ := openRoosCoefficientOperations l E e
    have hcompleted := completedMapIsIso l E e o
    have htransition := finiteTransitions l E e o
    have hfinite : ∀ n, IsIso (o.finiteMap n) := finiteMapIsIso l E e o
    obtain ⟨⟨rho, hrho, c, hc⟩, sigma, hsigma⟩ :=
      openRoosFunctorTransport l E e o hfinite hcompleted
    have hExtension : ∀ M, IntegralOnSlice.IsComplete l E V none M →
        IntegralOnSlice.IsComplete l E W none
          ((IntegralOpenReduction.shriek l E e o).obj M) := by
      intro M hM
      have := (hV.2.2.1 M).mp hM
      apply (hW.2.2.1 _).mpr
      rw [← hsigma M]
      infer_instance
    have hRestriction : ∀ H, IntegralOnSlice.IsComplete l E W none H →
        IntegralOnSlice.IsComplete l E V none
          ((IntegralOpenReduction.star l E e o).obj H) := by
      intro H hH
      have := (hW.2.2.1 H).mp hH
      apply (hV.2.2.1 _).mpr
      rw [← hrho H]
      infer_instance
    refine ⟨hW, hV, o, hfinite, hcompleted, htransition, ?_, ?_,
      hExtension, hRestriction, ?_, ?_, ?_, ?_⟩
    · refine ⟨rho, hrho, ?_⟩
      intro rho' hrho'
      apply Iso.ext
      ext H
      apply (cancel_epi (rho.inv.app H)).mp
      apply (hV.2.1 _ _ (hV.1 ((IntegralOpenReduction.star l E e o).obj H))).1
      calc
        (IntegralOnSlice.completionUnit l E V none).app
            ((IntegralOpenReduction.star l E e o).obj H) ≫
            (rho.inv.app H ≫ rho'.hom.app H) =
          (IntegralOpenReduction.star l E e o).map
            ((IntegralOnSlice.completionUnit l E W none).app H) ≫ rho'.hom.app H := by
              rw [← hrho H]
              simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
        _ = (IntegralOnSlice.completionUnit l E V none).app
            ((IntegralOpenReduction.star l E e o).obj H) := hrho' H
        _ = (IntegralOnSlice.completionUnit l E V none).app
            ((IntegralOpenReduction.star l E e o).obj H) ≫
            (rho.inv.app H ≫ rho.hom.app H) := by simp
    · exact ⟨IntegralOnSlice.completion l E W none ⋙ IntegralOpenReduction.star l E e o,
        c, Functor.whiskerRight (IntegralOnSlice.completionUnit l E W none)
          (IntegralOpenReduction.star l E e o), rho, hc, hrho⟩
    · intro H hH
      exact (hV.2.2.1 _).mp (hRestriction H hH)
    · intro M _
      exact derivedOpenUnit l E e o M
    · intro P
      simp only [IntegralOpenReduction.openAdjunction,
        SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction,
        Adjunction.localization_unit_app]
      rfl
    · exact restrictedOpenAdjunction l E e o hExtension hRestriction

end WeilConjectures.OpenRoos
