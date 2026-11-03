/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantCoefficientEquivalence
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedQuotientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor

/-! # The normalized quotient Roos triangle on explicit Koszul completion

This compatibility archive preserves the former interface for the legacy transport
importer while the active item uses the current condensed coefficient route.

Source: blueprint order 1248; Stacks Tags 091Z and 099M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
attribute [local instance 30000] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
variable (d : ProEtaleAdicCoefficientDatum A)

attribute [local irreducible] reductionChange adicDatumExtension adicDatumExtensionCounit

private theorem nativeDerivedUnit
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (C : CochainComplex (completedConstantModules T R) ℤ) :
    (adicDatumAdjunction T φ).unit.app (DerivedCategory.Q.obj C) ≫
        (adicDatumRestriction T φ).map (adicDatumComplexCounit T φ C) ≫
        (SheafOfModules.restrictScalars ((adicLisseForget T).map φ)
          ).mapDerivedCategoryFactors.hom.app
            (((reductionChange T φ).mapHomologicalComplex (.up ℤ)).obj C) =
      DerivedCategory.Q.map
        (((adicDatumOrdinaryAdjunction T φ).mapHomologicalComplex (.up ℤ)).unit.app C) := by
  let U := SheafOfModules.restrictScalars ((adicLisseForget T).map φ)
  let Cₕ := (HomotopyCategory.quotient _ (.up ℤ)).obj C
  have h := (adicDatumAdjunction_exists T φ).choose_spec Cₕ
    (((reductionChange T φ).mapHomotopyCategory (.up ℤ)).obj Cₕ) (𝟙 _)
  simp only [CategoryTheory.Functor.map_id, Adjunction.homEquiv_unit] at h
  erw [Category.comp_id, Category.comp_id] at h
  change (adicDatumAdjunction T φ).unit.app _ ≫
    (adicDatumRestriction T φ).map ((adicDatumExtensionCounit T φ).app Cₕ) = _ at h
  let E := ((reductionChange T φ).mapHomologicalComplex (.up ℤ)).obj C
  have hε : adicDatumComplexCounit T φ C =
      (adicDatumExtensionCounit T φ).app Cₕ := by
    change (adicDatumExtension T φ).map (𝟙 _) ≫ _ ≫
      (adicDatumQh T S).map (𝟙 _) ≫ 𝟙 _ = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    rfl
  have hU : (adicDatumRestrictionComparison T φ).hom.app
      (((reductionChange T φ).mapHomotopyCategory (.up ℤ)).obj Cₕ) =
      U.mapDerivedCategoryFactors.hom.app E := by
    change U.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj E) = _
    exact exactFactorsh_app_eq U E
  have h' := congrArg (fun v ↦ v ≫ (adicDatumRestrictionComparison T φ).hom.app
    (((reductionChange T φ).mapHomotopyCategory (.up ℤ)).obj Cₕ)) h
  simp only [Category.assoc] at h'
  erw [Iso.inv_hom_id_app, Category.comp_id] at h'
  rw [hU] at h'
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient, quotient_map_eq_Qmap] at h'
  rw [hε]
  exact h'

attribute [local irreducible] adicDatumAdjunction

private def nativeQuotientUnit
    (C : CochainComplex (adicDatumModules T d) ℤ) (n : ℕ) :
    C ⟶ ((adicDatumTowerFunctor T d).obj C).asFunctor.obj (op n) where
  f q := (adicDatumOrdinaryAdjunction T (adicDatumProjection T d n)).unit.app (C.X q)
  comm' q k _ := ((adicDatumOrdinaryAdjunction T
    (adicDatumProjection T d n)).unit.naturality (C.d q k)).symm

private theorem nativeModelUnit {K : adicDatumDerived T d} (M : AdicDatumModel T d K)
    (n : ℕ) :
    M.realization.inv ≫ DerivedCategory.Q.map (nativeQuotientUnit T d M.complex n) ≫
        (adicDatumModelRestriction T d M n).hom ≫
        (adicDatumRestriction T (adicDatumProjection T d n)).map
          (adicDatumModelReductionIso T d M n).inv =
      (adicDatumAdjunction T (adicDatumProjection T d n)).unit.app K := by
  let φ := adicDatumProjection T d n
  let U := SheafOfModules.restrictScalars ((adicLisseForget T).map φ)
  let E := ((reductionChange T φ).mapHomologicalComplex (.up ℤ)).obj M.complex
  apply (cancel_mono ((adicDatumRestriction T φ).map
    (adicDatumModelReductionIso T d M n).hom)).1
  simp only [φ, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  change M.realization.inv ≫ _ ≫ _ = (adicDatumAdjunction T φ).unit.app K ≫
    (adicDatumRestriction T φ).map (adicDatumModelReductionComparison T d M n)
  dsimp only [adicDatumModelReductionComparison]
  rw [Functor.map_comp]
  have hn := (adicDatumAdjunction T φ).unit.naturality M.realization.inv
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  dsimp only [adicDatumReduction]
  erw [← reassoc_of% hn]
  apply (cancel_epi M.realization.inv).2
  apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app E)).1
  dsimp only [adicDatumModelRestriction, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  simp only [Category.assoc]
  erw [nativeDerivedUnit]
  dsimp only [U, E, φ]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  erw [← DerivedCategory.Q.map_comp]
  apply congrArg DerivedCategory.Q.map
  apply HomologicalComplex.hom_ext
  intro q
  change (nativeQuotientUnit T d M.complex n).f q ≫
    (adicDatumModelComplexRestrictionIso T d M n).hom.f q = _
  have hq : (adicDatumModelComplexRestrictionIso T d M n).hom.f q = 𝟙 _ :=
    (adicDatumModelComplexRestrictionIso_exists T d M n).exists.choose_spec q
  erw [hq]
  exact Category.comp_id _

section Presentation
variable (D : AdicCoefficientDatum A)

private theorem nativeRoundTrip_back
    (C : CochainComplex (adicDatumModules T (intrinsicPresentationDatum D)) ℤ) :
    ((intrinsicPresentationModulesBack T D).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (nativeRoundTrip T D) (.up ℤ)).hom.app C) =
      (NatIso.mapHomologicalComplex (intrinsicPresentationRoundTrip T D) (.up ℤ)).hom.app
        (((intrinsicPresentationModulesBack T D).mapHomologicalComplex (.up ℤ)).obj C) := by
  ext q U x
  change _ = ((intrinsicPresentationRoundTrip T D).hom.app _).val.app U x
  erw [(intrinsicPresentationRoundTrip_exists T D).exists.choose_spec]
  dsimp only [nativeRoundTrip, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app]
  change ((pbcRestrictComp (pbcCompletedComparison T D).hom
    (pbcCompletedComparison T D).inv (𝟙 _)
      (pbcCompletedComparison T D).hom_inv_id).inv.app _).val.app U
        ((reconstructionRestrictId T _).inv.app _ |>.val.app U x) = x
  let e := pbcRestrictComp (pbcCompletedComparison T D).hom
    (pbcCompletedComparison T D).inv (𝟙 _) (pbcCompletedComparison T D).hom_inv_id
  change (e.inv.app (C.X q)).val.app U x = x
  have h := reconstructionComp_section T (pbcCompletedComparison T D).hom
    (pbcCompletedComparison T D).inv (𝟙 _) (pbcCompletedComparison T D).hom_inv_id
    (C.X q) U ((e.inv.app (C.X q)).val.app U x)
  have hi := congrArg (fun g ↦ g.val.app U x) (e.inv_hom_id_app (C.X q))
  exact h.symm.trans hi

attribute [local irreducible] pbcCompletedComparison intrinsicPresentationRoundTrip
  nativeRoundTrip reconstructionRestrictId

private theorem pointedComparison
    {C : Type*} [Category C] (F : C ⥤ C) (η : 𝟭 C ⟶ F)
    {X Y Z W : C} (k : X ≅ Y) (e₀ : F.obj X ≅ Z) (e₁ : F.obj Y ≅ W)
    (u : X ⟶ Z) (v : Y ⟶ W)
    (h₀ : η.app X ≫ e₀.hom = u) (h₁ : η.app Y ≫ e₁.hom = v) :
    u ≫ (e₀.symm ≪≫ F.mapIso k ≪≫ e₁).hom = k.hom ≫ v := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← h₀, Category.assoc, Iso.hom_inv_id_assoc]
  have hn := η.naturality k.hom
  dsimp only [Functor.id_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc, h₁]

private theorem nativeFiberComparison
    (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules T (intrinsicPresentationDatum D)) ℤ) :
    let B := intrinsicPresentationModulesBack T D
    let BC := B.mapHomologicalComplex (.up ℤ)
    let C' := BC.obj C
    ∃ e : B.mapDerivedCategory.obj
        (completedIntrinsicCompletion T (intrinsicPresentationDatum D) r f C) ≅
          DerivedCategory.Q.obj (intrinsicCompletionComplex T D r f C'),
      B.mapDerivedCategory.map
          (DerivedCategory.Q.map
            (completedKoszulUnitComplex T (intrinsicPresentationDatum D) r f C)) ≫ e.hom =
        B.mapDerivedCategoryFactors.hom.app C ≫
          DerivedCategory.Q.map (intrinsicCompletionComplexUnit T D r f C') := by
  dsimp only
  let B := intrinsicPresentationModulesBack T D
  let BC := B.mapHomologicalComplex (.up ℤ)
  let C' := (intrinsicPresentationComplex T D).obj (BC.obj C)
  let j : C ≅ C' :=
    (NatIso.mapHomologicalComplex (nativeRoundTrip T D) (.up ℤ)).app C
  let k := DerivedCategory.Q.mapIso j
  obtain ⟨F, η, hF⟩ := completedIntrinsicCompletion_descends T
    (intrinsicPresentationDatum D) r f
  obtain ⟨e₀, he₀⟩ := hF C
  obtain ⟨e₁, he₁⟩ := hF C'
  let i : completedIntrinsicCompletion T (intrinsicPresentationDatum D) r f C ≅
      completedIntrinsicCompletion T (intrinsicPresentationDatum D) r f C' :=
    e₀.symm ≪≫ F.mapIso k ≪≫ e₁
  have hi : DerivedCategory.Q.map
        (completedKoszulUnitComplex T (intrinsicPresentationDatum D) r f C) ≫ i.hom =
      k.hom ≫ DerivedCategory.Q.map
        (completedKoszulUnitComplex T (intrinsicPresentationDatum D) r f C') := by
    exact pointedComparison F η k e₀ e₁ _ _ he₀ he₁
  let e := B.mapDerivedCategory.mapIso i ≪≫
    B.mapDerivedCategoryFactors.app (completedKoszulFiber T
      (intrinsicPresentationDatum D) r f C')
  refine ⟨e, ?_⟩
  change B.mapDerivedCategory.map _ ≫ B.mapDerivedCategory.map i.hom ≫ _ = _
  rw [← B.mapDerivedCategory.map_comp_assoc, hi, B.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  erw [B.mapDerivedCategoryFactors.hom.naturality]
  simp only [Functor.comp_map]
  erw [B.mapDerivedCategoryFactors.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  apply congrArg DerivedCategory.Q.map
  change BC.map j.hom ≫ BC.map _ = intrinsicCompletionComplexUnit T D r f (BC.obj C)
  erw [nativeRoundTrip_back]
  rfl

private def nativeRingEquivalence
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (β : R ≅ S) :
    pbcModules T R ≌ pbcModules T S :=
  CategoryTheory.Equivalence.mk (pbcRestrict β.inv) (pbcRestrict β.hom)
    ((pbcRestrictComp β.hom β.inv (𝟙 _) β.hom_inv_id ≪≫
      reconstructionRestrictId T R).symm)
    (pbcRestrictComp β.inv β.hom (𝟙 _) β.inv_hom_id ≪≫
      reconstructionRestrictId T S)

private theorem nativeProjectionComparison (n : ℕ) :
    (pbcCompletedComparison T D).hom ≫ pbcAdicProjection T D n =
      adicDatumProjection T (intrinsicPresentationDatum D) n ≫
        (pbcLevelConstantComparison T D n).hom := by
  have h := HasLimit.isoOfNatIso_hom_π (pbcConstantSystemComparison T D) (op n)
  delta pbcCompletedComparison
  dsimp only [pbcAdicProjection, adicDatumProjection,
    pbcConstantSystemComparison, intrinsicPresentationDatum, adicLisseCompletedRing,
    pbcAdicRings, NatIso.ofComponents_hom_app] at h ⊢
  exact h

private def nativeRestrictionSquare (n : ℕ) :
    (nativeRingEquivalence T (pbcLevelConstantComparison T D n)).inverse ⋙
        (SheafOfModules.restrictScalars
          ((adicLisseForget T).map (adicDatumProjection T (intrinsicPresentationDatum D) n))) ≅
      pbcRestrict (pbcAdicProjection T D n) ⋙
        (nativeRingEquivalence T (pbcCompletedComparison T D)).inverse :=
  pbcRestrictComp (adicDatumProjection T (intrinsicPresentationDatum D) n)
    (pbcLevelConstantComparison T D n).hom _ rfl ≪≫
      (pbcRestrictComp (pbcCompletedComparison T D).hom (pbcAdicProjection T D n)
        _ (nativeProjectionComparison T D n)).symm

private def nativeReductionComparison (n : ℕ) :
    adicDatumOrdinaryReduction T (intrinsicPresentationDatum D) n ⋙
        intrinsicPresentationModulesBack T D ≅
      intrinsicPresentationModulesBack T D ⋙ completedReductionLevel T D n :=
  reductionTransport (nativeRingEquivalence T (pbcCompletedComparison T D))
    (nativeRingEquivalence T (pbcLevelConstantComparison T D n))
    (reductionChange T (adicDatumProjection T (intrinsicPresentationDatum D) n)) _
    (pbcExtend (pbcAdicProjection T D n)) _
    (adicDatumOrdinaryAdjunction T (adicDatumProjection T (intrinsicPresentationDatum D) n))
    (pbcScalarAdjunction (pbcAdicProjection T D n))
    (nativeRestrictionSquare T D n)

private theorem nativeReductionComparison_unit (n : ℕ)
    (N : adicDatumModules T (intrinsicPresentationDatum D)) :
    (intrinsicPresentationModulesBack T D).map
        ((adicDatumOrdinaryAdjunction T
          (adicDatumProjection T (intrinsicPresentationDatum D) n)).unit.app N) ≫
        (nativeReductionComparison T D n).hom.app N =
      (pbcScalarAdjunction (pbcAdicProjection T D n)).unit.app
        ((intrinsicPresentationModulesBack T D).obj N) :=
  reductionTransport_unit (nativeRingEquivalence T (pbcCompletedComparison T D))
    (nativeRingEquivalence T (pbcLevelConstantComparison T D n))
    (reductionChange T (adicDatumProjection T (intrinsicPresentationDatum D) n)) _
    (pbcExtend (pbcAdicProjection T D n)) _
    (adicDatumOrdinaryAdjunction T (adicDatumProjection T (intrinsicPresentationDatum D) n))
    (pbcScalarAdjunction (pbcAdicProjection T D n)) (nativeRestrictionSquare T D n) N

attribute [local irreducible] nativeReductionComparison nativeRestrictionSquare
  comparisonChangeAdjunction

private theorem nativeOrdinaryUnit_formula (n : ℕ)
    (N : adicDatumModules T (intrinsicPresentationDatum D)) (U : T.ProEtᵒᵖ)
    (x : N.val.obj U) :
    ((adicDatumOrdinaryAdjunction T
      (adicDatumProjection T (intrinsicPresentationDatum D) n)).unit.app N).val.app U x =
      adicDatumTensorSection T
        (adicDatumProjection T (intrinsicPresentationDatum D) n) N U 1 x := by
  have h := congrArg (fun v ↦ v.val.app U x)
    ((adicDatumOrdinaryAdjunction_exists T
      (adicDatumProjection T (intrinsicPresentationDatum D) n)).choose_spec N)
  exact h.trans ((adicDatumOrdinaryUnit_exists T _ N).exists.choose_spec U x)

attribute [local irreducible] adicDatumOrdinaryAdjunction pbcScalarAdjunction

private theorem nativeOrdinaryUnit_epi (n : ℕ)
    (N : adicDatumModules T (intrinsicPresentationDatum D)) :
    Epi ((adicDatumOrdinaryAdjunction T
      (adicDatumProjection T (intrinsicPresentationDatum D) n)).unit.app N) := by
  let B := intrinsicPresentationModulesBack T D
  have : B.IsEquivalence := by
    exact (reconstructionPresentationBackEquiv T D).isEquivalence_functor
  have hp : Epi ((pbcScalarAdjunction (pbcAdicProjection T D n)).unit.app (B.obj N)) := by
    have he : (pbcScalarAdjunction (pbcAdicProjection T D n)).unit.app (B.obj N) =
        (comparisonChangeAdjunction T (pbcAdicProjection T D n)).unit.app (B.obj N) := by
      ext U x
      change _ = ((comparisonChangeAdjunction T _).unit.app (B.obj N)).val.app U x
      exact (reconstructionUnit_section T (pbcAdicProjection T D n) (B.obj N) U x).trans
        (comparisonChangeUnit_apply T (pbcAdicProjection T D n) (B.obj N) U x).symm
    rw [he]
    exact comparisonChangeUnit_epi T _ (completedProjection_surjective T D n) _
  have h := nativeReductionComparison_unit T D n N
  let u := (adicDatumOrdinaryAdjunction T
    (adicDatumProjection T (intrinsicPresentationDatum D) n)).unit.app N
  let e := (nativeReductionComparison T D n).app N
  have : Epi (B.map u ≫ e.hom) := by
    change Epi (_ ≫ (nativeReductionComparison T D n).hom.app N)
    erw [h]
    exact hp
  have he : Epi ((B.map u ≫ e.hom) ≫ e.inv) := inferInstance
  have : Epi (B.map u) := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he
  exact B.epi_of_epi_map inferInstance

private theorem nativeReductionComparison_step
    (N : adicDatumModules T (intrinsicPresentationDatum D)) (n : ℕ) :
    (intrinsicPresentationModulesBack T D).map
        ((adicDatumOrdinaryTransition T (intrinsicPresentationDatum D)
          (op (n + 1)) (op n) (homOfLE (Nat.le_succ n)).op).app N) ≫
        (nativeReductionComparison T D n).hom.app N =
      (nativeReductionComparison T D (n + 1)).hom.app N ≫
        (completedReductionTransition T D (n + 1) n (Nat.le_succ n)).app
          ((intrinsicPresentationModulesBack T D).obj N) := by
  let B := intrinsicPresentationModulesBack T D
  let u (n : ℕ) := (adicDatumOrdinaryAdjunction T
    (adicDatumProjection T (intrinsicPresentationDatum D) n)).unit.app N
  have hu : u (n + 1) ≫ (adicDatumOrdinaryTransition T (intrinsicPresentationDatum D)
      (op (n + 1)) (op n) (homOfLE (Nat.le_succ n)).op).app N = u n := by
    ext U x
    change ((adicDatumOrdinaryTransition T (intrinsicPresentationDatum D)
      (op (n + 1)) (op n) (homOfLE (Nat.le_succ n)).op).app N).val.app U
        ((u (n + 1)).val.app U x) = (u n).val.app U x
    dsimp only [u]
    erw [nativeOrdinaryUnit_formula, nativeOrdinaryUnit_formula]
    exact ((adicDatumOrdinaryTransition_exists T (intrinsicPresentationDatum D)
      (op (n + 1)) (op n) (homOfLE (Nat.le_succ n)).op).exists.choose_spec N U 1 x).trans
        (by rw [map_one])
  have := nativeOrdinaryUnit_epi T D (n + 1) N
  have : B.IsEquivalence := by
    exact (reconstructionPresentationBackEquiv T D).isEquivalence_functor
  apply (cancel_epi (B.map (u (n + 1)))).1
  rw [← B.map_comp_assoc, hu, nativeReductionComparison_unit]
  rw [← Category.assoc, nativeReductionComparison_unit]
  ext U x
  change ((pbcScalarAdjunction (pbcAdicProjection T D n)).unit.app (B.obj N)).val.app U x =
    ((completedReductionTransition T D (n + 1) n (Nat.le_succ n)).app (B.obj N)).val.app U
      (((pbcScalarAdjunction (pbcAdicProjection T D (n + 1))).unit.app (B.obj N)).val.app U x)
  erw [reconstructionUnit_section, reconstructionUnit_section]
  exact ((completedReductionTransition_exists T D (n + 1) n
    (Nat.le_succ n)).exists.choose_spec (B.obj N) U 1 x).trans
      (by rw [map_one]; rfl) |>.symm

private theorem nativeKFlat_of_iso
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {P Q : CochainComplex (pbcModules T R) ℤ} (e : P ≅ Q)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := R) P) :
    CochainComplex.IsAcyclicTensorKFlat (R := R) Q := by
  let := SheafOfModules.monoidalCategory R
  intro Z hZ n
  let F := (MonoidalCategory.curriedTensor (pbcModules T R)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let e' : CochainComplex.mapBifunctor Z P (MonoidalCategory.curriedTensor _) ≅
      CochainComplex.mapBifunctor Z Q (MonoidalCategory.curriedTensor _) :=
    HomologicalComplex₂.total.mapIso ((F.obj Z).mapIso e) (ComplexShape.up ℤ)
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (hP Z hZ n)).of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso e').symm |>
      (HomologicalComplex.exactAt_iff_isZero_homology _ n).2

private theorem nativeBack_kflat
    (C : CochainComplex (adicDatumModules T (intrinsicPresentationDatum D)) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat
      (R := adicDatumRing T (intrinsicPresentationDatum D)) C) :
    CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion T D)
      (((intrinsicPresentationModulesBack T D).mapHomologicalComplex (.up ℤ)).obj C) := by
  let β := pbcCompletedComparison T D
  let e : reductionChange T β.hom ≅ intrinsicPresentationModulesBack T D :=
    (pbcScalarAdjunction β.hom).leftAdjointUniq (nativeRingEquivalence T β).toAdjunction
  apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2
  apply nativeKFlat_of_iso T ((NatIso.mapHomologicalComplex e (.up ℤ)).app C)
  exact adicDatumExtension_kflat T β.hom C hC

private def nativeStrictLevel
    (C : CochainComplex (adicDatumModules T (intrinsicPresentationDatum D)) ℤ) (n : ℕ) :
    ((intrinsicPresentationModulesBack T D).mapHomologicalComplex (.up ℤ)).obj
        (((adicDatumTowerFunctor T (intrinsicPresentationDatum D)).obj C).asFunctor.obj
          (op n)) ≅
      ((completedReductionComplexTowerFunctor T D).obj
        (((intrinsicPresentationModulesBack T D).mapHomologicalComplex (.up ℤ)).obj C)
          ).asFunctor.obj (op n) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (nativeReductionComparison T D n).app (C.X q)) ?_
  intro q k hqk
  exact ((nativeReductionComparison T D n).hom.naturality (C.d q k)).symm

private theorem nativeStrictLevel_step
    (C : CochainComplex (adicDatumModules T (intrinsicPresentationDatum D)) ℤ) (n : ℕ) :
    ((intrinsicPresentationModulesBack T D).mapHomologicalComplex (.up ℤ)).map
        (((adicDatumTowerFunctor T (intrinsicPresentationDatum D)).obj C).asFunctor.map
          (homOfLE (Nat.le_succ n)).op) ≫ (nativeStrictLevel T D C n).hom =
      (nativeStrictLevel T D C (n + 1)).hom ≫
        ((completedReductionComplexTowerFunctor T D).obj
          (((intrinsicPresentationModulesBack T D).mapHomologicalComplex (.up ℤ)).obj C)
            ).asFunctor.map (homOfLE (Nat.le_succ n)).op := by
  apply HomologicalComplex.hom_ext
  intro q
  change (intrinsicPresentationModulesBack T D).map
      ((adicDatumOrdinaryTransition T (intrinsicPresentationDatum D)
        (op (n + 1)) (op n) (homOfLE (Nat.le_succ n)).op).app (C.X q)) ≫
      (nativeReductionComparison T D n).hom.app (C.X q) =
    (nativeReductionComparison T D (n + 1)).hom.app (C.X q) ≫
      (completedReductionModuleTower T D
        ((intrinsicPresentationModulesBack T D).obj (C.X q))).map
          (homOfLE (Nat.le_succ n)).op
  dsimp only [completedReductionModuleTower]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  exact nativeReductionComparison_step T D (C.X q) n

private theorem nativeStrictLevel_unit
    (C : CochainComplex (adicDatumModules T (intrinsicPresentationDatum D)) ℤ) (n : ℕ) :
    ((intrinsicPresentationModulesBack T D).mapHomologicalComplex (.up ℤ)).map
        (nativeQuotientUnit T (intrinsicPresentationDatum D) C n) ≫
        (nativeStrictLevel T D C n).hom =
      ((NatTrans.mapHomologicalComplex
        (pbcScalarAdjunction (pbcAdicProjection T D n)).unit (.up ℤ)).app
          (((intrinsicPresentationModulesBack T D).mapHomologicalComplex (.up ℤ)).obj C)) := by
  apply HomologicalComplex.hom_ext
  intro q
  exact nativeReductionComparison_unit T D n (C.X q)

private theorem actualStrictStep
    (J : CochainComplex (reductionTowerCategory T
      (reductionModuleRing T (completedReductionCoefficient T D))) ℤ) (n : ℕ) :
    (reductionTowerEvaluation T (reductionModuleRing T (completedReductionCoefficient T D))
      (n + 1)).mapDerivedCategoryFactors.inv.app J ≫
        completedTowerDerivedStep T D (DerivedCategory.Q.obj J) n =
      DerivedCategory.Q.map (J.asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫
        (reductionTowerEvaluation T (reductionModuleRing T (completedReductionCoefficient T D))
          n).mapDerivedCategoryFactors.inv.app J := by
  change _ ≫ (Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ _ _
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      (completedTowerEvaluationStep T (reductionModuleRing T (completedReductionCoefficient T D)) n)
        (.up ℤ)) DerivedCategory.Q)).app (DerivedCategory.Q.obj J) = _
  erw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Functor.whiskerRight_app,
    Iso.inv_hom_id_app_assoc]
  rfl

attribute [local irreducible] nativeStrictLevel productTransport nativeQuotientUnit

private theorem nativeFiberRoos
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = D.ideal)
    (C : CochainComplex (adicDatumModules T (intrinsicPresentationDatum D)) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat
      (R := adicDatumRing T (intrinsicPresentationDatum D)) C) :
    let J := (adicDatumTowerFunctor T (intrinsicPresentationDatum D)).obj C
    let V := fun n : ℕ ↦ DerivedCategory.Q.obj (J.asFunctor.obj (op n))
    ∃ (p : completedIntrinsicCompletion T (intrinsicPresentationDatum D) r f C ⟶ ∏ᶜ V)
      (δ : (∏ᶜ V) ⟶
        (completedIntrinsicCompletion T (intrinsicPresentationDatum D) r f C)⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle
        (fun n ↦ DerivedCategory.Q.map (J.asFunctor.map (homOfLE (Nat.le_succ n)).op))
        (completedIntrinsicCompletion T (intrinsicPresentationDatum D) r f C) p δ ∧
      ∀ n, DerivedCategory.Q.map
          (completedKoszulUnitComplex T (intrinsicPresentationDatum D) r f C) ≫
          p ≫ Pi.π V n =
        DerivedCategory.Q.map (nativeQuotientUnit T (intrinsicPresentationDatum D) C n) := by
  dsimp only
  let B := intrinsicPresentationModulesBack T D
  have : B.IsEquivalence := (reconstructionPresentationBackEquiv T D).isEquivalence_functor
  let F := B.mapDerivedCategory
  have : F.IsEquivalence := inferInstance
  let : HasProductsOfShape ℕ (DerivedCategory (pbcModules T (pbcAdicCompletion T D))) :=
    Adjunction.hasLimitsOfShape_of_equivalence F.inv
  let BC := B.mapHomologicalComplex (.up ℤ)
  let C' := BC.obj C
  let J := (adicDatumTowerFunctor T (intrinsicPresentationDatum D)).obj C
  let J' := (completedReductionComplexTowerFunctor T D).obj C'
  let V := fun n : ℕ ↦ DerivedCategory.Q.obj (J.asFunctor.obj (op n))
  let W := completedTowerDerivedSequence T D (DerivedCategory.Q.obj J')
  let a (n : ℕ) : F.obj (V n) ≅ W n :=
    B.mapDerivedCategoryFactors.app (J.asFunctor.obj (op n)) ≪≫
      DerivedCategory.Q.mapIso (nativeStrictLevel T D C n) ≪≫
      ((reductionTowerEvaluation T (reductionModuleRing T (pbcAdicCompletion T D)) n
        ).mapDerivedCategoryFactors.app J').symm
  have ha (n : ℕ) :
      F.map (DerivedCategory.Q.map (J.asFunctor.map (homOfLE (Nat.le_succ n)).op)) ≫
          (a n).hom =
        (a (n + 1)).hom ≫ completedTowerDerivedStep T D (DerivedCategory.Q.obj J') n := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    erw [B.mapDerivedCategoryFactors.hom.naturality_assoc]
    simp only [Functor.comp_map]
    rw [← DerivedCategory.Q.map_comp_assoc, nativeStrictLevel_step,
      DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    erw [actualStrictStep T D J' n]
    rfl
  obtain ⟨e₀, he₀⟩ := nativeFiberComparison T D r f C
  obtain ⟨e₁, he₁⟩ := actualFiberToStrict T D r f hf C' (nativeBack_kflat T D C hC)
  let e := e₀ ≪≫ e₁
  let : HasProductsOfShape ℕ
      (reductionDerivedCategory T (completedReductionCoefficient T D)) := by
    change HasProductsOfShape ℕ (DerivedCategory (pbcModules T (pbcAdicCompletion T D)))
    infer_instance
  obtain ⟨δ', hδ'⟩ := completedRlim_roos T D (DerivedCategory.Q.obj J')
  apply reflectNormalizedRoos F a _ _ ha e
    (completedRlimRoosProjection T D (DerivedCategory.Q.obj J')) δ' hδ'
    (DerivedCategory.Q.map
      (completedKoszulUnitComplex T (intrinsicPresentationDatum D) r f C))
    (fun n ↦ DerivedCategory.Q.map
      (nativeQuotientUnit T (intrinsicPresentationDatum D) C n))
  intro n
  dsimp only [completedRlimRoosProjection]
  erw [Pi.lift_π]
  dsimp only [e, Iso.trans_hom]
  simp only [Category.assoc]
  erw [reassoc_of% he₀]
  erw [he₁ n]
  dsimp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  erw [B.mapDerivedCategoryFactors.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← DerivedCategory.Q.map_comp_assoc, nativeStrictLevel_unit]
  rfl

end Presentation

private theorem normalizeModelComposite
    {C : Type*} [Category C] {X Y Z P V W H : C}
    (α : X ⟶ Y) (u : Y ⟶ Z) (p : Z ⟶ P) (π : P ⟶ V)
    (q : Y ⟶ V) (v : V ⟶ W) (w : W ⟶ H) (h : u ≫ p ≫ π = q) :
    (α ≫ u) ≫ p ≫ π ≫ v ≫ w = α ≫ q ≫ v ≫ w := by
  simp only [Category.assoc]
  rw [reassoc_of% h]

/-- Explicit Koszul completion carries a quotient Roos triangle with normalized unit.
This assertion holds before imposing completeness on the input object.

Source: blueprint Koszul reconstruction, order 1248; Stacks Tags 091Z and 099M
(blueprint: lem-weil-pbc-completed-koszul-reduction-roos-triangle).
Proof: form D : AdicCoefficientDatum A with exactly d's inherited complete datum
and quotient-finiteness certificates; intrinsicPresentationDatum D is definitionally d.
Let B = intrinsicPresentationModulesBack T D and C = B.mapHomologicalComplex(M.complex).
The inverse of B.mapDerivedCategoryFactors at M.complex, followed by the image of
M.realization, realizes C as B.mapDerivedCategory(K). Apply
completedKoszulQuotientComparison to D, C and this realization. This supplies a
unit-normalized isomorphism from intrinsicCompletion to the derived strict quotient
limit. Its source comparison ultimately uses the Noetherian Koszul augmentations:
their cones are pro-zero, also after derived tensor by the K-flat representative,
and their derived inverse limit vanishes.

Apply G = intrinsicPresentationModules T D to the resulting derived comparison.
The completed coefficient ring comparison is an isomorphism, so G and B are exact
inverse equivalences. Their round trips are identity on underlying sections.
Use completedIntrinsicCompletion_descends and the round trip G(C) ≅ M.complex to
identify the transported Koszul fiber and its unit with the exact fiber in this
statement. The representative comparisons supplied by descent preserve the unit;
its naturality and the scalar-equivalence triangle identities give this equality
also for the round trip, rather than just an unnormalized object isomorphism.

At every quotient level, use the finite coefficient comparison induced by constants
and the universal K-flat scalar-extension comparisons to identify the transported
strict quotient tower with adicDatumModelTower T d M. The transition squares hold
because both maps send s tensor m to the quotient of s tensor m. The normalized
ordinary scalar comparisons determine these maps, so the level comparisons form an
isomorphism of the whole derived sequence. Apply completedRlim_roos to the source
strict derived tower. Exact inverse coefficient restrictions preserve products and
distinguished triangles. Transport its two product vertices through that sequence
isomorphism and its first vertex through the Koszul comparison to obtain p and δ.

The source completion unit is the derived constant-limit adjunction unit followed
by the strict quotient augmentation. Its nth evaluation is the ordinary quotient
unit, since every Koszul augmentation sends 1 to 1 and has zero homotopy component.
The normalization in adicDatumAdjunction_exists identifies this with the derived
scalar adjunction unit after the specified model restriction and reduction maps.
The equality from completedKoszulQuotientComparison and the unit-preserving descent
therefore give precisely the displayed equation for each n.
The empty list of generators, zero quotient, and empty scheme use the same normalized
maps and triangles; neither flatness of the quotient nor constancy of a reduced tower
is required. -/
theorem completedKoszulReductionRoosTriangle_legacy {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = d.ideal) :
    ∃ (p : completedIntrinsicCompletion T d r f M.complex ⟶
        ∏ᶜ (fun n : ℕ ↦ (adicDatumModelTower T d M).obj (op n)))
      (δ : (∏ᶜ (fun n : ℕ ↦ (adicDatumModelTower T d M).obj (op n))) ⟶
        (completedIntrinsicCompletion T d r f M.complex)⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ (adicDatumModelTower T d M).map
          (homOfLE (Nat.le_succ n)).op)
        (completedIntrinsicCompletion T d r f M.complex) p δ ∧
      ∀ n : ℕ,
        completedIntrinsicCompletionMap T d r f M.complex M.realization ≫
          p ≫ Pi.π (fun a : ℕ ↦ (adicDatumModelTower T d M).obj (op a)) n ≫
          (adicDatumModelRestriction T d M n).hom ≫
          (adicDatumRestriction T (adicDatumProjection T d n)).map
            (adicDatumModelReductionIso T d M n).inv =
          (adicDatumAdjunction T (adicDatumProjection T d n)).unit.app K := by
  let D : AdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  obtain ⟨p, δ, hδ, hp⟩ := nativeFiberRoos T D r f hf M.complex M.isKFlat
  refine ⟨p, δ, hδ, fun n ↦ ?_⟩
  exact (normalizeModelComposite M.realization.inv
    (DerivedCategory.Q.map (completedKoszulUnitComplex T d r f M.complex)) p
    (Pi.π (fun a : ℕ ↦ (adicDatumModelTower T d M).obj (op a)) n)
    (DerivedCategory.Q.map (nativeQuotientUnit T d M.complex n))
    (adicDatumModelRestriction T d M n).hom
    ((adicDatumRestriction T (adicDatumProjection T d n)).map
      (adicDatumModelReductionIso T d M n).inv) (hp n)).trans
        (nativeModelUnit T d M n)

end AlgebraicGeometry.Scheme
