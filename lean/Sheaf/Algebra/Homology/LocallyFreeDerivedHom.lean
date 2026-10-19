/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.CategoryTheory.Adjunction.Additive
import all Sheaf.AlgebraicGeometry.DualTensorHomComparison
import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Free
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Derived Hom from a locally finite free module on a ringed site

Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex, specialized to P[0]
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom).

The degree-zero formulation below is applied to every shifted bounded-below complex.
Thus H⁰ RΓ(P∨ ⊗ K[n]) is Hⁿ RΓ(P∨ ⊗ K), including negative n. The cycle normalization
specifies evaluation, rather than only asserting the existence of abstract group isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
universe u v w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory

/-- Evaluation associated to a monoidal pairing. Source: Stacks, Tag 08JJ
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom).
Factoring this formula through the ambient monoidal category keeps specialization to
sheaves from repeatedly expanding the localized associators and unitors. -/
noncomputable def locallyFreePairingEvaluate
    {A : Type*} [Category A] [MonoidalCategory A] {P D N : A}
    (ev : P ⊗ D ⟶ 𝟙_ A) (z : 𝟙_ A ⟶ D ⊗ N) : P ⟶ N :=
  (ρ_ P).inv ≫ P ◁ z ≫ (α_ P D N).inv ≫ ev ▷ N ≫ (λ_ N).hom

/-- The ordinary-to-derived zeroth-cohomology comparison for an additive functor.
Source: Stacks, Tags 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def locallyFreeDerivedComparison
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) 0 ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B 0 := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let q := HomotopyCategory.quotient A (.up ℤ)
  let a : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso B)).inv ≫
    Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) F.rightDerivedFunctor).hom
  exact (Functor.isoWhiskerLeft G (DerivedCategory.homologyFunctorFactors B 0)).inv ≫
    Functor.whiskerRight a (DerivedCategory.homologyFunctor B 0)

private theorem locallyFreeDerivedComparison_isIso
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) [K.IsKInjective] :
    IsIso ((locallyFreeDerivedComparison F).app K) := by
  dsimp [locallyFreeDerivedComparison]
  infer_instance

private noncomputable def pairingAddHom
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    (P D N : A) [(tensorLeft P).Additive] (ev : P ⊗ D ⟶ 𝟙_ A) :
    (𝟙_ A ⟶ D ⊗ N) →+ (P ⟶ N) where
  toFun := locallyFreePairingEvaluate ev
  map_zero' := by
    simp only [locallyFreePairingEvaluate,
      show P ◁ (0 : 𝟙_ A ⟶ D ⊗ N) = 0 from (tensorLeft P).map_zero _ _,
      comp_zero, zero_comp]
  map_add' := by
    intro a b
    simp only [locallyFreePairingEvaluate,
      show P ◁ (a + b) = P ◁ a + P ◁ b from (tensorLeft P).map_add,
      Preadditive.comp_add, Preadditive.add_comp]

private theorem pairing_eq_uncurry
    {A : Type*} [Category A] [MonoidalCategory A] [MonoidalClosed A]
    (P N : A) (z : 𝟙_ A ⟶ (ihom P).obj (𝟙_ A) ⊗ N) :
    locallyFreePairingEvaluate ((ihom.ev P).app (𝟙_ A)) z =
      (ρ_ P).inv ≫ MonoidalClosed.uncurry
        (z ≫ MonoidalClosed.ihomUnitTensorToIhom P N) := by
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.ihomUnitTensorToIhom,
    MonoidalClosed.uncurry_curry]
  rfl

private noncomputable def closedEvaluateAddEquiv
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A] [MonoidalClosed A]
    (P N : A) [(tensorLeft P).Additive]
    [IsIso (MonoidalClosed.ihomUnitTensorToIhom P N)] :
    (𝟙_ A ⟶ (ihom P).obj (𝟙_ A) ⊗ N) ≃+ (P ⟶ N) := by
  let e := (Iso.homCongr (Iso.refl (𝟙_ A))
    (asIso (MonoidalClosed.ihomUnitTensorToIhom P N))).trans
      MonoidalClosed.curryHomEquiv'.symm
  apply AddEquiv.ofBijective
    (pairingAddHom P ((ihom P).obj (𝟙_ A)) N ((ihom.ev P).app (𝟙_ A)))
  have h : (pairingAddHom P ((ihom P).obj (𝟙_ A)) N
      ((ihom.ev P).app (𝟙_ A)) : _ → _) = e := by
    funext z
    change locallyFreePairingEvaluate _ z = _
    rw [pairing_eq_uncurry]
    simp [e, Iso.homCongr, MonoidalClosed.uncurry']
  rw [h]
  exact e.bijective

private theorem transfer_finite_exact
    {A B : Type*} [Category A] [Category B] (F G : A ⥤ B) (e : F ≅ G)
    (hl : PreservesFiniteLimits G) (hc : PreservesFiniteColimits G) :
    PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  let := hl
  let := hc
  exact ⟨preservesFiniteLimits_of_natIso e.symm,
    preservesFiniteColimits_of_natIso e.symm⟩

private theorem left_and_right_exact
    {A B : Type*} [Category A] [Category B] (F G : A ⥤ B) (e : F ≅ G)
    (hl : PreservesLimits G) (hc : PreservesColimits F) :
    PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  let := hl
  let := hc
  exact ⟨preservesFiniteLimits_of_natIso e.symm, inferInstance⟩

private theorem additive_equiv_inverse_trans_apply
    {A B D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    (e : A ≃+ B) (e' : A ≃+ D) (a : A) : (e.symm.trans e') (e a) = e' a := by
  simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]

section AbstractModel

variable {A : Type v} [Category.{u} A] [Abelian A] [MonoidalCategory A]
  [MonoidalClosed A] [∀ P : A, (tensorLeft P).Additive]

private instance abstract_ihom_additive (P : A) : (ihom P).Additive :=
  (ihom.adjunction P).right_adjoint_additive

private def genericGood (P : A) : Prop :=
  (∀ N, IsIso (MonoidalClosed.ihomUnitTensorToIhom P N)) ∧
    PreservesFiniteLimits (tensorLeft P) ∧ PreservesFiniteColimits (tensorLeft P)

/-- The abstract categorical model of this construction, specialized to sheaves below.
Source: Stacks Project, Tags 08JJ, 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def genericDualTensor (P : A) : A ⥤ A :=
  tensorLeft ((ihom P).obj (𝟙_ A))

/-- Additivity of the abstract model functor.
Source: Mathlib additive tensor functors and preadditive coyoneda
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
instance genericDualTensor_additive (P : A) : (genericDualTensor P).Additive := by
  dsimp [genericDualTensor]
  infer_instance

/-- The abstract categorical model of this construction, specialized to sheaves below.
Source: Stacks Project, Tags 08JJ, 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def genericDualTensorMap (P P' M N : A) (p : P' ⟶ P) (f : M ⟶ N) :
    (genericDualTensor P).obj M ⟶ (genericDualTensor P').obj N :=
  tensorHom ((MonoidalClosed.pre p).app (𝟙_ A)) f

/-- The abstract categorical model of this construction, specialized to sheaves below.
Source: Stacks Project, Tags 08JJ, 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def genericSections : A ⥤ AddCommGrpCat.{u} :=
  preadditiveCoyoneda.obj (op (𝟙_ A))

/-- Additivity of the abstract model functor.
Source: Mathlib additive tensor functors and preadditive coyoneda
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
instance genericSections_additive : (genericSections (A := A)).Additive := by
  dsimp [genericSections]
  infer_instance

/-- The abstract categorical model of this construction, specialized to sheaves below.
Source: Stacks Project, Tags 08JJ, 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev genericTensorSections (P : A) :
    CochainComplex A ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (genericDualTensor P).mapHomologicalComplex (.up ℤ) ⋙
    genericSections.mapHomologicalComplex (.up ℤ)

/-- The abstract categorical model of this construction, specialized to sheaves below.
Source: Stacks Project, Tags 08JJ, 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def genericEvaluate (P N : A)
    (z : 𝟙_ A ⟶ (genericDualTensor P).obj N) : P ⟶ N :=
  locallyFreePairingEvaluate ((ihom.ev P).app (𝟙_ A)) z

private theorem abstract_closed_comparison_naturality
    {A : Type*} [Category A] [MonoidalCategory A] [MonoidalClosed A]
    (P P' N N' : A) (p : P' ⟶ P) (f : N ⟶ N') :
    ((MonoidalClosed.pre p).app (𝟙_ A) ⊗ₘ f) ≫
        MonoidalClosed.ihomUnitTensorToIhom P' N' =
      MonoidalClosed.ihomUnitTensorToIhom P N ≫ (ihom P).map f ≫
        (MonoidalClosed.pre p).app N' := by
  rw [← Category.assoc (MonoidalClosed.ihomUnitTensorToIhom P N)]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_natural_left]
  simp only [MonoidalClosed.ihomUnitTensorToIhom, MonoidalClosed.uncurry_curry,
    tensorHom_def, whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc,
    whisker_exchange_assoc, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, MonoidalClosed.id_tensor_pre_app_comp_ev]
  monoidal

private theorem abstract_closed_evaluation_naturality
    {A : Type*} [Category A] [MonoidalCategory A] [MonoidalClosed A]
    (P P' N N' : A) (p : P' ⟶ P) (f : N ⟶ N')
    (g : 𝟙_ A ⟶ (ihom P).obj N) :
    (ρ_ P').inv ≫ MonoidalClosed.uncurry
        (g ≫ (ihom P).map f ≫ (MonoidalClosed.pre p).app N') =
      p ≫ (ρ_ P).inv ≫ MonoidalClosed.uncurry g ≫ f := by
  rw [← Category.assoc g, MonoidalClosed.uncurry_pre_app,
    MonoidalClosed.uncurry_natural_right]
  rw [← rightUnitor_inv_naturality_assoc]

private noncomputable def abstract_dualTensorComparison
    (P N : A) :
    (genericDualTensor P).obj N ⟶ (ihom P).obj N := by
  exact MonoidalClosed.ihomUnitTensorToIhom P N

private theorem abstract_dualTensorComparison_isIso (P N : A)
    (hP : ∀ N, IsIso (MonoidalClosed.ihomUnitTensorToIhom P N)) :
    IsIso (abstract_dualTensorComparison P N) := hP N

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_dualTensorComparison_naturality
    (P P' N N' : A) (p : P' ⟶ P) (f : N ⟶ N') :
    genericDualTensorMap P P' N N' p f ≫ abstract_dualTensorComparison P' N' =
      abstract_dualTensorComparison P N ≫ (ihom P).map f ≫
        (MonoidalClosed.pre p).app N' := by
  exact abstract_closed_comparison_naturality P P' N N' p f

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_dualTensorMap_identity
    (P M N : A) (f : M ⟶ N) :
    genericDualTensorMap P P M N (𝟙 P) f = (genericDualTensor P).map f := by
  dsimp only [genericDualTensorMap]
  rw [MonoidalClosed.pre_id]
  exact MonoidalCategory.id_tensorHom _ f

set_option backward.isDefEq.respectTransparency false in
private noncomputable def abstract_dualTensorIso
    (P : A)
    (hP : ∀ N, IsIso (MonoidalClosed.ihomUnitTensorToIhom P N)) :
    genericDualTensor P ≅ ihom P :=
  NatIso.ofComponents (fun N ↦ by
    have := abstract_dualTensorComparison_isIso P N hP
    exact asIso (abstract_dualTensorComparison P N)) (by
      intro N N' f
      change (genericDualTensor P).map f ≫ abstract_dualTensorComparison P N' =
        abstract_dualTensorComparison P N ≫ (ihom P).map f
      have h := abstract_dualTensorComparison_naturality P P N N' (𝟙 P) f
      rw [abstract_dualTensorMap_identity] at h
      simpa only [MonoidalClosed.pre_id, NatTrans.id_app, Category.comp_id] using h)

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_dualTensor_exact
    (P : A)
    (hP : ∀ N, IsIso (MonoidalClosed.ihomUnitTensorToIhom P N)) :
    PreservesFiniteLimits (genericDualTensor P) ∧
      PreservesFiniteColimits (genericDualTensor P) := by
  exact left_and_right_exact (genericDualTensor P)
    (ihom P) (abstract_dualTensorIso P hP)
    (ihom.adjunction P).rightAdjoint_preservesLimits
    (ihom.adjunction ((ihom P).obj (𝟙_ A))).leftAdjoint_preservesColimits

private theorem abstract_tensorLeft_exact (P : A) (hP : genericGood P) :
    PreservesFiniteLimits (tensorLeft P) ∧ PreservesFiniteColimits (tensorLeft P) := hP.2

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_dualTensor_preservesKInjective
    (P : A)
    (hP : genericGood P) :
    (genericDualTensor P).PreservesKInjectiveComplexes := by
  let := (abstract_tensorLeft_exact P hP).1
  let := (abstract_tensorLeft_exact P hP).2
  have := (ihom.adjunction P).preservesKInjectiveComplexes
  exact Functor.preservesKInjectiveComplexes_of_iso
    (F := ihom P)
    (G := genericDualTensor P) (abstract_dualTensorIso P hP.1).symm

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_evaluate_eq_uncurry
    (P N : A)
    (z : 𝟙_ A ⟶ (genericDualTensor P).obj N) :
      genericEvaluate P N z = (ρ_ P).inv ≫
      MonoidalClosed.uncurry
        (z ≫ abstract_dualTensorComparison P N) := by
  exact pairing_eq_uncurry P N z

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_evaluate_naturality
    (P P' N N' : A) (p : P' ⟶ P) (f : N ⟶ N')
    (z : 𝟙_ A ⟶ (genericDualTensor P).obj N) :
    genericEvaluate P' N'
        (z ≫ genericDualTensorMap P P' N N' p f) =
      p ≫ genericEvaluate P N z ≫ f := by
  rw [abstract_evaluate_eq_uncurry, abstract_evaluate_eq_uncurry, Category.assoc,
    abstract_dualTensorComparison_naturality]
  simpa only [Category.assoc] using abstract_closed_evaluation_naturality P P' N N' p f
    (z ≫ abstract_dualTensorComparison P N)

private noncomputable def abstract_evaluateAddHom
    (P N : A) :
    (𝟙_ A ⟶ (genericDualTensor P).obj N) →+ (P ⟶ N) :=
  pairingAddHom P _ N ((ihom.ev P).app (𝟙_ _))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def abstract_evaluateAddEquiv
    (P N : A) (hP : genericGood P) :
    (𝟙_ A ⟶ (genericDualTensor P).obj N) ≃+ (P ⟶ N) := by
  have : IsIso (MonoidalClosed.ihomUnitTensorToIhom P N) :=
    abstract_dualTensorComparison_isIso P N hP.1
  exact closedEvaluateAddEquiv P N

set_option backward.isDefEq.respectTransparency false in
private noncomputable def abstract_evaluationComplexIso
    (P : A)
    (hP : genericGood P)
    (K : CochainComplex (A) ℤ) :
    (genericTensorSections P).obj K ≅
      (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K) := by
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (abstract_evaluateAddEquiv P (K.X n) hP).toAddCommGrpIso) (by
      intro i j hij
      ext z
      symm
      change genericEvaluate P (K.X j)
        (z ≫ (genericDualTensor P).map (K.d i j)) =
          genericEvaluate P (K.X i) z ≫ K.d i j
      have h := abstract_evaluate_naturality P P (K.X i) (K.X j) (𝟙 P) (K.d i j) z
      rw [abstract_dualTensorMap_identity, Category.id_comp] at h
      exact h)

private theorem abstract_evaluationComplexIso_hom_apply
    (P : A)
    (hP : genericGood P)
    (K : CochainComplex (A) ℤ)
    (i : ℤ) (z : 𝟙_ A ⟶ (genericDualTensor P).obj (K.X i)) :
    (abstract_evaluationComplexIso P hP K).hom.f i z =
      genericEvaluate P (K.X i) z := rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def abstract_singleHomComplexIso
    {A : Type*} [Category A] [Abelian A] (P : A) (K : CochainComplex A ℤ) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor A 0).obj P) K ≅
      (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (X := P) (K := K) (zero_add n)).toAddCommGrpIso) (by
        intro i j hij
        ext a
        obtain ⟨a, rfl⟩ :=
          CochainComplex.HomComplex.Cochain.fromSingleMk_surjective a i (zero_add i)
        change CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add i)
            (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add i)) ≫ K.d i j =
          CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add j)
            (CochainComplex.HomComplex.δ i j
              (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add i)))
        simp only [CochainComplex.HomComplex.Cochain.δ_fromSingleMk, zero_add,
          CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk])

private noncomputable def abstract_singleHomologyEquiv
    {A : Type*} [Category A] [Abelian A] (P : A) (K : CochainComplex A ℤ) :
    ((((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).homology 0) ≃+
      ((HomotopyCategory.quotient A (.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj P) ⟶
          (HomotopyCategory.quotient A (.up ℤ)).obj K) :=
  let e := HomologicalComplex.homologyMapIso (abstract_singleHomComplexIso P K).symm 0
  e.addCommGroupIsoToAddEquiv.trans
    ((CochainComplex.HomComplex.leftHomologyData _ K 0).homologyIso.addCommGroupIsoToAddEquiv.trans
      (CochainComplex.HomComplex.CohomologyClass.homAddEquiv.trans
        (Linear.homCongr ℤ (Iso.refl _)
          ((HomotopyCategory.quotient A (.up ℤ)).mapIso
            ((shiftFunctorZero _ ℤ).app K))).toAddEquiv))

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_singleHomologyEquiv_cycle
    {A : Type*} [Category A] [Abelian A] (P : A) (K : CochainComplex A ℤ)
    (z : (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).cycles 0)
    (f : (CochainComplex.singleFunctor A 0).obj P ⟶ K)
    (hf : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0 =
      ((((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).iCycles 0) z) :
    abstract_singleHomologyEquiv P K
      (HomologicalComplex.homologyπ
        (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K) 0 z) =
      (HomotopyCategory.quotient A (.up ℤ)).map f := by
  let S := (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K)
  let E := abstract_singleHomComplexIso P K
  let D := CochainComplex.HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor A 0).obj P) K 0
  let y := HomologicalComplex.cyclesMap E.inv 0 z
  have hy : D.cyclesIso.hom y = CochainComplex.HomComplex.Cocycle.ofHom f := by
    apply CochainComplex.HomComplex.Cocycle.ext
    apply (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add (0 : ℤ))).injective
    have h₁ : (D.cyclesIso.hom y).val =
        (((CochainComplex.singleFunctor A 0).obj P).HomComplex K).iCycles 0 y :=
      ConcreteCategory.congr_hom D.cyclesIso_hom_comp_i y
    have h₂ : (((CochainComplex.singleFunctor A 0).obj P).HomComplex K).iCycles 0 y =
        E.inv.f 0 (S.iCycles 0 z) :=
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i E.inv 0) z
    rw [h₁.trans h₂]
    change (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add (0 : ℤ)))
      ((CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add (0 : ℤ))).symm
        (S.iCycles 0 z)) = _
    rw [AddEquiv.apply_symm_apply]
    simpa [CochainComplex.HomComplex.Cochain.fromSingleEquiv] using hf.symm
  have hπ : HomologicalComplex.homologyMap E.inv 0 (S.homologyπ 0 z) =
      (((CochainComplex.singleFunctor A 0).obj P).HomComplex K).homologyπ 0 y :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality E.inv 0) z
  have hD : D.homologyIso.hom
      ((((CochainComplex.singleFunctor A 0).obj P).HomComplex K).homologyπ 0 y) =
      CochainComplex.HomComplex.CohomologyClass.mk (D.cyclesIso.hom y) :=
    ConcreteCategory.congr_hom D.homologyπ_comp_homologyIso_hom y
  unfold abstract_singleHomologyEquiv
  change (Linear.homCongr ℤ (Iso.refl _)
      ((HomotopyCategory.quotient A (.up ℤ)).mapIso
        ((shiftFunctorZero _ ℤ).app K))).toAddEquiv
    (CochainComplex.HomComplex.CohomologyClass.homAddEquiv
      (D.homologyIso.hom (HomologicalComplex.homologyMap E.inv 0 (S.homologyπ 0 z)))) = _
  rw [hπ, hD, hy]
  change (𝟙 _ ≫ (HomotopyCategory.quotient A (.up ℤ)).map
    (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (CochainComplex.HomComplex.Cocycle.ofHom f))) ≫
    (HomotopyCategory.quotient A (.up ℤ)).map
      ((shiftFunctorZero _ ℤ).hom.app K) = _
  rw [Category.id_comp, ← Functor.map_comp]
  congr 1
  ext i
  simp [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
    CochainComplex.HomComplex.Cocycle.homOf, CochainComplex.HomComplex.Cocycle.rightShift,
    CochainComplex.HomComplex.Cochain.rightShift_v, CochainComplex.shiftFunctorZero_hom_app_f]

private instance abstract_addCommGrpForgetSelf :
    HasForget₂ AddCommGrpCat.{u} AddCommGrpCat.{u} where
  forget₂ := 𝟭 _
  forget_comp := rfl

private instance abstract_addCommGrpForgetSelf_additive :
    (forget₂ AddCommGrpCat.{u} AddCommGrpCat.{u}).Additive :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u}).Additive

private instance abstract_addCommGrpForgetSelf_homology :
    (forget₂ AddCommGrpCat.{u} AddCommGrpCat.{u}).PreservesHomology :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u}).PreservesHomology

private noncomputable def abstract_singleMapCycle
    {A : Type*} [Category A] [Abelian A] (P : A) (K : CochainComplex A ℤ)
    (f : (CochainComplex.singleFunctor A 0).obj P ⟶ K) :
    (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).cycles 0 :=
  (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).cyclesMk (i := 0)
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0) 1 (by simp) (by
      change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0) ≫ K.d 0 1 = 0
      erw [Category.assoc, f.comm]
      simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
        HomologicalComplex.single_obj_d])

private theorem abstract_singleMapCycle_i
    {A : Type*} [Category A] [Abelian A] (P : A) (K : CochainComplex A ℤ)
    (f : (CochainComplex.singleFunctor A 0).obj P ⟶ K) :
    (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).iCycles 0
      (abstract_singleMapCycle P K f) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0 := by
  unfold abstract_singleMapCycle
  exact HomologicalComplex.i_cyclesMk
    (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K) _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_singleHomologyEquiv_naturality
    {A : Type*} [Category A] [Abelian A] (P P' : A) (K L : CochainComplex A ℤ)
    (p : P' ⟶ P) (f : K ⟶ L)
    (t : (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (((preadditiveCoyoneda.obj (op P')).mapHomologicalComplex (.up ℤ)).obj L))
    (ht : ∀ (i : ℤ) (a : P ⟶ K.X i), t.f i a = p ≫ a ≫ f.f i)
    (x : (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).homology 0) :
    abstract_singleHomologyEquiv P' L (HomologicalComplex.homologyMap t 0 x) =
      (HomotopyCategory.quotient A (.up ℤ)).map
        ((CochainComplex.singleFunctor A 0).map p) ≫
          abstract_singleHomologyEquiv P K x ≫ (HomotopyCategory.quotient A (.up ℤ)).map f := by
  let S := (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K)
  let S' := (((preadditiveCoyoneda.obj (op P')).mapHomologicalComplex (.up ℤ)).obj L)
  let q := HomotopyCategory.quotient A (.up ℤ)
  obtain ⟨g, hg⟩ := q.map_surjective (abstract_singleHomologyEquiv P K x)
  let z := abstract_singleMapCycle P K g
  have hz : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ g.f 0 =
      S.iCycles 0 z := (abstract_singleMapCycle_i P K g).symm
  have hx : x = S.homologyπ 0 z :=
    (abstract_singleHomologyEquiv P K).injective
      (hg.symm.trans (abstract_singleHomologyEquiv_cycle P K z g hz).symm)
  rw [hx]
  have hπ : HomologicalComplex.homologyMap t 0 (S.homologyπ 0 z) =
      S'.homologyπ 0 (HomologicalComplex.cyclesMap t 0 z) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality t 0) z
  rw [hπ, abstract_singleHomologyEquiv_cycle P K z g hz]
  rw [← q.map_comp, ← q.map_comp]
  apply abstract_singleHomologyEquiv_cycle
  have hi : S'.iCycles 0 (HomologicalComplex.cyclesMap t 0 z) = t.f 0 (S.iCycles 0 z) :=
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i t 0) z
  rw [hi, ht, ← hz]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [← Category.assoc (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P').inv]
  simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self, Category.assoc]

variable [HasDerivedCategory.{w} A] [IsGrothendieckAbelian.{u} A]

/-- The abstract categorical model of this construction, specialized to sheaves below.
Source: Stacks Project, Tags 08JJ, 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def genericHypercohomology : DerivedCategory A ⥤ AddCommGrpCat.{u} :=
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  (genericSections (A := A)).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0

/-- The abstract categorical model of this construction, specialized to sheaves below.
Source: Stacks Project, Tags 08JJ, 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def genericSectionsComparison (K : CochainComplex A ℤ) :
    (((genericSections (A := A)).mapHomologicalComplex (.up ℤ)).obj K).homology 0 ⟶
      (genericHypercohomology (A := A)).obj (DerivedCategory.Q.obj K) := by
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  exact (locallyFreeDerivedComparison (genericSections (A := A))).app K

private theorem abstract_sectionsComparison_isIso
    (K : CochainComplex (A) ℤ) [K.IsKInjective] :
    IsIso (genericSectionsComparison K) := by
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  exact locallyFreeDerivedComparison_isIso (genericSections (A := A)) K

private theorem abstract_sectionsComparison_naturality
    (K L : CochainComplex (A) ℤ) (f : K ⟶ L) :
    HomologicalComplex.homologyMap
        (((genericSections (A := A)).mapHomologicalComplex (.up ℤ)).map f) 0 ≫
      genericSectionsComparison L =
    genericSectionsComparison K ≫
      (genericHypercohomology (A := A)).map (DerivedCategory.Q.map f) := by
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  exact (locallyFreeDerivedComparison (genericSections (A := A))).naturality f

private noncomputable def abstract_dualTensorComplexMap
    (P P' : A)
    (K L : CochainComplex (A) ℤ) (p : P' ⟶ P) (f : K ⟶ L) :
    ((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((genericDualTensor P').mapHomologicalComplex (.up ℤ)).obj L where
  f i := genericDualTensorMap P P' (K.X i) (L.X i) p (f.f i)
  comm' i j hij := by
    symm
    change _ ◁ K.d i j ≫ genericDualTensorMap P P' _ _ p (f.f j) =
      genericDualTensorMap P P' _ _ p (f.f i) ≫ _ ◁ L.d i j
    simp only [genericDualTensorMap, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, f.comm]

omit [HasDerivedCategory.{w} (A)] in
private theorem abstract_dualTensorComplexMap_id_left
    (P : A)
    (K L : CochainComplex (A) ℤ) (f : K ⟶ L) :
    abstract_dualTensorComplexMap P P K L (𝟙 P) f =
      ((genericDualTensor P).mapHomologicalComplex (.up ℤ)).map f := by
  apply HomologicalComplex.hom_ext
  intro i
  exact abstract_dualTensorMap_identity P _ _ (f.f i)

private noncomputable def abstract_kInjectiveQuotientEquiv
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P K : CochainComplex A ℤ) [K.IsKInjective] :
    ((HomotopyCategory.quotient A (.up ℤ)).obj P ⟶
      (HomotopyCategory.quotient A (.up ℤ)).obj K) ≃+
      (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj K) :=
  (AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
    (CochainComplex.IsKInjective.Qh_map_bijective _ K)).trans
      (Linear.homCongr ℤ ((DerivedCategory.quotientCompQhIso A).app P)
        ((DerivedCategory.quotientCompQhIso A).app K)).toAddEquiv

private theorem abstract_kInjectiveQuotientEquiv_map
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P K : CochainComplex A ℤ) [K.IsKInjective] (f : P ⟶ K) :
    abstract_kInjectiveQuotientEquiv P K ((HomotopyCategory.quotient A (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  change (((DerivedCategory.quotientCompQhIso A).app P).inv ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map f)) ≫
      ((DerivedCategory.quotientCompQhIso A).app K).hom = _
  rw [Category.assoc]
  erw [(DerivedCategory.quotientCompQhIso A).hom.naturality f]
  simp

set_option synthInstance.maxHeartbeats 100000 in
-- Infer addition on the localized Hom group without exhausting the instance budget.
private noncomputable def abstract_kInjectiveEvaluationEquiv
    (P : A)
    (hP : genericGood P)
    (K : CochainComplex (A) ℤ) [K.IsKInjective] :
    ((genericTensorSections P).obj K).homology 0 ≃+
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj P) ⟶
        DerivedCategory.Q.obj K) :=
  (HomologicalComplex.homologyMapIso
    (abstract_evaluationComplexIso P hP K) 0).addCommGroupIsoToAddEquiv.trans
      ((abstract_singleHomologyEquiv P K).trans
        (abstract_kInjectiveQuotientEquiv ((CochainComplex.singleFunctor _ 0).obj P) K))

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_kInjectiveEvaluationEquiv_cycle
    (P : A)
    (hP : genericGood P)
    (K : CochainComplex (A) ℤ) [K.IsKInjective]
    (z : ((genericTensorSections P).obj K).cycles 0)
    (f : (CochainComplex.singleFunctor _ 0).obj P ⟶ K)
    (hf : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0 =
      genericEvaluate P (K.X 0)
        (((genericTensorSections P).obj K).iCycles 0 z)) :
    abstract_kInjectiveEvaluationEquiv P hP K
      (((genericTensorSections P).obj K).homologyπ 0 z) = DerivedCategory.Q.map f := by
  let E := abstract_evaluationComplexIso P hP K
  let S := (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K)
  let z' := HomologicalComplex.cyclesMap E.hom 0 z
  have hπ : HomologicalComplex.homologyMap E.hom 0
      (((genericTensorSections P).obj K).homologyπ 0 z) = S.homologyπ 0 z' :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality E.hom 0) z
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i E.hom 0) z
  change S.iCycles 0 z' = E.hom.f 0 _ at hi
  rw [abstract_evaluationComplexIso_hom_apply] at hi
  change abstract_kInjectiveQuotientEquiv _ K
    (abstract_singleHomologyEquiv P K (HomologicalComplex.homologyMap E.hom 0 _)) = _
  rw [hπ, abstract_singleHomologyEquiv_cycle P K z' f (hf.trans hi.symm),
    abstract_kInjectiveQuotientEquiv_map]

private noncomputable def abstract_kInjectiveDerivedEquiv
    (P : A)
    (hP : genericGood P)
    (K : CochainComplex (A) ℤ) [K.IsKInjective] :
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj P) ⟶ DerivedCategory.Q.obj K) ≃+
      (genericHypercohomology (A := A)).obj (DerivedCategory.Q.obj
        (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K)) := by
  have := abstract_dualTensor_preservesKInjective P hP
  have := abstract_sectionsComparison_isIso
    (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K)
  exact (abstract_kInjectiveEvaluationEquiv P hP K).symm.trans
    (asIso (genericSectionsComparison
      (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K))
      ).addCommGroupIsoToAddEquiv

set_option maxHeartbeats 800000 in
-- The cycle and naturality identities elaborate several derived Hom groups.
private theorem abstract_kInjectiveDerivedEquiv_cycle
    (P : A)
    (hP : genericGood P)
    (K : CochainComplex (A) ℤ) [K.IsKInjective]
    (z : ((genericTensorSections P).obj K).cycles 0)
    (f : (CochainComplex.singleFunctor _ 0).obj P ⟶ K)
    (hf : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0 =
      genericEvaluate P (K.X 0)
        (((genericTensorSections P).obj K).iCycles 0 z)) :
    abstract_kInjectiveDerivedEquiv P hP K (DerivedCategory.Q.map f) =
      genericSectionsComparison
        (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K)
        (((genericTensorSections P).obj K).homologyπ 0 z) := by
  have := abstract_dualTensor_preservesKInjective P hP
  have := abstract_sectionsComparison_isIso
    (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K)
  have h := abstract_kInjectiveEvaluationEquiv_cycle P hP K z f hf
  calc
    abstract_kInjectiveDerivedEquiv P hP K (DerivedCategory.Q.map f) =
        abstract_kInjectiveDerivedEquiv P hP K
          (abstract_kInjectiveEvaluationEquiv P hP K
            (((genericTensorSections P).obj K).homologyπ 0 z)) :=
      congrArg (abstract_kInjectiveDerivedEquiv P hP K) h.symm
    _ = _ := additive_equiv_inverse_trans_apply
      (abstract_kInjectiveEvaluationEquiv P hP K)
      (asIso (genericSectionsComparison
        (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K))
        ).addCommGroupIsoToAddEquiv _

private theorem abstract_kInjectiveQuotientEquiv_naturality
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P P' : CochainComplex A ℤ) (K L : CochainComplex A ℤ)
    [K.IsKInjective] [L.IsKInjective] (p : P' ⟶ P) (f : K ⟶ L)
    (a : (HomotopyCategory.quotient A (.up ℤ)).obj P ⟶
      (HomotopyCategory.quotient A (.up ℤ)).obj K) :
    abstract_kInjectiveQuotientEquiv P' L
      ((HomotopyCategory.quotient A (.up ℤ)).map p ≫ a ≫
        (HomotopyCategory.quotient A (.up ℤ)).map f) =
      DerivedCategory.Q.map p ≫ abstract_kInjectiveQuotientEquiv P K a ≫
        DerivedCategory.Q.map f := by
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective a
  rw [← Functor.map_comp, ← Functor.map_comp, abstract_kInjectiveQuotientEquiv_map,
    abstract_kInjectiveQuotientEquiv_map, Functor.map_comp, Functor.map_comp]

set_option maxHeartbeats 800000 in
-- The cycle and naturality identities elaborate several derived Hom groups.
set_option backward.isDefEq.respectTransparency false in
private theorem abstract_kInjectiveEvaluationEquiv_naturality
    (P P' : A)
    (hP : genericGood P) (hP' : genericGood P')
    (K L : CochainComplex (A) ℤ)
    [K.IsKInjective] [L.IsKInjective] (p : P' ⟶ P) (f : K ⟶ L)
    (t : ((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((genericDualTensor P').mapHomologicalComplex (.up ℤ)).obj L)
    (ht : ∀ i, t.f i = genericDualTensorMap P P' (K.X i) (L.X i) p (f.f i))
    (x : ((genericTensorSections P).obj K).homology 0) :
    abstract_kInjectiveEvaluationEquiv P' hP' L
      (HomologicalComplex.homologyMap
        (((genericSections (A := A)).mapHomologicalComplex (.up ℤ)).map t) 0 x) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map p) ≫
        abstract_kInjectiveEvaluationEquiv P hP K x ≫ DerivedCategory.Q.map f := by
  let E := abstract_evaluationComplexIso P hP K
  let E' := abstract_evaluationComplexIso P' hP' L
  let g := ((genericSections (A := A)).mapHomologicalComplex (.up ℤ)).map t
  let s := E.inv ≫ g ≫ E'.hom
  have hs (i : ℤ) (a : P ⟶ K.X i) : s.f i a = p ≫ a ≫ f.f i := by
    let z := E.inv.f i a
    have hc : E.inv.f i ≫ E.hom.f i = 𝟙 _ :=
      congrArg (fun h ↦ HomologicalComplex.Hom.f h i) E.inv_hom_id
    have hz := ConcreteCategory.congr_hom hc a
    change E.hom.f i z = a at hz
    rw [abstract_evaluationComplexIso_hom_apply] at hz
    change genericEvaluate P' (L.X i) (z ≫ t.f i) = _
    rw [ht, abstract_evaluate_naturality, hz]
  have he : g ≫ E'.hom = E.hom ≫ s := by simp [s]
  have hh := congrArg (fun h ↦ h x)
    (congrArg (fun h ↦ HomologicalComplex.homologyMap h 0) he)
  simp only [HomologicalComplex.homologyMap_comp, AddCommGrpCat.comp_apply] at hh
  change abstract_kInjectiveQuotientEquiv _ L (abstract_singleHomologyEquiv P' L
    (HomologicalComplex.homologyMap E'.hom 0
      (HomologicalComplex.homologyMap g 0 x))) = _
  calc
    _ = abstract_kInjectiveQuotientEquiv _ L (abstract_singleHomologyEquiv P' L
        (HomologicalComplex.homologyMap s 0 (HomologicalComplex.homologyMap E.hom 0 x))) :=
      congrArg (fun y ↦ abstract_kInjectiveQuotientEquiv _ L
        (abstract_singleHomologyEquiv P' L y)) hh
    _ = _ := by
      rw [abstract_singleHomologyEquiv_naturality P P' K L p f s hs,
        abstract_kInjectiveQuotientEquiv_naturality]
      rfl

private theorem abstract_kInjectiveDerivedEquiv_apply
    (P : A) (hP : genericGood P) (K : CochainComplex A ℤ) [K.IsKInjective]
    (a : DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj P) ⟶
      DerivedCategory.Q.obj K) :
    abstract_kInjectiveDerivedEquiv P hP K a =
      genericSectionsComparison
        (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K)
        ((abstract_kInjectiveEvaluationEquiv P hP K).symm a) := rfl

set_option maxHeartbeats 800000 in
-- The cycle and naturality identities elaborate several derived Hom groups.
set_option backward.isDefEq.respectTransparency false in
private theorem abstract_kInjectiveDerivedEquiv_naturality
    (P P' : A)
    (hP : genericGood P) (hP' : genericGood P')
    (K L : CochainComplex (A) ℤ)
    [K.IsKInjective] [L.IsKInjective] (p : P' ⟶ P) (f : K ⟶ L)
    (t : ((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((genericDualTensor P').mapHomologicalComplex (.up ℤ)).obj L)
    (ht : ∀ i, t.f i = genericDualTensorMap P P' (K.X i) (L.X i) p (f.f i))
    (a : DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj P) ⟶
      DerivedCategory.Q.obj K) :
    abstract_kInjectiveDerivedEquiv P' hP' L
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map p) ≫
        a ≫ DerivedCategory.Q.map f) =
      (genericHypercohomology (A := A)).map (DerivedCategory.Q.map t)
        (abstract_kInjectiveDerivedEquiv P hP K a) := by
  let x := (abstract_kInjectiveEvaluationEquiv P hP K).symm a
  have h := abstract_kInjectiveEvaluationEquiv_naturality P P' hP hP' K L p f t ht x
  have hx : abstract_kInjectiveEvaluationEquiv P hP K x = a := AddEquiv.apply_symm_apply _ _
  rw [hx] at h
  rw [abstract_kInjectiveDerivedEquiv_apply, abstract_kInjectiveDerivedEquiv_apply,
    ← h, AddEquiv.symm_apply_apply]
  exact ConcreteCategory.congr_hom (abstract_sectionsComparison_naturality _ _ t) x

private noncomputable def locallyFreeResolution :
    CochainComplex (A) ℤ ⥤
    CochainComplex (A) ℤ := by
  exact CochainComplex.kInjectiveResolutionFunctor.{u} A

private noncomputable def locallyFreeResolutionUnit :
    𝟭 (CochainComplex (A) ℤ) ⟶
        locallyFreeResolution := by
  exact CochainComplex.toKInjectiveResolution.{u} A

private instance abstract_resolution_isKInjective
    (K : CochainComplex (A) ℤ) :
    ((locallyFreeResolution).obj K).IsKInjective := by
  exact CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A K

private instance abstract_resolution_unit_quasiIso
    (K : CochainComplex (A) ℤ) :
    QuasiIso ((locallyFreeResolutionUnit).app K) := by
  exact (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A K).2

private noncomputable def abstract_resolutionTensorIso
    (P : A)
    (hP : genericGood P)
    (K : CochainComplex (A) ℤ) :
    DerivedCategory.Q.obj
      (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K) ≅
    DerivedCategory.Q.obj (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj
      ((locallyFreeResolution).obj K)) := by
  letI := (abstract_dualTensor_exact P hP.1).1
  letI := (abstract_dualTensor_exact P hP.1).2
  exact asIso (DerivedCategory.Q.map
    (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).map
      ((locallyFreeResolutionUnit).app K)))

private noncomputable def abstract_resolvedDerivedEquiv
    (P : A)
    (hP : genericGood P)
    (K : CochainComplex (A) ℤ) :
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj P) ⟶ DerivedCategory.Q.obj K) ≃+
      (genericHypercohomology (A := A)).obj (DerivedCategory.Q.obj
        (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K)) :=
  have : IsIso (DerivedCategory.Q.map ((locallyFreeResolutionUnit).app K)) :=
    inferInstance
  ((Linear.homCongr ℤ (Iso.refl _)
      (asIso (DerivedCategory.Q.map ((locallyFreeResolutionUnit).app K)))).toAddEquiv.trans
    (abstract_kInjectiveDerivedEquiv P hP ((locallyFreeResolution).obj K))).trans
      ((genericHypercohomology (A := A)).mapIso
        (abstract_resolutionTensorIso P hP K)).symm.addCommGroupIsoToAddEquiv

private theorem abstract_resolvedDerivedEquiv_spec
    (P : A)
    (hP : genericGood P)
    (K : CochainComplex (A) ℤ)
    (a : DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj P) ⟶
      DerivedCategory.Q.obj K) :
    (genericHypercohomology (A := A)).map
      (abstract_resolutionTensorIso P hP K).hom (abstract_resolvedDerivedEquiv P hP K a) =
    abstract_kInjectiveDerivedEquiv P hP ((locallyFreeResolution).obj K)
      (a ≫ DerivedCategory.Q.map ((locallyFreeResolutionUnit).app K)) := by
  change ((genericHypercohomology (A := A)).mapIso
    (abstract_resolutionTensorIso P hP K)).hom
      (((genericHypercohomology (A := A)).mapIso
        (abstract_resolutionTensorIso P hP K)).inv _) = _
  rw [Iso.inv_hom_id_apply]
  change abstract_kInjectiveDerivedEquiv P hP ((locallyFreeResolution).obj K)
    ((𝟙 _ ≫ a) ≫ (asIso (DerivedCategory.Q.map
      ((locallyFreeResolutionUnit).app K))).hom) = _
  rw [Category.id_comp, asIso_hom]

private theorem abstract_resolution_tensor_square
    (P P' : A)
    (K L : CochainComplex (A) ℤ)
    (p : P' ⟶ P) (f : K ⟶ L)
    (t : ((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((genericDualTensor P').mapHomologicalComplex (.up ℤ)).obj L)
    (ht : ∀ i, t.f i = genericDualTensorMap P P' (K.X i) (L.X i) p (f.f i)) :
    t ≫ ((genericDualTensor P').mapHomologicalComplex (.up ℤ)).map
        ((locallyFreeResolutionUnit).app L) =
      ((genericDualTensor P).mapHomologicalComplex (.up ℤ)).map
        ((locallyFreeResolutionUnit).app K) ≫
      abstract_dualTensorComplexMap P P' _ _ p ((locallyFreeResolution).map f) := by
  apply HomologicalComplex.hom_ext
  intro i
  have h := congrArg (fun g ↦ HomologicalComplex.Hom.f g i)
    ((locallyFreeResolutionUnit).naturality f)
  change t.f i ≫ _ ◁ _ = _ ◁ _ ≫ _
  rw [ht]
  dsimp only [abstract_dualTensorComplexMap, genericDualTensorMap]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  congr 1
  try exact h

set_option maxHeartbeats 800000 in
-- The cycle and naturality identities elaborate several derived Hom groups.
private theorem abstract_resolvedDerivedEquiv_naturality
    (P P' : A)
    (hP : genericGood P) (hP' : genericGood P') (p : P' ⟶ P)
    (K L : CochainComplex (A) ℤ) (f : K ⟶ L)
    (t : ((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((genericDualTensor P').mapHomologicalComplex (.up ℤ)).obj L)
    (ht : ∀ i, t.f i = genericDualTensorMap P P' (K.X i) (L.X i) p (f.f i))
    (a : DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj P) ⟶
      DerivedCategory.Q.obj K) :
    abstract_resolvedDerivedEquiv P' hP' L
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map p) ≫
        a ≫ DerivedCategory.Q.map f) =
      (genericHypercohomology (A := A)).map (DerivedCategory.Q.map t)
        (abstract_resolvedDerivedEquiv P hP K a) := by
  let H := genericHypercohomology (A := A)
  let I := locallyFreeResolution (A := A)
  let η := locallyFreeResolutionUnit (A := A)
  let ti := abstract_dualTensorComplexMap P P' (I.obj K) (I.obj L) p (I.map f)
  have hs := abstract_resolution_tensor_square P P' K L p f t ht
  have hd : DerivedCategory.Q.map t ≫ (abstract_resolutionTensorIso P' hP' L).hom =
      (abstract_resolutionTensorIso P hP K).hom ≫ DerivedCategory.Q.map ti := by
    simpa only [abstract_resolutionTensorIso, asIso_hom, ← Functor.map_comp] using
      congrArg DerivedCategory.Q.map hs
  apply ((H.mapIso (abstract_resolutionTensorIso P' hP' L)).addCommGroupIsoToAddEquiv).injective
  change H.map (abstract_resolutionTensorIso P' hP' L).hom _ =
    H.map (abstract_resolutionTensorIso P' hP' L).hom (H.map (DerivedCategory.Q.map t) _)
  rw [abstract_resolvedDerivedEquiv_spec]
  have hr : H.map (abstract_resolutionTensorIso P' hP' L).hom
        (H.map (DerivedCategory.Q.map t) (abstract_resolvedDerivedEquiv P hP K a)) =
      H.map (DerivedCategory.Q.map ti)
        (abstract_kInjectiveDerivedEquiv P hP (I.obj K) (a ≫ DerivedCategory.Q.map (η.app K))) := by
    rw [← ConcreteCategory.comp_apply, ← H.map_comp, hd, H.map_comp,
      ConcreteCategory.comp_apply, abstract_resolvedDerivedEquiv_spec]
  rw [hr, ← abstract_kInjectiveDerivedEquiv_naturality P P' hP hP' (I.obj K) (I.obj L)
    p (I.map f) ti (fun _ ↦ rfl)]
  congr 1
  have hn := congrArg DerivedCategory.Q.map (η.naturality f)
  simpa only [Functor.map_comp, Functor.id_map, Category.assoc] using
    congrArg (fun z ↦ DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map p) ≫ a ≫ z) hn

private theorem abstract_resolvedDerivedEquiv_eq_kInjective
    (P : A)
    (hP : genericGood P)
    (K : CochainComplex (A) ℤ) [K.IsKInjective]
    (a : DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj P) ⟶
      DerivedCategory.Q.obj K) :
    abstract_resolvedDerivedEquiv P hP K a = abstract_kInjectiveDerivedEquiv P hP K a := by
  let H := genericHypercohomology (A := A)
  apply ((H.mapIso (abstract_resolutionTensorIso P hP K)).addCommGroupIsoToAddEquiv).injective
  change H.map (abstract_resolutionTensorIso P hP K).hom _ =
    H.map (abstract_resolutionTensorIso P hP K).hom _
  rw [abstract_resolvedDerivedEquiv_spec]
  have h := abstract_kInjectiveDerivedEquiv_naturality P P hP hP K
    ((locallyFreeResolution).obj K) (𝟙 P) ((locallyFreeResolutionUnit).app K)
    (abstract_dualTensorComplexMap P P _ _ (𝟙 P) ((locallyFreeResolutionUnit).app K))
    (fun _ ↦ rfl) a
  simpa only [Functor.map_id, Category.id_comp, abstract_dualTensorComplexMap_id_left,
    abstract_resolutionTensorIso, asIso_hom] using h

private theorem generic_derivedHom :
    ∃ e : ∀ (P : A)
      (_ : genericGood P)
      (K : CochainComplex (A) ℤ)
      (_ : CochainComplex.plus _ K),
      ((DerivedCategory.singleFunctor _ 0).obj P ⟶ DerivedCategory.Q.obj K) ≃+
        (genericHypercohomology (A := A)).obj
          (DerivedCategory.Q.obj
            (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K)),
      (∀ (P P' : A)
        (hP : genericGood P) (hP' : genericGood P') (p : P' ⟶ P)
        (K L : CochainComplex (A) ℤ)
        (hK : CochainComplex.plus _ K) (hL : CochainComplex.plus _ L) (f : K ⟶ L)
        (t : ((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K ⟶
          ((genericDualTensor P').mapHomologicalComplex (.up ℤ)).obj L),
        (∀ i : ℤ, t.f i =
          genericDualTensorMap P P' (K.X i) (L.X i) p (f.f i)) →
        ∀ a : (DerivedCategory.singleFunctor _ 0).obj P ⟶ DerivedCategory.Q.obj K,
          e P' hP' L hL
            ((DerivedCategory.singleFunctor _ 0).map p ≫ a ≫ DerivedCategory.Q.map f) =
          (genericHypercohomology (A := A)).map (DerivedCategory.Q.map t)
            (e P hP K hK a)) ∧
      (∀ (P : A)
        (hP : genericGood P)
        (K : CochainComplex (A) ℤ)
        (hK : CochainComplex.plus _ K) (_ : K.IsKInjective)
        (z : ((genericTensorSections P).obj K).cycles 0)
        (f : (CochainComplex.singleFunctor _ 0).obj P ⟶ K),
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0 =
          genericEvaluate P (K.X 0)
            ((((genericTensorSections P).obj K).iCycles 0) z) →
        e P hP K hK (DerivedCategory.Q.map f) =
          genericSectionsComparison
            (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K)
            ((((genericTensorSections P).obj K).homologyπ 0) z)) := by
  refine ⟨fun P hP K _ ↦ abstract_resolvedDerivedEquiv P hP K, ?_, ?_⟩
  · intro P P' hP hP' p K L hK hL f t ht a
    exact abstract_resolvedDerivedEquiv_naturality P P' hP hP' p K L f t ht a
  · intro P hP K hK hI z f hf
    exact (abstract_resolvedDerivedEquiv_eq_kInjective P hP K (DerivedCategory.Q.map f)).trans
      (abstract_kInjectiveDerivedEquiv_cycle P hP K z f hf)


end AbstractModel

private theorem finiteLocallyFree_presheaf_isIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (P N : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hP : P.IsFiniteLocallyFree) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
      (PresheafOfModules.dualTensorHom (R := R.obj) P.val N.val)) := by
  let := hP
  obtain ⟨q, hq, hf⟩ := SheafOfModules.IsFiniteLocallyFree.exists_localGeneratorsData (M := P)
  have hb (V : C) (i : q.I) (g : V ⟶ q.X i) :
      Function.Bijective
        ((PresheafOfModules.dualTensorHom (R := R.obj) P.val N.val).app (op V)) := by
    have := (hf.isFiniteType i).finite
    have := hq.isIso i
    exact SheafOfModules.dualTensorHom_app_bijective_of_iso_free (R := R) P N
      (asIso (q.generators i).π) g
  let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let v := PresheafOfModules.dualTensorHom (R := R.obj) P.val N.val
  have hW : J.W ((PresheafOfModules.toPresheaf R₀.obj).map v) :=
    (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
      ⟨Presheaf.isLocallyInjective_of_coversTop q.coversTop _ fun V i g ↦ (hb V i g).1,
        Presheaf.isLocallySurjective_of_coversTop q.coversTop _ fun V i g ↦ (hb V i g).2⟩
  change J.W.inverseImage (PresheafOfModules.toPresheaf R₀.obj) v at hW
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)] at hW
  have : IsIso ((PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
      (PresheafOfModules.dualTensorHom (R := R.obj) P.val N.val)) := hW
  exact this

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u})

/-- The standard coefficient-universe sheaf-composition instance, cached for this proof.
Source: Mathlib sheaf composition
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
theorem locallyFreeHasSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance

attribute [local instance 100000] locallyFreeHasSheafCompose

/-- The standard abelian structure on module sheaves, without changing its data.
Source: Mathlib module sheaves
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev locallyFreeModuleAbelian : Abelian (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  inferInstance

attribute [local instance 100000] locallyFreeModuleAbelian

/-- The additive structure inherited from the cached abelian structure.
Source: Mathlib module sheaves
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev locallyFreeModulePreadditive : Preadditive (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  (locallyFreeModuleAbelian J R).toPreadditive

attribute [local instance 100000] locallyFreeModulePreadditive

/-- The standard sheaf structure, cached without changing its data.
Source: the sheaf tensor-Hom construction
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev proofMonoidal : MonoidalCategory (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  SheafOfModules.monoidalCategory R

attribute [local instance 100000] proofMonoidal

/-- The standard sheaf structure, cached without changing its data.
Source: the sheaf tensor-Hom construction
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev proofClosed : MonoidalClosed (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  SheafOfModules.monoidalClosed (R := R)

attribute [local instance 100000] proofClosed

set_option backward.isDefEq.respectTransparency true in
private theorem finiteLocallyFree_comparison_isIso
    (P N : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hP : P.IsFiniteLocallyFree) :
    IsIso (MonoidalClosed.ihomUnitTensorToIhom P N) := by
  have := finiteLocallyFree_presheaf_isIso (R := R) P N hP
  have hc := IsIso.comp_isIso' (Iso.isIso_hom
    (SheafOfModules.tensorObjIsoSheafification
      (SheafOfModules.homObj (R := R) P (SheafOfModules.unit _)) N))
    (IsIso.comp_isIso' this (inferInstance : IsIso
      ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit.app
        (SheafOfModules.homObj (R := R) P N))))
  exact (congrArg (fun f ↦ IsIso f)
    (SheafOfModules.dualTensorHom_comparison (C := C) (J := J) (R := R) P N)).mp hc

/-- The termwise tensor functor with P∨. Source: Stacks, Tag 08JJ
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev locallyFreeDualTensor
    (P : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  genericDualTensor P

/-- Tensoring with the dual is additive.
Source: Mathlib additive tensor functors
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
instance locallyFreeDualTensor_additive
    (P : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (locallyFreeDualTensor J R P).Additive := by
  dsimp [locallyFreeDualTensor]
  infer_instance

/-- The tensor map induced contravariantly by p and covariantly by f.
Source: Stacks, Tag 08JJ (blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def locallyFreeDualTensorMap
    (P P' M N : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (p : P' ⟶ P) (f : M ⟶ N) :
    (locallyFreeDualTensor J R P).obj M ⟶ (locallyFreeDualTensor J R P').obj N :=
  genericDualTensorMap P P' M N p f

/-- Global sections as Hom from the unit module. Source: Stacks, Tag 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev locallyFreeSections :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      AddCommGrpCat.{u} :=
  genericSections

/-- Global sections are additive. Source: Mathlib preadditive coyoneda.
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
instance locallyFreeSections_additive : (locallyFreeSections J R).Additive := by
  dsimp [locallyFreeSections]
  infer_instance

/-- Global cochains after termwise tensor by P∨. Source: Stacks, Tag 08JJ
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev locallyFreeTensorSections
    (P : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
        CochainComplex AddCommGrpCat.{u} ℤ :=
  genericTensorSections P

/-- Evaluation of a global section of P∨ ⊗ N, giving a map P → N.
Source: Stacks, Tag 08JJ (blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev locallyFreeEvaluate
    (P N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (z : SheafOfModules.unit _ ⟶ (locallyFreeDualTensor J R P).obj N) : P ⟶ N :=
  genericEvaluate P N z

private theorem locallyFree_genericGood
    (P : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hP : P.IsFiniteLocallyFree) : genericGood P := by
  refine ⟨fun N ↦ finiteLocallyFree_comparison_isIso J R P N hP, ?_⟩
  let := hP
  let D := SheafOfModules.homObj (R := R) P (SheafOfModules.unit _)
  have hD := SheafOfModules.IsFiniteLocallyFree.homObj_unit (R := R) P
  have := SheafOfModules.isIso_bidual (R := R) P
  let e : tensorLeft P ≅ genericDualTensor D :=
    (tensoringLeft _).mapIso (asIso (SheafOfModules.bidual (R := R) P))
  have hd := abstract_dualTensor_exact D
    (fun N ↦ finiteLocallyFree_comparison_isIso J R D N hD)
  exact transfer_finite_exact (tensorLeft P) (genericDualTensor D) e hd.1 hd.2

section

variable [HasDerivedCategory.{w} (ringedSiteModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]

/-- The standard additive structure on the derived category.
Source: Mathlib derived categories
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev locallyFreeDerivedPreadditive : Preadditive (DerivedCategory
    (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :=
  DerivedCategory.instPreadditive

attribute [local instance 100000] locallyFreeDerivedPreadditive

/-- The canonical ordinary-to-derived global cohomology map.
Source: Stacks, Tags 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev locallyFreeSectionsComparison
    (K : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    (((locallyFreeSections J R).mapHomologicalComplex (.up ℤ)).obj K).homology 0 ⟶
      (ringedSiteZerothHypercohomology J R).obj (DerivedCategory.Q.obj K) := by
  let A := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  exact genericSectionsComparison (A := A) K

end

attribute [local instance 100000] locallyFreeDerivedPreadditive

variable [HasDerivedCategory.{w} (ringedSiteModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]

private theorem locallyFreeHypercohomology_eq_model
    [IsGrothendieckAbelian.{u} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    genericHypercohomology (A := ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) =
      ringedSiteZerothHypercohomology J R := by
  rfl

/-- The evaluation-induced derived Hom formula, in degree zero on all shifts.
Source: Stacks, Tag 08JJ (blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom).

Proof:
1. The canonical comparison P∨ ⊗ N → Hom(P,N) is the sheafification of evaluation.
   On every member of a finite local trivialization it is bijective by the dual-basis
   calculation; local bijectivity makes its sheafification invertible.
2. Tensor by P∨ is both a left adjoint and, via this comparison, a right adjoint,
   hence exact. Apply this also to the locally free dual and the bidual isomorphism
   to obtain exactness of tensor by P. Its right adjoint Hom(P,-), hence tensor by P∨,
   preserves K-injective complexes.
3. Mathlib identifies zeroth homology of Hom(P,K) with homotopy classes of maps P[0] → K.
   The explicit cycle formula and its naturality follow from this identification.
   For K-injective K, localization identifies these classes with derived maps, and
   the ordinary-to-derived global cohomology comparison is invertible.
4. Use the constructed functorial K-injective resolution K → I(K). Postcompose derived
   maps with this quasi-isomorphism, use step 3, and invert hypercohomology of its
   tensor by P∨. Naturality of the resolution proves naturality in both variables.
   On K-injective K this agrees with step 3, proving the required cycle normalization.
   The construction works for arbitrary complexes and specializes to the stated
   bounded-below formulation, applied in degree zero to every shift.
-/
theorem locallyFree_derivedHom :
    ∃ e : ∀ (P : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (_ : P.IsFiniteLocallyFree)
      (K : CochainComplex (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
      (_ : CochainComplex.plus _ K),
      ((DerivedCategory.singleFunctor _ 0).obj P ⟶ DerivedCategory.Q.obj K) ≃+
        (ringedSiteZerothHypercohomology J R).obj
          (DerivedCategory.Q.obj
            (((locallyFreeDualTensor J R P).mapHomologicalComplex (.up ℤ)).obj K)),
      (∀ (P P' : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (hP : P.IsFiniteLocallyFree) (hP' : P'.IsFiniteLocallyFree) (p : P' ⟶ P)
        (K L : CochainComplex (ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
        (hK : CochainComplex.plus _ K) (hL : CochainComplex.plus _ L) (f : K ⟶ L)
        (t : ((locallyFreeDualTensor J R P).mapHomologicalComplex (.up ℤ)).obj K ⟶
          ((locallyFreeDualTensor J R P').mapHomologicalComplex (.up ℤ)).obj L),
        (∀ i : ℤ, t.f i =
          locallyFreeDualTensorMap J R P P' (K.X i) (L.X i) p (f.f i)) →
        ∀ a : (DerivedCategory.singleFunctor _ 0).obj P ⟶ DerivedCategory.Q.obj K,
          e P' hP' L hL
            ((DerivedCategory.singleFunctor _ 0).map p ≫ a ≫ DerivedCategory.Q.map f) =
          (ringedSiteZerothHypercohomology J R).map (DerivedCategory.Q.map t)
            (e P hP K hK a)) ∧
      (∀ (P : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (hP : P.IsFiniteLocallyFree)
        (K : CochainComplex (ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
        (hK : CochainComplex.plus _ K) (_ : K.IsKInjective)
        (z : ((locallyFreeTensorSections J R P).obj K).cycles 0)
        (f : (CochainComplex.singleFunctor _ 0).obj P ⟶ K),
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0 =
          locallyFreeEvaluate J R P (K.X 0)
            ((((locallyFreeTensorSections J R P).obj K).iCycles 0) z) →
        e P hP K hK (DerivedCategory.Q.map f) =
          locallyFreeSectionsComparison J R
            (((locallyFreeDualTensor J R P).mapHomologicalComplex (.up ℤ)).obj K)
            ((((locallyFreeTensorSections J R P).obj K).homologyπ 0) z)) := by
  let : IsGrothendieckAbelian.{u} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.isGrothendieckAbelian _
  let hg := locallyFree_genericGood J R
  obtain ⟨e, he, hz⟩ := generic_derivedHom (A := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  refine ⟨fun P hP K hK ↦ e P (hg P hP) K hK, ?_, ?_⟩
  · intro P P' hP hP' p K L hK hL f t ht a
    exact he P P' (hg P hP) (hg P' hP') p K L hK hL f t ht a
  · intro P hP K hK hI z f hf
    dsimp only [locallyFreeTensorSections, locallyFreeEvaluate,
      locallyFreeSectionsComparison, locallyFreeDualTensor] at z hf ⊢
    have hz' := hz P (hg P hP) K hK hI z f
    have hh := hz' hf
    set_option backward.isDefEq.respectTransparency true in
      convert hh using 1
      · exact congrArg (fun (H : DerivedCategory (ringedSiteModules.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤ AddCommGrpCat.{u}) ↦
          ((H.obj (DerivedCategory.Q.obj
          (((genericDualTensor P).mapHomologicalComplex (.up ℤ)).obj K))) : Type u))
          (locallyFreeHypercohomology_eq_model J R).symm
      · exact HEq.refl ((e P (hg P hP) K hK) (DerivedCategory.Q.map f))
      · rfl

end CategoryTheory
