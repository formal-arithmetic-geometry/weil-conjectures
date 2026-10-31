/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterEvaluationData
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.CondensedActionInjectiveRestriction

/-! # Canonical free-parameter evaluation data and coherence.
Source: Stacks 08J7, 07A6, 07A7 (blueprint: def-sfb-free-parameter-degree-zero-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FreeParameterEvaluation

section TensorComparison
variable {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

private def flatTensorSingleIso (F : C) (hF : ObjectProperty.flat F) :
    DerivedCategory.Q ⋙ tensorRight ((DerivedCategory.singleFunctor C 0).obj F) ≅
      (tensorRight F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun K ↦
    whiskerLeftIso (DerivedCategory.Q.obj K)
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app F) ≪≫
    DerivedCategory.QObjTensorQObjIsoOfKFlatRight K
      ((CochainComplex.singleFunctor C 0).obj F)
      ((CochainComplex.kFlat_single_obj_iff_flat F 0).mpr hF) ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) F).app K))
    (by
      intro K L f
      change DerivedCategory.Q.map f ▷ _ ≫ _ = _ ≫ DerivedCategory.Q.map
        (((tensorRight F).mapHomologicalComplex (.up ℤ)).map f)
      simp only [Iso.trans_hom, whiskerLeftIso_hom, Functor.mapIso_hom, Category.assoc]
      erw [← whisker_exchange_assoc,
        DerivedCategory.qObjTensorQObjIsoOfKFlatRight_hom_naturality_assoc,
        ← DerivedCategory.Q.map_comp]
      erw [(CochainComplex.map₂HomologicalComplexFlipObjSingleIso
        (curriedTensor C) F).hom.naturality]
      simp only [DerivedCategory.Q.map_comp]
      rfl)

private lemma flatTensorSingleIso_eq (F : C) (hF : ObjectProperty.flat F)
    (K : CochainComplex C ℤ)
    (hK : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K) :
    (flatTensorSingleIso F hF).app K =
      DerivedCategory.QObjTensorSingleFunctorObjIso K hK F := by
  apply Iso.ext
  simp only [flatTensorSingleIso, NatIso.ofComponents_hom_app, Iso.app_hom,
    Iso.trans_hom, whiskerLeftIso_hom,
    DerivedCategory.QObjTensorSingleFunctorObjIso,
    DerivedCategory.QObjTensorQObjIsoOfKFlatRight, tensorIso_hom,
    Iso.trans_hom, Iso.app_hom, Iso.symm_hom, asIso_hom, Functor.mapIso_hom,
    Category.assoc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  erw [← (DerivedCategory.quotientCompQhIso C).hom.naturality]
  rfl

attribute [local instance] DerivedCategory.braidedCategory'

private def flatTensorComparisonOnComplexes (F : C) (hF : ObjectProperty.flat F) :
    DerivedCategory.Q ⋙ tensorLeft ((DerivedCategory.singleFunctor C 0).obj F) ≅
      (tensorLeft F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (BraidedCategory.tensorLeftIsoTensorRight ((DerivedCategory.singleFunctor C 0).obj F)) ≪≫
    flatTensorSingleIso F hF ≪≫
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight F).symm (.up ℤ)) DerivedCategory.Q

private def flatTensorComparison (F : C) (hF : ObjectProperty.flat F)
    [PreservesFiniteLimits (tensorLeft F)] :
    (tensorLeft F).mapDerivedCategory ≅
      tensorLeft ((DerivedCategory.singleFunctor C 0).obj F) :=
  (Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    _ _ _ _ (flatTensorComparisonOnComplexes F hF)).symm

private lemma flatTensorComparison_fac (F : C) (hF : ObjectProperty.flat F)
    [PreservesFiniteLimits (tensorLeft F)] (K : CochainComplex C ℤ) :
    (flatTensorComparison F hF).inv.app (DerivedCategory.Q.obj K) ≫
      (tensorLeft F).mapDerivedCategoryFactors.hom.app K =
        (flatTensorComparisonOnComplexes F hF).hom.app K := by
  simp [flatTensorComparison, Localization.liftNatIso, Localization.Lifting.iso,
    Category.assoc]

private lemma flatTensorComparison_normalization (F : C) (hF : ObjectProperty.flat F)
    [PreservesFiniteLimits (tensorLeft F)] (K : CochainComplex C ℤ)
    (hK : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K) :
    (flatTensorComparison F hF).inv.app (DerivedCategory.Q.obj K) ≫
        (tensorLeft F).mapDerivedCategoryFactors.hom.app K =
      (β_ ((DerivedCategory.singleFunctor C 0).obj F) (DerivedCategory.Q.obj K)).hom ≫
        (DerivedCategory.QObjTensorSingleFunctorObjIso K hK F).hom ≫
        DerivedCategory.Q.map (((NatIso.mapHomologicalComplex
          (BraidedCategory.tensorLeftIsoTensorRight F).symm (.up ℤ)).app K).hom) := by
  rw [flatTensorComparison_fac]
  change (β_ ((DerivedCategory.singleFunctor C 0).obj F) (DerivedCategory.Q.obj K)).hom ≫
    (flatTensorSingleIso F hF).hom.app K ≫ _ = _
  rw [← Iso.app_hom, flatTensorSingleIso_eq F hF K hK]
  rfl

private lemma tensorIso_ext_kFlat {F G : DerivedCategory C ⥤ DerivedCategory C}
    (e e' : F ≅ G)
    (h : ∀ (K : CochainComplex C ℤ)
      (_ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K),
      e.inv.app (DerivedCategory.Q.obj K) = e'.inv.app (DerivedCategory.Q.obj K)) :
    e = e' := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext Y
  obtain ⟨K, π, hπ, _, hK⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage Y)
  have : QuasiIso π := hπ
  have : IsIso (DerivedCategory.Q.map π) := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  let i : DerivedCategory.Q.obj K ≅ Y :=
    asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso Y
  rw [← cancel_epi (G.map i.hom), e.inv.naturality, e'.inv.naturality, h K hK]

end TensorComparison
variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

attribute [local instance] PointDerivedHom.pullMonoidal
attribute [local instance] DerivedCategory.braidedCategory'


/-- The representable free parameter is flat, with no projectivity assertion.
Source: Stacks 03EK and node proof step 10
(blueprint: def-sfb-free-parameter-degree-zero-data).
Proof: the free adjunction identifies A_P with extension by zero of the regular
module on the representable P. Extension by zero of this flat regular module is
flat. Equivalently tensoring is locally a direct sum of copies indexed by maps
to P; sheafification is exact and filtered local refinements preserve kernels. -/
theorem freeParameter_flat (P : Profinite.{u}) :
    ObjectProperty.flat (freeParameter R P) := by
  let A : CategoryTheory.CondensedBar.Ring.{u} := ⟨R.X⟩
  obtain ⟨_, _, h, _⟩ := Profinite.CondensedAction.restriction_free_flat_comparison A
  obtain ⟨_, _, hlim, _⟩ := h P
  exact (ObjectProperty.flat_iff_preservesFiniteLimits _).mpr hlim

/-- Exact tensoring with the representable free parameter.
Source: Stacks 03EK (blueprint: def-sfb-free-parameter-degree-zero-data). -/
instance parameterTensorLimits (P : Profinite.{u}) :
    PreservesFiniteLimits (tensorLeft (freeParameter R P)) :=
  (ObjectProperty.flat_iff_preservesFiniteLimits _).mp (freeParameter_flat R P)

/-- The unique tensor comparison normalized on actual K-flat representatives.
This fixes the link between the recorded closed derived Hom and the unary
K-injective right derived Hom used only to compute degree zero.
Source: Stacks 08J7, node proof step 3
(blueprint: def-sfb-free-parameter-degree-zero-data).
Proof: tensoring with the flat A_P is exact, so its total left derived functor
is termwise tensoring. The K-flat tensor comparison, followed by the braiding
and single-complex identification, gives the displayed representative formula.
It descends through quasi-isomorphisms to the asserted natural isomorphism.
Every derived object has a K-flat representative, proving uniqueness. -/
theorem parameterTensor_existsUnique (P : Profinite.{u}) :
    ∃! e : (tensorLeft (freeParameter R P)).mapDerivedCategory ≅
      tensorLeft (parameterD R P),
      ∀ (K : CochainComplex (PointModules R) ℤ)
        (hK : (HomologicalComplex.quasiIso (PointModules R) (.up ℤ)).kFlat K),
        e.inv.app (DerivedCategory.Q.obj K) ≫
          (tensorLeft (freeParameter R P)).mapDerivedCategoryFactors.hom.app K =
        (β_ (parameterD R P) (DerivedCategory.Q.obj K)).hom ≫
          (DerivedCategory.QObjTensorSingleFunctorObjIso K hK (freeParameter R P)).hom ≫
          DerivedCategory.Q.map
            (((NatIso.mapHomologicalComplex
              (BraidedCategory.tensorLeftIsoTensorRight (freeParameter R P)).symm
              (.up ℤ)).app K).hom) := by
  let e := flatTensorComparison (freeParameter R P) (freeParameter_flat R P)
  have he := flatTensorComparison_normalization (freeParameter R P) (freeParameter_flat R P)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply tensorIso_ext_kFlat e' e
  intro K hK
  rw [← cancel_mono ((tensorLeft (freeParameter R P)).mapDerivedCategoryFactors.hom.app K),
    he' K hK, he K hK]

/-- Canonical tensor comparison selected from a uniqueness specification.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-degree-zero-data). -/
def parameterTensor (P : Profinite.{u}) := (parameterTensor_existsUnique R P).choose

/-- The actual linking isomorphism: uniqueness of right adjoints transports the
normalized tensor comparison. The main functors remain closed derived Hom.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-degree-zero-data). -/
def unaryHomComparison (P : Profinite.{u}) :
    functions R P ≅ (ihom (freeParameter R P)).rightDerivedFunctor :=
  Adjunction.rightAdjointUniq (ihom.adjunction (parameterD R P))
    (((ihom.adjunction (freeParameter R P)).derivedAdjunction).ofNatIsoLeft
      ((tensorLeft (freeParameter R P)).leftDerivedFunctorIsoMapDerivedCategory ≪≫
        parameterTensor R P))

/-- Underived generator evaluation using the existing strong tensor comparison.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-degree-zero-data). -/
def evaluationApp (X : Scheme.{u}) (P : Profinite.{u}) (N : PointModules R) :
    (pointPull R (testScheme X P)).obj ((ihom (freeParameter R P)).obj N) ⟶
      (pointPull R (testScheme X P)).obj N :=
  letI : (pointPull R (testScheme X P)).Monoidal :=
    PointDerivedHom.pullMonoidal R.X (testScheme X P)
  (λ_ _).inv ≫ (parameterGenerator R X P ⊗ₘ 𝟙 _) ≫
    (Functor.Monoidal.μIso (pointPull R (testScheme X P))
      (freeParameter R P) ((ihom (freeParameter R P)).obj N)).hom ≫
    (pointPull R (testScheme X P)).map ((ihom.ev (freeParameter R P)).app N)

/-- Canonical degree-zero identification for a left exact total right derived functor.
This uses the ordinary injective-resolution comparison and R^0=F, not a chosen map.
Source: Stacks 08J7, proof step 3
(blueprint: def-sfb-free-parameter-degree-zero-data). -/
def degreeZero {C : Type (u + 2)} {D : Type (u + 2)}
    [Category.{u + 1} C] [Category.{u + 1} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
    [EnoughInjectives C] [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] (M : C) :
    (DerivedCategory.homologyFunctor D 0).obj
      (G.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M)) ≅ G.obj M :=
  G.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫ G.rightDerivedZeroIsoSelf.app M

/-- The canonical H^0 identification of F on a degree-zero coefficient module.
Source: Stacks 08J7, proof step 3
(blueprint: def-sfb-free-parameter-degree-zero-data). -/
def sourceZero (X : Scheme.{u}) (P : Profinite.{u}) (N : PointModules R) :=
  ((pointPull R X).mapDerivedCategoryHomologyFunctorIso 0).symm.app
      ((functions R P).obj ((DerivedCategory.singleFunctor (PointModules R) 0).obj N)) ≪≫
    (pointPull R X).mapIso
      ((DerivedCategory.homologyFunctor (PointModules R) 0).mapIso
        ((unaryHomComparison R P).app
          ((DerivedCategory.singleFunctor (PointModules R) 0).obj N)) ≪≫
        degreeZero (ihom (freeParameter R P)) N)

/-- The canonical H^0 identification of L on a degree-zero coefficient module.
Source: Stacks 08J7, proof step 3
(blueprint: def-sfb-free-parameter-degree-zero-data). -/
def targetZero (X : Scheme.{u}) (P : Profinite.{u}) (N : PointModules R) :=
  (DerivedCategory.homologyFunctor (Modules R X) 0).mapIso
    ((CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).mapIso
      (((pointPull R (testScheme X P)).mapDerivedCategorySingleFunctor 0).app N)) ≪≫
    degreeZero (CondensedRing.lowerStar R.X (projection X P))
      ((pointPull R (testScheme X P)).obj N)

end AlgebraicGeometry.ProEtale.FreeParameterEvaluation
