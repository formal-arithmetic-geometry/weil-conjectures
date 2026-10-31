/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedCoefficientFamilies
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcPullbackCoherentFamily
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarCompletionUnitSquare
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated

/-! # Strict completed-pullback coefficient family argument

Source: current blueprint, coefficient coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
private def conjugateStageMorphism
    {I : Type*} [Preorder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {D : I → Type*} [∀ i, Category (D i)]
    {S : StageSystem C} {T : StageSystem D}
    (F : StageSystem.Morphism S T) (G : ∀ i, C i ⥤ D i)
    (e : ∀ i, F.Φ i ≅ G i) : StageSystem.Morphism S T where
  Φ := G
  β h := Functor.isoWhiskerRight (e _).symm _ ≪≫ F.β h ≪≫
    Functor.isoWhiskerLeft _ (e _)
  coh {i j k} h h' K := by
    simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc (T.T h')
      ((e j).hom.app ((S.T h).obj K)) ((e j).inv.app ((S.T h).obj K)),
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← (e k).hom.naturality]
    rw [reassoc_of% F.coh h h' K]
    exact (T.assoc h h').hom.naturality_assoc ((e i).inv.app K) _

private theorem transportUnit
    {C : Type*} [Category C] {A B D E F : C}
    (a : A ≅ B) (b : D ≅ E) (c : D ≅ F)
    (u : A ⟶ D) (v : B ⟶ E) (w : A ⟶ F)
    (h : u ≫ b.hom = a.hom ≫ v) (h' : u ≫ c.hom = w) :
    v ≫ b.inv ≫ c.hom = a.inv ≫ w := by
  apply (cancel_epi a.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← h]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h'

private def localizedIntegralIso
    {R : Type*} [CommRing R] (p : R)
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {D : Type*} [Category D] [Preadditive D] [Linear R D]
    {F G : C ⥤ D} [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
    (e : F ≅ G) : ScalarLocalization.transport R p F ≅
      ScalarLocalization.transport R p G :=
  NatIso.ofComponents
    (fun K ↦ (ScalarLocalization.localization R D p).mapIso (e.app K.obj))
    (fun f ↦ ScalarLocalization.transportNat_naturality R p e.hom _ _ f)

namespace AlgebraicGeometry.Scheme

structure CbcCompletedPullCoefficientFamilyCore (l : ℕ) (Ω : Type w)
    [Fact l.Prime] [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    (g : Y ⟶ X) where
  preserves : ∀ E (K : pbcIntegralStage l Ω X E),
    PbcIsBoundedConstructibleComplete Y (pbcStageDatum l Ω E)
      (((pbcStageDatum l Ω E).completedPull g).obj K.obj)
  family : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω X dX.out iX.out)
    (pbcScalarSystem l Ω Y dY.out iY.out)
  localization : ∀ E,
    pbcStageLocalization l Ω X E ⋙ family.base.Φ E =
      pbcConditionalIntegral (pbcStageDatum l Ω E)
        ((pbcStageDatum l Ω E).completedPull g) (preserves E) ⋙
        pbcStageLocalization l Ω Y E
  reflectorFamily : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω X dX.out iX.out)
    (pbcScalarSystem l Ω Y dY.out iY.out)
  reflectorPhi : ∀ E,
    reflectorFamily.base.Φ E =
      pbcDescentPullback l Ω g (pbcQbarIntegralPull_mem l Ω g) E
  reflectorBeta : PbcPullbackBetaSpec l Ω g (pbcQbarIntegralPull_mem l Ω g)
    reflectorFamily.base
  ambientTransport : ∀ E : Padic.FiniteCoefficientFields l Ω,
    (pbcStageDatum l Ω E).completedPull g ≅
      pbcActualCompletedPull g (pbcStageDatum l Ω E)
  ambientUnit : ∀ E (K : pbcAmbientStage l Ω X E),
    (pbcStageDatum l Ω E).ordinaryToCompleted g K ≫
        (ambientTransport E).hom.app K =
      (cbcDatumOrdinaryTransport (pbcStageDatum l Ω E) g).inv.app K ≫
        (pbcActualCompletedPullUnit g (pbcStageDatum l Ω E)).app K
  integralTransport : ∀ E,
    pbcConditionalIntegral (pbcStageDatum l Ω E)
        ((pbcStageDatum l Ω E).completedPull g) (preserves E) ≅
      pbcConditionalIntegral (pbcStageDatum l Ω E)
        (pbcActualCompletedPull g (pbcStageDatum l Ω E))
        (pbcQbarIntegralPull_mem l Ω g E)
  integralTransport_hom : ∀ E (K : pbcIntegralStage l Ω X E),
    HEq ((integralTransport E).hom.app K).hom ((ambientTransport E).hom.app K.obj)
  rationalTransport : ∀ E, reflectorFamily.base.Φ E ≅ family.base.Φ E
  rationalTransport_hom : ∀ E (K : pbcIntegralStage l Ω X E),
    HEq ((rationalTransport E).hom.app ((pbcStageLocalization l Ω X E).obj K))
      ((eqToIso (reflectorPhi E)).hom.app ((pbcStageLocalization l Ω X E).obj K) ≫
        (pbcStageLocalization l Ω Y E).map ((integralTransport E).inv.app K))
  transportedBeta : ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F),
    family.base.β h =
      Functor.isoWhiskerRight (rationalTransport E).symm
          ((pbcScalarSystem l Ω Y dY.out iY.out).T h) ≪≫
        reflectorFamily.base.β h ≪≫
          Functor.isoWhiskerLeft ((pbcScalarSystem l Ω X dX.out iX.out).T h)
            (rationalTransport F)

/-- Strict completed-pullback core family.

Source: current blueprint, coefficient coherence.
(blueprint: lem-cbc-normalized-pull-family-core)

Proof: Use pbcActualAmbientCompletedPullback_tower composed with
cbcDatumActualStrictTransport.symm to identify datum completed pullback with
pbcActualCompletedPull. Cancel cbcDatumOrdinaryTransport to obtain its unit identity. Transport
pbcQbarIntegralPull_mem using closure under isomorphism. Restrict the ambient iso to the full
integral categories. Transport additivity and linearity to the restricted functor and apply
ScalarLocalization.transport. Obtain pbcPullbackCoherentFamily with the established reflector
preservation. Conjugate by its pointwise functor equalities and then by the localized restricted
iso. Define the stage beta by this conjugation. Expand the two sides of the associator equation;
cancel adjacent inverse comparisons and use naturality and the reflector associator equation.
Transfer CommShift by Functor.CommShift.ofIso and exactness by Functor.isTriangulated_of_iso.
Literal objects and the baseChange_tmul formula give the integral localization equality. Record
all the transport components and beta formula by their constructions. The reflector beta
specification is retained unchanged.
-/
theorem cbcCompletedPullCoefficientFamilyCore_exists (l : ℕ) (Ω : Type w)
    [Fact l.Prime] [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    (g : Y ⟶ X) : Nonempty (CbcCompletedPullCoefficientFamilyCore l Ω g) := by
  classical
  let ambient (E : Padic.FiniteCoefficientFields l Ω) :
      (pbcStageDatum l Ω E).completedPull g ≅
        pbcActualCompletedPull g (pbcStageDatum l Ω E) :=
    (cbcDatumActualStrictTransport (pbcStageDatum l Ω E) g).symm ≪≫
      pbcActualAmbientCompletedPullbackIso (pbcStageDatum l Ω E) g
  have unit (E : Padic.FiniteCoefficientFields l Ω) (K : pbcAmbientStage l Ω X E) :
      (pbcStageDatum l Ω E).ordinaryToCompleted g K ≫ (ambient E).hom.app K =
        (cbcDatumOrdinaryTransport (pbcStageDatum l Ω E) g).inv.app K ≫
          (pbcActualCompletedPullUnit g (pbcStageDatum l Ω E)).app K := by
    exact transportUnit
      ((cbcDatumOrdinaryTransport (pbcStageDatum l Ω E) g).app K)
      ((cbcDatumActualStrictTransport (pbcStageDatum l Ω E) g).app K)
      ((pbcActualAmbientCompletedPullbackIso (pbcStageDatum l Ω E) g).app K)
      _ _ _ (cbcDatumActualStrictTransport_unit (pbcStageDatum l Ω E) g K)
      ((pbcActualAmbientCompletedPullback_tower (pbcStageDatum l Ω E) g).exists.choose_spec K)
  have pres (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E) :
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum l Ω E)
        (((pbcStageDatum l Ω E).completedPull g).obj K.obj) := by
    let := (pbcIntegralUniformComplete_isTriangulated l (pbcFiniteField l Ω E)
      Y dY.out iY.out).1
    exact ObjectProperty.prop_of_iso _ ((ambient E).app K.obj).symm
      (pbcQbarIntegralPull_mem l Ω g E K)
  let strictIntegral (E : Padic.FiniteCoefficientFields l Ω) :=
    pbcConditionalIntegral (pbcStageDatum l Ω E)
      ((pbcStageDatum l Ω E).completedPull g) (pres E)
  let reflectorIntegral (E : Padic.FiniteCoefficientFields l Ω) :=
    pbcConditionalIntegral (pbcStageDatum l Ω E)
      (pbcActualCompletedPull g (pbcStageDatum l Ω E)) (pbcQbarIntegralPull_mem l Ω g E)
  let integral (E : Padic.FiniteCoefficientFields l Ω) :
      strictIntegral E ≅ reflectorIntegral E :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk (P := PbcIsBoundedConstructibleComplete Y
        (pbcStageDatum l Ω E)) ((ambient E).app K.obj))
      (by intro K L f; apply ObjectProperty.hom_ext; exact (ambient E).hom.naturality f.hom)
  let strictAdd (E : Padic.FiniteCoefficientFields l Ω) : (strictIntegral E).Additive :=
    Functor.additive_of_iso (integral E).symm
  let strictLin (E : Padic.FiniteCoefficientFields l Ω) :
      (strictIntegral E).Linear (PbcIntegralRing l (pbcFiniteField l Ω E)) :=
    Functor.linear_of_iso _ (integral E).symm
  let strictRational (E : Padic.FiniteCoefficientFields l Ω) :=
    ScalarLocalization.transport (PbcIntegralRing l (pbcFiniteField l Ω E))
      (pbcStageUniformizer l Ω E) (strictIntegral E)
  obtain ⟨R, hR, hβ⟩ := pbcPullbackCoherentFamily l Ω g (pbcQbarIntegralPull_mem l Ω g)
  let rational (E : Padic.FiniteCoefficientFields l Ω) : R.base.Φ E ≅ strictRational E :=
    eqToIso (hR E) ≪≫ localizedIntegralIso (pbcStageUniformizer l Ω E) (integral E).symm
  let := R.commShift
  let B := conjugateStageMorphism R.base strictRational rational
  let cs (E : Padic.FiniteCoefficientFields l Ω) : (strictRational E).CommShift ℤ :=
    Functor.CommShift.ofIso (rational E) ℤ
  let := cs
  let compat (E : Padic.FiniteCoefficientFields l Ω) :
      NatTrans.CommShift (rational E).hom ℤ :=
    Functor.CommShift.ofIso_compatibility (rational E) ℤ
  let F : StageSystem.CoherentExactMorphism
      (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out) := {
    base := B
    additive := fun E ↦ inferInstanceAs ((strictRational E).Additive)
    commShift := cs
    betaCommShift := by
      intro E F h
      let := R.betaCommShift h
      let := compat E
      let := compat F
      change NatTrans.CommShift
        ((Functor.isoWhiskerRight (rational E).symm _ ≪≫ R.base.β h ≪≫
          Functor.isoWhiskerLeft _ (rational F)).hom) ℤ
      simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
        Functor.isoWhiskerLeft_hom]
      infer_instance
    triangulated := by
      intro E
      let := R.triangulated E
      exact Functor.isTriangulated_of_iso (rational E) }
  refine ⟨{
    preserves := pres
    family := F
    localization := ?_
    reflectorFamily := R
    reflectorPhi := hR
    reflectorBeta := hβ
    ambientTransport := ambient
    ambientUnit := unit
    integralTransport := integral
    integralTransport_hom := fun E K ↦ HEq.rfl
    rationalTransport := rational
    rationalTransport_hom := fun E K ↦ HEq.rfl
    transportedBeta := fun h ↦ rfl }⟩
  intro E
  apply CategoryTheory.Functor.ext
  · intro K L f
    simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
    exact LinearMap.baseChange_tmul _ _ _
  · intro K
    rfl

end AlgebraicGeometry.Scheme
