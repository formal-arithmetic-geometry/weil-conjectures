/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformLocalModelCohomology
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleClosedProjection.ProEtaleClosedUnderivedProjection
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.Algebra.Homology.Finite.FiniteFreeMonoCokernelKFlat
import WeilConjectures.AlgebraicGeometry.Pbc.PbcIntrinsicTowerComplete
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
import WeilConjectures.AlgebraicGeometry.Pbc.PbcFiniteDirectImageCohomology
import WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.SmoothPurity.DimensionExtension
import Mathlib.Algebra.Divisibility.Units
import Mathlib.GroupTheory.OrderOfElement
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReduction
import WeilConjectures.Algebra.Homology.ProperBaseChange.UniformPerfectQuotientBound

/-! # Finite-reduction control for completed coefficient operations

Source: blueprint proper base change, constructible-preservation proof, steps 1, 3--5.
The conclusion records cohomology, before local models and etale witnesses are assembled.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- One cohomological window for the canonical reductions.
No local models or etale origins are asserted. Source: Stacks 09C7, 099N and 09AL
(blueprint: lem-weil-pbc-completed-constructible-reduction-control). -/
def PbcConstructibleReductionControl
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) : Prop :=
  ∃ a b : ℤ, a ≤ b ∧
      (∀ (n : ℕ) (q : ℤ),
        @IsConstructibleProEtaleCoefficientModuleSheaf T (A ⧸ d.ideal ^ (n + 1)) _
          (d.quotientFinite n)
          ((pbcRestrict (pbcLevelConstantComparison T d n).hom).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((pbcCompletedReduction T d n).obj K)))) ∧
      (∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcCompletedReduction T d n).obj K)))

private theorem control_quotient_models
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ∃ r : ℕ, ∀ n : ℕ,
      ∃ (F : CochainComplex (ModuleCat.{u + 1} A) ℤ)
        (ε : F ⟶ (CochainComplex.singleFunctor _ 0).obj
          (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))),
        QuasiIso ε ∧
        (∀ q : ℤ, Module.Projective A (F.X q) ∧ Module.Finite A (F.X q)) ∧
        (∀ q : ℤ, q < -(r : ℤ) ∨ 0 < q → IsZero (F.X q)) := by
  classical
  let : IsNoetherianRing A := d.noetherian
  have hmodels (n : ℕ) :
      ∃ (F : CochainComplex (ModuleCat.{u + 1} A) ℤ)
        (ε : F ⟶ (CochainComplex.singleFunctor _ 0).obj
          (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))),
        QuasiIso ε ∧ ∃ a b : ℤ, F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
          ∀ q : ℤ, Module.Projective A (F.X q) ∧ Module.Finite A (F.X q) := by
    let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
    obtain ⟨F, a, b, ha, hb, hF, ⟨eF⟩⟩ := d.quotientPerfect (n + 1) (by omega)
    have := ha
    have := hb
    have (q : ℤ) : Module.Projective A (F.X q) := (hF q).1
    have (q : ℤ) : Projective (F.X q) := inferInstance
    obtain ⟨ε, hε⟩ := DerivedCategory.Q_map_surjective_of_projective F
      ((CochainComplex.singleFunctor _ 0).obj
        (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))) b eF.inv
    have : IsIso (DerivedCategory.Q.map ε) := by rw [hε]; infer_instance
    exact ⟨F, ε, (DerivedCategory.isIso_Q_map_iff_quasiIso _ ε).mp inferInstance,
      a, b, ha, hb, hF⟩
  let := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} A)
  have hperfect (n : ℕ) (hn : 1 ≤ n) :
      DerivedCategory.IsPerfect ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        (ModuleCat.of A (A ⧸ d.ideal ^ n))) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    obtain ⟨F, ε, hε, a, b, ha, hb, hf⟩ := hmodels k
    let := hε
    exact ⟨F, a, b, ha, hb, hf, ⟨(asIso (DerivedCategory.Q.map ε)).symm⟩⟩
  obtain ⟨r, hr, _⟩ := ModuleCat.exists_uniform_finite_projective_resolution_quotient_pow
    d.ideal (fun n hn ↦ by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact d.quotientFinite k) hperfect
  refine ⟨r, fun n ↦ ?_⟩
  obtain ⟨P, hfin, hzero⟩ := hr (n + 1) (by omega)
  let F := P.complex.extend ComplexShape.embeddingDownNat
  let ε := HomologicalComplex.extendMap P.π ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1))) 0 0 rfl).hom
  have hε : QuasiIso ε := by
    dsimp only [ε]
    infer_instance
  refine ⟨F, ε, hε, ?_, ?_⟩
  · intro q
    have : Projective (F.X q) := inferInstance
    refine ⟨inferInstance, ?_⟩
    by_cases hq : ∃ k : ℕ, -(k : ℤ) = q
    · obtain ⟨k, hk⟩ := hq
      have := hfin k
      exact Module.Finite.equiv
        (P.complex.extendXIso ComplexShape.embeddingDownNat hk).toLinearEquiv.symm
    · have hz : IsZero (F.X q) := P.complex.isZero_extend_X
        ComplexShape.embeddingDownNat q (by simpa using hq)
      have := ModuleCat.subsingleton_of_isZero hz
      infer_instance
  · intro q hq
    rcases hq with hq | hq
    · have hq' : q ≤ 0 := by omega
      obtain ⟨k, hk⟩ : ∃ k : ℕ, -(k : ℤ) = q := ⟨(-q).toNat, by omega⟩
      exact (hzero k (by omega)).of_iso
        (P.complex.extendXIso ComplexShape.embeddingDownNat hk)
    · exact CochainComplex.isZero_of_isStrictlyLE F 0 q hq

private theorem control_functor_flat
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (H : ModuleCat.{u + 1} A ⥤ pbcModules T R) [H.Additive]
    [PreservesFiniteColimits H]
    (e : H.obj (ModuleCat.of A A) ≅ SheafOfModules.unit ((adicLisseForget T).obj R))
    (M : ModuleCat.{u + 1} A) [Module.Finite A M] [Module.Projective A M] :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) (H.obj M) := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.cochainModulesPreadditive R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  have : HasFiniteBiproducts (pbcModules T R) := Abelian.hasFiniteBiproducts
  obtain ⟨r, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let V := fun _ : Fin r ↦ ModuleCat.of A A
  let j : ModuleCat.of A (Fin r → A) ≅ ∐ V :=
    (ModuleCat.piIsoPi V).symm ≪≫ biproductIso V
  let v : H.obj (∐ V) ≅ ∐ (fun _ : Fin r ↦
      SheafOfModules.unit ((adicLisseForget T).obj R)) :=
    PreservesCoproduct.iso H V ≪≫ Sigma.mapIso (fun _ ↦ e)
  let ret : Retract (H.obj M) (∐ (fun _ : Fin r ↦
      SheafOfModules.unit ((adicLisseForget T).obj R))) :=
    { i := H.map (ModuleCat.ofHom g ≫ j.hom) ≫ v.hom
      r := v.inv ≫ H.map (j.inv ≫ ModuleCat.ofHom f)
      retract := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, ← H.map_comp]
        have hh : ModuleCat.ofHom g ≫ ModuleCat.ofHom f = 𝟙 M :=
          ModuleCat.hom_ext hfg
        rw [hh, H.map_id] }
  have hflat : ObjectProperty.flat (H.obj M) := ObjectProperty.flat_of_retract ret
    (flat_finite_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _))
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R _).symm hflat.2

private theorem control_extension_bound
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (F : CochainComplex (pbcModules T R) ℤ) (r : ℕ)
    (hb : ∀ q : ℤ, q < -(r : ℤ) ∨ 0 < q → IsZero (F.X q))
    (hf : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) (F.X q))
    (eF : DerivedCategory.Q.obj F ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj S))))
    (K : DerivedCategory (pbcModules T R)) (a : ℤ) [K.IsGE a] :
    ((pbcDerivedExtend φ).obj K).IsGE (a - r) := by
  classical
  let C := pbcModules T R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  let := SheafOfModules.cochainModulesPreadditive R
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} C
  let : IsGrothendieckAbelian.{u + 1} C :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, u + 1}
      (ProEt.topology T) ((adicLisseForget T).obj R)
  have := DerivedCategory.hasDerivedMonoidalCategory C
  let : MonoidalCategory (DerivedCategory C) := inferInstance
  have hFa : F.IsStrictlyGE (-(r : ℤ)) := (F.isStrictlyGE_iff _).2
    (fun q hq ↦ hb q (Or.inl hq))
  have hFb : F.IsStrictlyLE 0 := (F.isStrictlyLE_iff _).2
    (fun q hq ↦ hb q (Or.inr hq))
  have hflat (q : ℤ) : ObjectProperty.flat (F.X q) := by
    have hr : exactFunctor C C (MonoidalCategory.tensorRight (F.X q)) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R _) (hf q)
    exact ⟨(exactFunctor C C).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight _).symm hr, hr⟩
  have htor := DerivedCategory.torAmplitudeIn_Q_obj_of_flat F (-(r : ℤ)) 0 hflat
  have hbound := DerivedCategory.isGE_tensor_of_torAmplitudeIn htor K a
  let N := (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj S))
  obtain ⟨P, p, hP, hpflat, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := R) (DerivedCategory.Q.objPreimage K)
  let := hp
  let eP := asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hk : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro Z hZ
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
    have hz : HomotopyCategory.subcategoryAcyclic C
        (MonoidalCategory.tensorObj ((HomotopyCategory.quotient C (.up ℤ)).obj Z)
          ((HomotopyCategory.quotient C (.up ℤ)).obj P)) :=
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP Z hZ)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hz, hz⟩
  let E := pbcExtend φ
  let U := pbcRestrict φ
  let c : MonoidalCategory.tensorRight N ≅ E ⋙ U :=
    (completedOrdinaryRestrictionComparison T φ).some.symm
  have he : IsIso (pbcComplexCounit φ P) := by
    have := pbcExtensionCounit_isIso φ P hP
    dsimp only [pbcComplexCounit]
    infer_instance
  let e : (MonoidalCategory.tensorObj (DerivedCategory.Q.obj F) K) ≅
      U.mapDerivedCategory.obj ((pbcDerivedExtend φ).obj K) :=
    MonoidalCategory.tensorIso (Iso.refl _) eP.symm ≪≫
      DerivedCategory.QObjTensorQObjIsoOfKFlatRight F P hk ≪≫
      DerivedCategory.Q.mapIso (β_ F P) ≪≫
      (DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P F hk).symm ≪≫
      MonoidalCategory.tensorIso (Iso.refl _) eF ≪≫
      DerivedCategory.QObjTensorSingleFunctorObjIso P hk N ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex c (.up ℤ)).app P) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).symm.app P) ≪≫
      (U.mapDerivedCategoryFactors.app _).symm ≪≫
      U.mapDerivedCategory.mapIso (asIso (pbcComplexCounit φ P)).symm ≪≫
      U.mapDerivedCategory.mapIso ((pbcDerivedExtend φ).mapIso eP)
  have hU := DerivedCategory.TStructure.t.isGE_of_iso e (-(r : ℤ) + a)
  have hzero (q : ℤ) (hq : q < a - r) :
      IsZero (U.obj ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcDerivedExtend φ).obj K))) := by
    exact (DerivedCategory.isZero_of_isGE _ (-(r : ℤ) + a) q (by omega)).of_iso
      ((U.mapDerivedCategoryHomologyFunctorIso q).app _)
  apply (DerivedCategory.isGE_iff _ _).2
  intro q hq
  let H := (DerivedCategory.homologyFunctor _ q).obj ((pbcDerivedExtend φ).obj K)
  have hz : IsZero ((SheafOfModules.toSheaf _).obj H) :=
    (SheafOfModules.toSheaf ((adicLisseForget T).obj R)).map_isZero (hzero q hq)
  apply (IsZero.iff_id_eq_zero H).2
  apply (SheafOfModules.toSheaf _).map_injective
  simpa using hz.eq_of_src ((SheafOfModules.toSheaf _).map (𝟙 H))
    ((SheafOfModules.toSheaf _).map (0 : H ⟶ H))

private theorem control_local_lower
    {T V : Scheme.{u}} (g : V ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (n : ℕ)
    (F : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (ε : F ⟶ (CochainComplex.singleFunctor _ 0).obj
      (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))) (hε : QuasiIso ε)
    (hf : ∀ q : ℤ, Module.Projective A (F.X q) ∧ Module.Finite A (F.X q))
    (hb : ∀ q : ℤ, q < -(r : ℤ) ∨ 0 < q → IsZero (F.X q))
    (K : DerivedCategory (pbcModules V
      ((adicTowerInverseImage g).obj (pbcAdicCompletion T d))))
    (a : ℤ) [K.IsGE a] :
    ((pbcDerivedExtend ((adicTowerInverseImage g).map (pbcAdicProjection T d n))).obj K).IsGE
      (a - r) := by
  classical
  let : IsNoetherianRing A := d.noetherian
  let c := CompletedConstantReduction.base T d.ideal ≫
    CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite
  let E := completedAdicChange T c
  let G := proEtaleModuleInverseImage g (pbcAdicCompletion T d)
  let H := (adicLisseConstantModules T A ⋙ E) ⋙ G
  have hfin := CompletedConstantReduction.finite_coefficient_identification
    T d.ideal d.quotientFinite
  have hc : IsIso (CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite) :=
    hfin.2.1
  have hh := completed_constant_algebra_flat_quotients T d.ideal _
    (asIso (CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite)) c
    (fun n ↦ by
      dsimp only [c]
      simp only [asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]
      exact (CompletedConstantReduction.base_exists T d.ideal).choose_spec.1 n)
  let : PreservesFiniteLimits E := ((exactFunctor_iff E).1 hh.2.1).1
  let : PreservesFiniteColimits E := ((exactFunctor_iff E).1 hh.2.1).2
  let : PreservesFiniteLimits (adicLisseConstantModules T A) :=
    (CompletedConstantReduction.constant_exact T A).1
  let : PreservesFiniteColimits (adicLisseConstantModules T A) :=
    (CompletedConstantReduction.constant_exact T A).2
  let := CompletedConstantReduction.constant_additive T A
  have : E.Additive := pbcExtend_additive c
  have : PreservesFiniteLimits G :=
    proEtaleModuleInverseImage_preservesFiniteLimits g (pbcAdicCompletion T d)
  let : G.IsLeftAdjoint := (proEtaleModuleInverseImageAdjunction g
    (pbcAdicCompletion T d)).isLeftAdjoint
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  have : H.Additive := inferInstance
  let φ := (adicTowerInverseImage g).map (pbcAdicProjection T d n)
  let R := (adicTowerInverseImage g).obj (pbcAdicCompletion T d)
  let N := (pbcRestrict φ).obj (SheafOfModules.unit
    ((adicLisseForget V).obj ((adicTowerInverseImage g).obj
      ((pbcAdicRings T d).obj (op n)))))
  let eH : H.obj (ModuleCat.of A A) ≅
      SheafOfModules.unit ((adicLisseForget V).obj R) :=
    G.mapIso (CompletedConstantReduction.constantChange_unit T c) ≪≫
      ProEtaleClosedProjection.regularInverseIso g (pbcAdicCompletion T d)
  let rr := CompletedConstantReduction.finiteReduction T d.ideal d.quotientFinite n
  have : IsIso rr := hfin.2.2.1 n
  let eN : H.obj (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1))) ≅ N :=
    G.mapIso (asIso rr) ≪≫
      ProEtaleClosedProjection.coefficientInverseIso g (pbcAdicProjection T d n)
  let P := (H.mapHomologicalComplex (.up ℤ)).obj F
  let ε' : P ⟶ (CochainComplex.singleFunctor _ 0).obj N :=
    (H.mapHomologicalComplex (.up ℤ)).map ε ≫
      (H.mapCochainComplexSingleFunctor 0).hom.app _ ≫
      (CochainComplex.singleFunctor _ 0).map eN.hom
  have : QuasiIso ε := hε
  have : QuasiIso ε' := by dsimp only [ε']; infer_instance
  apply control_extension_bound V φ P r
  · intro q hq
    exact H.map_isZero (hb q hq)
  · intro q
    have := (hf q).1
    have := (hf q).2
    exact control_functor_flat V R H eH (F.X q)
  · exact asIso (DerivedCategory.Q.map ε')

private theorem control_constructible_iso
    (T : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    {F G : pbcModules T (adicLisseConstantRing T B)} (e : F ≅ G)
    (h : IsConstructibleProEtaleCoefficientModuleSheaf T B F) :
    IsConstructibleProEtaleCoefficientModuleSheaf T B G := by
  obtain ⟨S, hn, hc, hs⟩ := h
  refine ⟨S, hn, hc, fun i ↦ ?_⟩
  obtain ⟨V, hV, hv⟩ := hs i
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := hv U f hf
  exact ⟨M, hM, ⟨((SheafOfModules.overFunctor _ U).mapIso
    ((proEtaleModuleInverseImage (S.immersion i) (adicLisseConstantRing T B)).mapIso
      e)).symm ≪≫ eM⟩⟩

private theorem control_of_lower_bound
    (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (hK : PbcHasUniformConstructibleReductions T d K)
    (c : ℤ) (hLower : ∀ n, ((pbcCompletedReduction T d n).obj K).IsGE c) :
    PbcConstructibleReductionControl T d K := by
  classical
  obtain ⟨M, e, ⟨a, b, hab, S, hS⟩, _⟩ := hK
  choose W hW hL using hS
  have hcov := fun i ↦ cover_of_sieve (S.domain i) (W i) (hW i)
  choose I U f hU hf using hcov
  let V (i : Fin S.n) : Cover.{u + 1} proetalePrecoverage (S.domain i) :=
    { I₀ := I i, X := fun j ↦ (U i j).left, f := fun j ↦ (U i j).hom, mem₀ := hU i }
  have hmodels (i : Fin S.n) (j : (V i).I₀) :
      Nonempty (AdicTowerLocalModel d ((V i).f j ≫ S.immersion i) M a b) :=
    hL i (U i j) (f i j) (hf i j)
  let L (i : Fin S.n) (j : (V i).I₀) := Classical.choice (hmodels i j)
  have hb := uniform_upper T d M a b hab S V L
  have hc := uniform_constructible T d M a b S V L
  refine ⟨min c b, b, min_le_right _ _, ?_, ?_⟩
  · intro n q
    exact control_constructible_iso T _
      ((pbcRestrict (pbcLevelConstantComparison T d n).hom).mapIso
        ((DerivedCategory.homologyFunctor _ q).mapIso (e n))) (hc n q)
  · intro n q hq
    rcases hq with hq | hq
    · have := hLower n
      exact DerivedCategory.isZero_of_isGE _ c q (lt_of_lt_of_le hq (min_le_left _ _))
    · have := hb n
      exact (DerivedCategory.isZero_of_isLE (M.level n) b q hq).of_iso
        ((DerivedCategory.homologyFunctor _ q).mapIso (e n)).symm

private theorem control_of_uniform
    (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (hK : PbcHasUniformConstructibleReductions T d K) :
    PbcConstructibleReductionControl T d K := by
  classical
  obtain ⟨r, hr⟩ := control_quotient_models d
  have hK' := hK
  obtain ⟨M, e, ⟨a, b, hab, S, hS⟩, _⟩ := hK
  choose W hW hL using hS
  have hcov := fun i ↦ cover_of_sieve (S.domain i) (W i) (hW i)
  choose I U f hU hf using hcov
  let V (i : Fin S.n) : Cover.{u + 1} proetalePrecoverage (S.domain i) :=
    { I₀ := I i, X := fun j ↦ (U i j).left, f := fun j ↦ (U i j).hom, mem₀ := hU i }
  have hmodels (i : Fin S.n) (j : (V i).I₀) :
      Nonempty (AdicTowerLocalModel d ((V i).f j ≫ S.immersion i) M a b) :=
    hL i (U i j) (f i j) (hf i j)
  let L (i : Fin S.n) (j : (V i).I₀) := Classical.choice (hmodels i j)
  apply control_of_lower_bound T d K hK' (a - r)
  intro n
  obtain ⟨F, ε, hε, hF, hbound⟩ := hr n
  have hm : (M.level n).IsGE (a - r) := by
    apply (DerivedCategory.isGE_iff _ _).2
    intro q hq
    let H := (DerivedCategory.homologyFunctor _ q).obj (M.level n)
    have hz : IsZero ((SheafOfModules.toSheaf _).obj H) := by
      apply proEtale_isZero_of_stratum_cover T S V
      intro i j
      let g := (V i).f j ≫ S.immersion i
      have : (L i j).complex.IsStrictlyGE a :=
        ((L i j).complex.isStrictlyGE_iff _).2
          (fun q hq ↦ (L i j).bounded q (Or.inl hq))
      have hh : (adicTowerLocalReduction d g (L i j).complex n).IsGE (a - r) :=
        control_local_lower g d r n F ε hε hF hbound
          (DerivedCategory.Q.obj (L i j).complex) a
      apply pullback_homology_zero g _ (M.level n) q
      exact (DerivedCategory.isZero_of_isGE _ (a - r) q hq).of_iso
        ((DerivedCategory.homologyFunctor _ q).mapIso ((L i j).identification n))
    apply (IsZero.iff_id_eq_zero H).2
    apply (SheafOfModules.toSheaf _).map_injective
    simpa using hz.eq_of_src ((SheafOfModules.toSheaf _).map (𝟙 H))
      ((SheafOfModules.toSheaf _).map (0 : H ⟶ H))
  exact DerivedCategory.TStructure.t.isGE_of_iso (e n) (a - r)

private theorem control_quotient_orders {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (N : ℕ) (hN : (N : A) ∈ I) (hunit : IsUnit (N : B))
    (n : ℕ) (x : A ⧸ I ^ n) : IsUnit (addOrderOf x : B) := by
  have hz : (N ^ n : ℕ) • x = 0 := by
    have hc : (N ^ n : A ⧸ I ^ n) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (I ^ n)), ← map_pow]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa only [Nat.cast_pow] using Ideal.pow_mem_pow hN n
    simp only [nsmul_eq_mul, Nat.cast_pow, hc, zero_mul]
  exact isUnit_of_dvd_unit
    (Nat.cast_dvd_cast (addOrderOf_dvd_of_nsmul_eq_zero hz))
    (by simpa only [Nat.cast_pow] using hunit.pow n)

private theorem control_field_bound {S T : Scheme.{u}}
    (f : S ⟶ T) [IsProper f] [CompactSpace T] :
    ∃ e : ℕ, ∀ (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ T),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
  obtain ⟨e, he⟩ := exists_fibre_dimension_bound f
  refine ⟨e, fun Ω _ y ↦ ?_⟩
  obtain ⟨⟨t, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω T).symm.surjective y
  calc
    topologicalKrullDim (pullback f (Spec.map a ≫ T.fromSpecResidueField t) : Scheme)
        = topologicalKrullDim
          (pullback (pullback.snd f (T.fromSpecResidueField t)) (Spec.map a) : Scheme) :=
      (IsHomeomorph.topologicalKrullDim_eq _ (pullbackLeftPullbackSndIso f
        (T.fromSpecResidueField t) (Spec.map a)).hom.homeomorph.isHomeomorph).symm
    _ = topologicalKrullDim (f.fiber t) := by
      let : (f.fiber t).Over (Spec (T.residueField t)) := ⟨f.fiberToSpecResidueField t⟩
      let : Algebra (T.residueField t) Ω := a.hom.toAlgebra
      let : LocallyOfFiniteType (f.fiber t ↘ Spec (.of (T.residueField t))) := by
        change LocallyOfFiniteType (pullback.snd f (T.fromSpecResidueField t))
        infer_instance
      let : QuasiCompact (f.fiber t ↘ Spec (.of (T.residueField t))) := by
        change QuasiCompact (pullback.snd f (T.fromSpecResidueField t))
        infer_instance
      exact (topologicalKrullDim_fieldExtension_and_denseOpen
        (K := T.residueField t) (X := f.fiber t)).1 Ω
    _ ≤ (e : WithBot ℕ∞) := he t

private theorem control_push {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (hDimS : ∃ k : ℕ, topologicalKrullDim S ≤ (k : WithBot ℕ∞))
    (hDimT : ∃ k : ℕ, topologicalKrullDim T ≤ (k : WithBot ℕ∞))
    (f : S ⟶ T) [IsProper f] {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (N : ℕ) (hAnn : (N : A ⧸ d.ideal) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) (hT : IsUnit (N : Γ(T, ⊤)))
    (K : d.derived S) (hK : PbcConstructibleReductionControl S d K) :
    PbcConstructibleReductionControl T d ((d.push f).obj K) := by
  obtain ⟨a, b, hab, hc, hb⟩ := hK
  obtain ⟨e, he⟩ := control_field_bound f
  have hmem : (N : A) ∈ d.ideal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_natCast] using hAnn
  have horders (V : Scheme.{u}) (hV : IsUnit (N : Γ(V, ⊤))) (n : ℕ)
      (x : A ⧸ d.ideal ^ (n + 1)) (v : V) :
      IsUnit (addOrderOf x : V.presheaf.stalk v) := by
    apply control_quotient_orders d.ideal N hmem _ (n + 1) x
    simpa only [map_natCast] using hV.map (V.presheaf.germ ⊤ v trivial).hom
  have hfin (n : ℕ) := pbc_finite_directImage_cohomology hDimS hDimT f d n
    (horders S hS n) (horders T hT n) e he a b
    ((pbcCompletedReduction S d n).obj K) (hc n) (hb n)
  refine ⟨a, b + 2 * (e : ℤ), by omega, ?_, ?_⟩
  · intro n q
    exact control_constructible_iso T _
      ((pbcRestrict (pbcLevelConstantComparison T d n).hom).mapIso
        ((DerivedCategory.homologyFunctor _ q).mapIso
          (asIso (d.finiteProjection f K n)).symm)) ((hfin n).1 q)
  · intro n q hq
    exact ((hfin n).2 q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso (asIso (d.finiteProjection f K n)))

private theorem intrinsicComplete_of_iso
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {K L : PbcCompletedDerived T d} (e : K ≅ L)
    (hK : PbcIsIntrinsicallyComplete T d K) : PbcIsIntrinsicallyComplete T d L := by
  obtain ⟨r, f, hf, C, eC, hC⟩ := hK
  refine ⟨r, f, hf, C,
    eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison T d).inv).mapIso e, ?_⟩
  change IsIso (eC.inv ≫ _) at hC
  have hu := (isIso_comp_left_iff eC.inv _).mp hC
  change IsIso ((_ ≫ eC.inv) ≫ _)
  infer_instance

private theorem actualPush_intrinsicComplete
    {S T : Scheme.{u}} (f : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived S d) (hK : PbcIsIntrinsicallyComplete S d K) :
    PbcIsIntrinsicallyComplete T d ((pbcActualDerivedPush f d).obj K) := by
  let P : ObjectProperty (PbcCompletedDerived S d) := PbcIsIntrinsicallyComplete S d
  let Q : ObjectProperty (PbcCompletedDerived T d) := PbcIsIntrinsicallyComplete T d
  let a := Adjunction.ofIsRightAdjoint P.ι
  let b := Adjunction.ofIsRightAdjoint Q.ι
  have : IsIso ((pbcActualCompletionUnit d S).app K) :=
    a.isIso_unit_app_iff_mem_essImage.mpr ⟨⟨K, hK⟩, ⟨Iso.refl _⟩⟩
  have he := (pbcActualDirectCompletionIso_exists f d).exists.choose_spec K
  change (pbcActualCompletionUnit d T).app ((pbcActualDerivedPush f d).obj K) ≫
    (pbcActualDirectCompletionIso f d).hom.app K = _ at he
  have : IsIso ((pbcActualCompletionUnit d T).app
      ((pbcActualDerivedPush f d).obj K) ≫
        (pbcActualDirectCompletionIso f d).hom.app K) := by
    rw [he]
    infer_instance
  have : IsIso ((pbcActualCompletionUnit d T).app
      ((pbcActualDerivedPush f d).obj K)) :=
    IsIso.of_isIso_comp_right _ ((pbcActualDirectCompletionIso f d).hom.app K)
  have : IsIso (b.unit.app ((pbcActualDerivedPush f d).obj K)) := by
    change IsIso ((pbcActualCompletionUnit d T).app ((pbcActualDerivedPush f d).obj K))
    infer_instance
  obtain ⟨L, ⟨e⟩⟩ := b.mem_essImage_of_unit_isIso ((pbcActualDerivedPush f d).obj K)
  exact intrinsicComplete_of_iso T d e L.property

private theorem datumPush_eq_actualPush
    {S T : Scheme.{u}} (f : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    d.push f = pbcActualDerivedPush f d := by
  have hm : proEtaleRingModuleDirectImage f (d.completedRing T) (d.completedRing S)
      (d.integralRingIso f) = completedModuleDirectImage f d := by
    unfold proEtaleRingModuleDirectImage completedModuleDirectImage
    unfold proEtaleRingDirectImageMap completedCoefficientDirectImageMap
    rw [cbcDatumCoefficient_eq]
    rfl
  cases hm
  rfl

private theorem datumPush_intrinsicComplete
    {S T : Scheme.{u}} (f : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived S d) (hK : PbcIsIntrinsicallyComplete S d K) :
    PbcIsIntrinsicallyComplete T d ((d.push f).obj K) := by
  rw [datumPush_eq_actualPush]
  exact actualPush_intrinsicComplete f d K hK


private theorem control_pull {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (g : S ⟶ T) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : d.derived T) (hcomplete : PbcIsIntrinsicallyComplete T d K)
    (hK : PbcConstructibleReductionControl T d K) :
    PbcConstructibleReductionControl S d ((d.completedPull g).obj K) := by
  obtain ⟨a, b, hab, hc, hb⟩ := hK
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let C := DerivedCategory.Q.objPreimage K
  let eC := DerivedCategory.Q.objObjPreimageIso K
  have hC := (d.towerComplete_iff_intrinsic T K).mp
    (pbcIntrinsicComplete_towerComplete d T K hcomplete) r f hf C eC
  have he (n : ℕ) : (pbcCompletedReduction S d n).obj ((d.completedPull g).obj K) ≅
      (completedReductionFiniteTarget g d n).obj K := by
    have := (completedPullback_reduction g d r f hf K C eC hC).2.1 n
    exact (pbcCompletedReduction S d n).mapIso
      ((cbcDatumCompletedTransport d g).app K).symm ≪≫
        asIso (completedPullbackReductionArrow g d K n)
  refine ⟨a, b, hab, ?_, ?_⟩
  · intro n q
    let F := proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
      ((pbcAdicRings S d).obj (op n)) (asIso (completedFiniteCoefficientMap g d n))
    let L := (pbcCompletedReduction T d n).obj K
    have h := pbc_finite_pullback_constructibility g d n
      ((DerivedCategory.homologyFunctor _ q).obj L) (hc n q)
    exact control_constructible_iso S _
      ((pbcRestrict (pbcLevelConstantComparison S d n).hom).mapIso
        ((F.mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
          ((DerivedCategory.homologyFunctor _ q).mapIso (he n)).symm)) h
  · intro n q hq
    let F := proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
      ((pbcAdicRings S d).obj (op n)) (asIso (completedFiniteCoefficientMap g d n))
    exact (F.isZero_homologyFunctor_mapDerivedCategory_obj (hb n q hq)).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso (he n))

/-- The canonical finite reductions of the four operations have
constructible cohomology in one common window.
Source: blueprint main-20261015, prop-weil-pbc-preservation-constructible.proof.md,
steps 1 and 3--5; Stacks 09C7, 099N, 09AL
(blueprint: lem-weil-pbc-completed-constructible-reduction-control).

Proof: take a common local term interval [d0,d1] of the input. Uniform perfect quotient
resolutions in [-r,0], sheafified by the flat constant-to-completed comparison, compute
the reductions locally in [d0-r,d1]. On each stratum its supplied covering detects
vanishing; every geometric point is on a stratum. The retained bounded-below etale
origins and geometric stalk conservativity turn these into global cohomological bounds.
The finite-lisse cohomology of the models gives constructibility.
Apply amplification_of_isProper with N and the fibre bound e, giving AMP(2e).
The perfect projection formula compares its reductions with finite direct image on
cohomology: quotient-linearity follows by locally lifting quotient scalars to the
completed ring and using annihilation to make the lifts irrelevant. Finite amplification
therefore gives constructibility and interval [d0-r,d1+2e]. Completed-pullback reduction
gives quotient-linear reduction comparisons; finite pullback
preserves constructibility and the interval. Apply these facts to K and then Rf_*K,
and repeat direct image for f-prime after pulling back K along g-prime. Transport the
finite-level bounds and constructibility through the quotient-linear comparisons.
No etale origin, normalization, or local model for an output is constructed here.
Zero objects, empty schemes and zero quotients obey the same vanishing containments. -/
theorem AdicCoefficientDatum.constructible_reduction_control
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (hDimX : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (hDimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (hDimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (hDimY' : ∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))
    [IsProper f] [IsProper f']
    (N : ℕ) (hN : 0 < N) (hAnn : (N : A ⧸ d.ideal) = 0)
    (hNX : IsUnit (N : Γ(X, ⊤))) (hNY : IsUnit (N : Γ(Y, ⊤)))
    (hNX' : IsUnit (N : Γ(X', ⊤))) (hNY' : IsUnit (N : Γ(Y', ⊤)))
    (e : ℕ)
    (hFibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (K : d.derived X) (hK : PbcIsBoundedConstructibleComplete X d K) :
    PbcConstructibleReductionControl Y d ((d.push f).obj K) ∧
      PbcConstructibleReductionControl Y' d
        ((d.completedPull g).obj ((d.push f).obj K)) ∧
      PbcConstructibleReductionControl X' d ((d.completedPull g').obj K) ∧
      PbcConstructibleReductionControl Y' d
        ((d.push f').obj ((d.completedPull g').obj K)) := by
  have _ := sq
  have _ := hN
  have _ := hFibres
  have hinput := control_of_uniform X d K hK.2.1
  have hp := control_push hDimX hDimY f d N hAnn hNX hNY K hinput
  have hg := control_pull g d _ (datumPush_intrinsicComplete f d K hK.1) hp
  have hg' := control_pull g' d K hK.1 hinput
  exact ⟨hp, hg, hg', control_push hDimX' hDimY' f' d N hAnn hNX' hNY'
    ((d.completedPull g').obj K) hg'⟩

end AlgebraicGeometry.Scheme
