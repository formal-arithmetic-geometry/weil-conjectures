/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.SmoothPurity.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Algebra.Homology.SmoothPurity.RestrictedScalarCohomologyLocalConstancy
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteTensorConstructibleCohomology
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility

/-! # Finite scalar tools for normalized-tower reconstruction

Source: current blueprint, scalar-extension-functor clause (2); Stacks 06YY and 094H.
These are the finite-coefficient proofs from ScalarExtensionFunctor, isolated from
its rational-stage, Tate-line and integral-tower constructions.
(blueprint: lem-sp-finite-scalar-reconstruction-tools)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify

/-- Canonical finite coefficient extension, with its actual universal derived tensor.
Source: Stacks 06YY (blueprint: lem-sp-finite-scalar-reconstruction-tools). -/
abbrev spFiniteScalarExtension {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    proEtaleDerivedCategory T A ⥤ proEtaleDerivedCategory T B :=
  reductionDerivedChange T (Scheme.proEtaleConstantRingMap (T := T) f)

attribute [local instance] scalarExtensionSmall

private def finiteScalarKFlatIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := proEtaleConstantRing T A) P) :
    (spFiniteScalarExtension f T).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P) := by
  have : IsIso (reductionScalarComplexCounit T
      (proEtaleConstantRingMap (T := T) f) P) := by
    have h := reductionDerivedCounit_isIso T
      (proEtaleConstantRingMap (T := T) f) P hP
    dsimp only [reductionScalarComplexCounit, reductionComplexCounit]
    infer_instance
  exact asIso (reductionScalarComplexCounit T (proEtaleConstantRingMap (T := T) f) P)

section ConstructibilityProof
open MonoidalCategory

attribute [local irreducible] SheafOfModules.monoidalCategory

section AbstractTensor
universe cv cu cw


end AbstractTensor

/-- The Tor test is equivalent to a flat representative on the same interval.
Source: Stacks 06YY (blueprint: lem-sp-finite-scalar-reconstruction-tools). -/
theorem spFiniteScalar_tor_flat_model
    (T : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory T A) (a b : ℤ) (hab : a ≤ b) :
    HasProEtaleTorAmplitude T A K a b ↔
      ∃ P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ,
        (∀ i, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (J := ProEt.topology T) (R := proEtaleConstantRing T A) (P.X i)) ∧
        (∀ i, i < a ∨ b < i → IsZero (P.X i)) ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  classical
  let R := proEtaleConstantRing T A
  let C := proEtaleRingModules T R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have : IsGrothendieckAbelian.{u + 1} C :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (ProEt.topology T) _
  have : ∀ X Y : GradedObject ℤ C, GradedObject.HasTensor X Y := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ C,
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ C,
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := by infer_instance
  have : ∀ X Y Z W : GradedObject ℤ C,
      GradedObject.HasTensor₄ObjExt X Y Z W := by infer_instance
  have : DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (.up ℤ)) := by infer_instance
  have htor : HasProEtaleTorAmplitude T A K a b ↔
      DerivedCategory.torAmplitudeIn C a b K := by
    apply scalarExtension_abstract_tor_iff K a b hab
    intro L
    obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral L
    exact ⟨P, f, hf, hP⟩
  rw [htor, DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat]
  have hflat (M : C) : CategoryTheory.ObjectProperty.flat M ↔
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology T) (R := R) M := by
    refine ⟨fun h ↦ ?_, SheafOfModules.flat_to_cat R M⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R M).symm h.2
  constructor
  · rintro ⟨P, hge, hle, hP, ⟨e⟩⟩
    refine ⟨P, fun i ↦ (hflat _).1 (hP i), ?_, ⟨e.symm⟩⟩
    intro i hi
    rcases hi with hi | hi
    · exact P.isZero_of_isStrictlyGE a i hi
    · exact P.isZero_of_isStrictlyLE b i hi
  · rintro ⟨P, hP, hb, ⟨e⟩⟩
    have hge : P.IsStrictlyGE a :=
      (CochainComplex.isStrictlyGE_iff _ _).2 (fun i hi ↦ hb i (Or.inl hi))
    have hle : P.IsStrictlyLE b :=
      (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi ↦ hb i (Or.inr hi))
    exact ⟨P, hge, hle, fun i ↦ (hflat _).2 (hP i), ⟨e.symm⟩⟩

private theorem scalarExtension_tor
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) (K : proEtaleDerivedCategory T A)
    (a b : ℤ) (hTor : HasProEtaleTorAmplitude T A K a b) :
    HasProEtaleTorAmplitude T B ((spFiniteScalarExtension f T).obj K) a b := by
  classical
  let R := proEtaleConstantRing T A
  let S := proEtaleConstantRing T B
  let φ := proEtaleConstantRingMap (T := T) f
  let E := reductionChange T φ
  obtain ⟨P, hf, hb, ⟨e⟩⟩ := (spFiniteScalar_tor_flat_model T A K a b hTor.1).mp hTor
  have : P.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi ↦ hb i (Or.inr hi))
  have hP := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P b hf
  have hext := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    φ P E (reductionChange_obj_eq T φ) (fun g ↦ reductionChange_map_eq T φ g) hP
      (fun i ↦ (SheafOfModules.flat_to_cat R (P.X i) (hf i)).2)
  let Q := (E.mapHomologicalComplex (.up ℤ)).obj P
  have hQ : ∀ i, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology T) (R := S) (Q.X i) := by
    intro i
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso S (Q.X i)).symm (hext.2 i)
  let c : (spFiniteScalarExtension f T).obj K ≅ DerivedCategory.Q.obj Q :=
    (spFiniteScalarExtension f T).mapIso e ≪≫ finiteScalarKFlatIso f T P hP
  apply (spFiniteScalar_tor_flat_model T B _ a b hTor.1).mpr
  exact ⟨Q, hQ, fun i hi ↦ E.map_isZero (hb i hi), ⟨c⟩⟩

/-- The uniform Tor interval bounds cohomological support.
Source: Stacks 06YY (blueprint: lem-sp-finite-scalar-reconstruction-tools). -/
theorem spFiniteScalar_bounded_of_tor
    (T : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory T A) (a b : ℤ)
    (hTor : HasProEtaleTorAmplitude T A K a b) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)} := by
  classical
  obtain ⟨P, _, hb, ⟨e⟩⟩ := (spFiniteScalar_tor_flat_model T A K a b hTor.1).mp hTor
  apply (Set.finite_Icc a b).subset
  intro i hi
  by_contra hout
  have hor : i < a ∨ b < i := by
    change ¬ (a ≤ i ∧ i ≤ b) at hout
    omega
  have hz := (P.sc i).isZero_homology_of_isZero_X₂ (hb i hor)
  exact hi (hz.of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P))

private theorem scalarExtension_cochainModelIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u}) :
    Nonempty (spFiniteScalarExtension f T ≅
      SheafOfModules.constantCoefficientScalarExtensionOfUniverses.{u + 1, u, u + 1, u + 2, u + 2}
        (ProEt.topology T)
          ((ULift.ringEquiv : ULift.{u + 1, u} B ≃+* B).symm.toRingHom.comp
            (f.comp (ULift.ringEquiv : ULift.{u + 1, u} A ≃+* A).toRingHom))) := by
  let α := proEtaleConstantRingMap (T := T) f
  let D := Classical.choice (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel α)
  let E := reductionChange T α
  let F := reductionDerivedChange T α
  let ε := reductionDerivedCounit T α
  let c := complexCounitNat E F ε
  have : F.IsLeftDerivedFunctor c
      (HomologicalComplex.quasiIso (proEtaleRingModules T (proEtaleConstantRing T A)) (.up ℤ)) :=
    complexCounitNat_kan E F ε
  have : D.T.IsLeftDerivedFunctor D.ε
      (HomologicalComplex.quasiIso (proEtaleRingModules T (proEtaleConstantRing T A)) (.up ℤ)) :=
    D.universal
  let e : E ≅ D.E := NatIso.ofComponents
    (fun M ↦ eqToIso ((reductionChange_obj_eq T α M).trans (D.obj_eq M).symm)) (by
      intro M N g
      dsimp only [eqToIso.hom]
      rw [reductionChange_map_eq, D.map_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans])
  let d := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q
  exact ⟨Functor.leftDerivedNatIso F D.T c D.ε
    (HomologicalComplex.quasiIso (proEtaleRingModules T (proEtaleConstantRing T A)) (.up ℤ)) d⟩

private theorem scalarExtension_constructible
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (K : proEtaleDerivedCategory T A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)) :
    ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T B)) i).obj
          ((spFiniteScalarExtension f T).obj K)) := by
  classical
  let H := fun j : ℤ ↦ (DerivedCategory.homologyFunctor
    (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj K
  obtain ⟨S, hn, hS⟩ := common_stratification hbounded.toFinset T A H
    (fun j _ ↦ hconstructible j)
  have hKb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (H j) := by
    obtain ⟨b, hb⟩ := hbounded.bddAbove
    refine ⟨b, fun j hj ↦ ?_⟩
    by_contra hz
    exact (not_le_of_gt hj) (hb hz)
  have hstratum (i : Fin S.n) (j : ℤ) :
      IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} (S.domain i) A
        (proEtaleConstantModulePullback (S.immersion i) A (H j)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing (S.domain i) A)
          (proEtaleConstantModulePullback (S.immersion i) A (H j))) := by
    by_cases hz : IsZero (H j)
    · have hzero := pullback_isZero (S.immersion i) A (H j) hz
      refine ⟨?_, fun Ω _ _ x ↦ finite_stalk_of_isZero _ A _ hzero x⟩
      obtain ⟨I, U, f, hf, hM⟩ := locallyConstant_of_isZero _ A _ hzero
      exact ⟨I, U, f, hf, fun k ↦ ⟨(hM k).choose, trivial, (hM k).choose_spec⟩⟩
    · obtain ⟨hl, hs⟩ := hS j (hbounded.mem_toFinset.mpr hz) i
      obtain ⟨I, U, f, hf, hM⟩ := hl
      exact ⟨⟨I, U, f, hf, fun k ↦ ⟨(hM k).choose, trivial, (hM k).choose_spec⟩⟩, hs⟩
  intro q
  let D := SheafOfModules.constantCoefficientScalarExtensionOfUniverses.{u + 1, u, u + 1,
    u + 2, u + 2}
    (ProEt.topology T)
      ((ULift.ringEquiv : ULift.{u + 1, u} B ≃+* B).symm.toRingHom.comp
        (f.comp (ULift.ringEquiv : ULift.{u + 1, u} A ≃+* A).toRingHom))
  have hD : IsConstructibleProEtaleModuleSheaf T B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T B)) q).obj (D.obj K)) := by
    refine ⟨S, hn, fun i ↦ ?_⟩
    exact scalarExtension_models_finiteLocal (S.domain i) B _
      (restrictedScalarCohomology_finiteLocalModels (S.immersion i) f K hKb
        (hstratum i) q)
  obtain ⟨e⟩ := scalarExtension_cochainModelIso f T
  exact constructibleProEtale_of_iso T B
    ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T B)) q).mapIso
        (e.symm.app K)) hD

end ConstructibilityProof

attribute [local instance] scalarExtensionSmall

/-- Constructibility, boundedness and the identical Tor interval survive arbitrary
finite coefficient extension, including non-flat maps.
Source: blueprint proof (2), Stacks 094H, 06YY
(blueprint: lem-sp-finite-scalar-reconstruction-tools).
Proof: identify the stated Tor test with the native derived tensor test using the
K-flat tensor/single comparison. The bounded flat-model theorem then represents K by
flat modules supported in the same interval [a,b]. Termwise coefficient extension
preserves flatness and K-flatness, so the same interval works over B. The support of
that representative also bounds cohomology.
For constructibility, refine the finitely many input cohomology stratifications to
one finite stratification. Compare the published scalar functor with the cochain
model by uniqueness of left derived functors. On each stratum,
lem-sp-restricted-scalar-cohomology-local-constancy supplies finite constant B-module
models for its cohomology. Restricting their scalars and the constant-module stalk
comparison give intrinsic constructibility. No flatness of B or Noetherian
hypothesis on T is used. -/
theorem spFiniteScalar_preserves_constructible_tor
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (f : A →+* B) (T : Scheme.{u}) (K : proEtaleDerivedCategory T A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K))
    (a b : ℤ) (hTor : HasProEtaleTorAmplitude T A K a b) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T B)) i).obj
        ((spFiniteScalarExtension f T).obj K))} ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T B)) i).obj
          ((spFiniteScalarExtension f T).obj K))) ∧
    HasProEtaleTorAmplitude T B ((spFiniteScalarExtension f T).obj K) a b := by
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hB
  have ht := scalarExtension_tor f T K a b hTor
  exact ⟨spFiniteScalar_bounded_of_tor T B _ a b ht,
    scalarExtension_constructible f T K hbounded hconstructible, ht⟩


end AlgebraicGeometry.ProEtale
