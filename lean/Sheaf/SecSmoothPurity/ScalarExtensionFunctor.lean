/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.SecSmoothPurity.OpenScalarExchange
public import Sheaf.CategoryTheory.ConstantCoefficientScalarExtension
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Paper.TateTwistLocallyFree
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

import all Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Paper.PurTwistRootLocalModels
import Sheaf.Paper.SignedLineTensorEquivalence
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Sheaf.Paper.FieldStageOrdinaryRealization
import all Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.ScalarExtensionDualLocalIso
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

import all Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison

import Sheaf.Paper.ScalarExtensionDualTowerCore

import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients

import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients

import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

import Sheaf.Paper.RestrictedScalarCohomologyLocalConstancy

import all Sheaf.Paper.FiniteTensorConstructibleCohomology

import all Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated

import all Sheaf.Paper.ProEtaleConstantModuleConstructibility

/-! # Derived scalar extension on the small pro-etale site

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
  sk-def-sp-scalar-extension/sk-def-sp-scalar-extension-functor.md
(blueprint: det-sp-scalar-extension-functor).

The underlying functor is the canonical K-flat derived extension of scalars along a
map of constant coefficient rings.  The accompanying statements record its exactness,
finite constructibility and Tor-amplitude preservation, Tate-line scalar extension,
and the canonical associativity comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Derived extension of scalars on the ordinary constant-ring pro-etale categories.
Source: Stacks Tags 06YY and 06YS; blueprint `det-sp-scalar-extension-functor`.

The functor is computed by a K-flat representative, and the target category carries
its action through the right tensor factor.  Its construction is the published
`scalarExtension`; no second tensor or localization is introduced here.
(blueprint: det-sp-scalar-extension-functor).
-/
noncomputable def scalarExtensionFunctor {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory T A ⥤ Scheme.proEtaleDerivedCategory T B :=
  scalarExtension f T

/-- Exactness of the published derived tensor functor.
Source: Stacks 06YS, 06YY; clause (1) (blueprint: det-sp-scalar-extension-functor).
Proof: resolve by K-flat complexes using lem-pc-kflat-resolution. The ordinary tensor
functor is additive and preserves shifts and mapping cones. Its left derived functor
therefore carries distinguished triangles to distinguished triangles, by
lem-pur-derived-change-of-rings. -/
theorem scalarExtensionFunctor_exact
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u}) :
    ∃ (_ : (scalarExtensionFunctor f T).CommShift ℤ),
      (scalarExtensionFunctor f T).IsTriangulated := by
  exact (reductionDerivedExistence T
    (proEtaleConstantRingMap (T := T) f)).choose_spec.choose_spec.2.1

/-- The actual universal counit on a complex, rather than a chosen model comparison.
Source: Stacks 06YY; clause (1) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctorCounit
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :=
  reductionScalarComplexCounit T (proEtaleConstantRingMap (T := T) f) P

/-- K-flat computation, including the functor and its target-ring tensor action.
Source: Stacks 06YS, 06YY; clause (1) (blueprint: det-sp-scalar-extension-functor).
Proof: the universal counit in lem-pur-derived-change-of-rings is invertible on
K-flat complexes. Its cochain form conjugates by the two canonical quotient
factorizations, hence remains invertible. The ordinary complex is termwise sheafified
extension with B acting on the scalar factor. -/
theorem scalarExtensionFunctor_kflat_representation
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing T A) P) :
    IsIso (scalarExtensionFunctorCounit f T P) := by
  exact scalarCounit_isIso T (proEtaleConstantRingMap (T := T) f) P hP

/-- The canonical formula S_f(Q(P)) ≅ Q(P tensor B), on every K-flat representative.
Source: Stacks 06YY; clause (1) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctorKFlatIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing T A) P) :
    (scalarExtensionFunctor f T).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P) :=
  @asIso _ _ _ _ (scalarExtensionFunctorCounit f T P)
    (scalarExtensionFunctor_kflat_representation f T P hP)

/-- The map of representatives is u tensor id_B, with the same counit comparison.
Source: Stacks 06YY; clause (1) (blueprint: det-sp-scalar-extension-functor).
Proof: apply naturality of the universal derived counit and of the quotient
factorization maps. The selected ordinary tensor functor maps u to id_B tensor u
by the map clause of lem-pur-derived-change-of-rings. -/
theorem scalarExtensionFunctor_map
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    {P Q : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ}
    (v : P ⟶ Q) :
    (scalarExtensionFunctor f T).map (DerivedCategory.Q.map v) ≫
        scalarExtensionFunctorCounit f T Q =
      scalarExtensionFunctorCounit f T P ≫ DerivedCategory.Q.map
        ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).map v) := by
  let E := reductionChange T (proEtaleConstantRingMap (T := T) f)
  let F := scalarExtensionFunctor f T
  let q := HomotopyCategory.quotient
    (proEtaleRingModules T (proEtaleConstantRing T A)) (.up ℤ)
  let j : q ⋙ (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _)
  let ε : DerivedCategory.Q ⋙ F ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv F ≫
      (Functor.associator q DerivedCategory.Qh F).hom ≫
        Functor.whiskerLeft q (reductionDerivedCounit T (proEtaleConstantRingMap (T := T) f)) ≫
          j.hom
  simpa [ε, j, E, F, q, scalarExtensionFunctorCounit,
    reductionScalarComplexCounit, reductionComplexCounit, scalarExtensionFunctor,
    scalarExtension, reductionChangeComplex] using ε.naturality v

section ConstructibilityProof
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
private theorem scalarExtensionSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance] scalarExtensionSmall
open MonoidalCategory

attribute [local irreducible] SheafOfModules.monoidalCategory

section AbstractTensor
universe cv cu cw


private theorem scalarExtension_abstract_tensor_comparison
    {C : Type cu} [CategoryTheory.Category.{cv} C] [Abelian C]
  [IsGrothendieckAbelian.{cv} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [HasDerivedCategory.{cw} C]
  [Abelian.HasFunctorialFlatResolution C]
    (P : CochainComplex C ℤ)
    (hP : ∀ V : CochainComplex C ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V P (curriedTensor C)).Acyclic)
    (K : DerivedCategory C) (e : DerivedCategory.Q.obj P ≅ K) (M : C) :
    Nonempty (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P
      ((HomologicalComplex.single C (.up ℤ) 0).obj M) (curriedTensor C)) ≅
        K ⊗ (DerivedCategory.singleFunctor C 0).obj M) := by
  have hk : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro V hV
    obtain ⟨V, rfl⟩ := V.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hV
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor V P (curriedTensor C))).2 (hP V hV)
    refine ⟨?_, hr⟩
    exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr
  exact ⟨DerivedCategory.Q.mapIso
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P) ≪≫
    (DerivedCategory.QObjTensorSingleFunctorObjIso P hk M).symm ≪≫
      tensorIso e (Iso.refl _)⟩
private theorem scalarExtension_abstract_tor_iff
    {C : Type cu} [CategoryTheory.Category.{cv} C] [Abelian C]
  [IsGrothendieckAbelian.{cv} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [HasDerivedCategory.{cw} C]
  [Abelian.HasFunctorialFlatResolution C]
    (K : DerivedCategory C) (a b : ℤ) (hab : a ≤ b)
    (hRes : ∀ L : CochainComplex C ℤ,
      ∃ (P : CochainComplex C ℤ) (f : P ⟶ L), QuasiIso f ∧
        ∀ V : CochainComplex C ℤ, V.Acyclic →
          (CochainComplex.mapBifunctor V P (curriedTensor C)).Acyclic) :
    (a ≤ b ∧ ∀ (L P : CochainComplex C ℤ), Nonempty (DerivedCategory.Q.obj L ≅ K) →
      ∀ (f : P ⟶ L), QuasiIso f →
        (∀ V : CochainComplex C ℤ, V.Acyclic →
          (CochainComplex.mapBifunctor V P (curriedTensor C)).Acyclic) →
      ∀ (M : C) (i : ℤ), i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor C i).obj
          (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P
            ((HomologicalComplex.single C (.up ℤ) 0).obj M) (curriedTensor C))))) ↔
      DerivedCategory.torAmplitudeIn C a b K := by
  have compare (L P : CochainComplex C ℤ) (eL : DerivedCategory.Q.obj L ≅ K)
      (f : P ⟶ L) (hf : QuasiIso f)
      (hP : ∀ V : CochainComplex C ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V P (curriedTensor C)).Acyclic) (M : C) :
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P
        ((HomologicalComplex.single C (.up ℤ) 0).obj M) (curriedTensor C)) ≅
        K ⊗ (DerivedCategory.singleFunctor C 0).obj M := by
    have : QuasiIso f := hf
    exact (scalarExtension_abstract_tensor_comparison P hP K
      (asIso (DerivedCategory.Q.map f) ≪≫ eL) M).some
  constructor
  · intro h M
    let L := DerivedCategory.Q.objPreimage K
    let eL := DerivedCategory.Q.objObjPreimageIso K
    obtain ⟨P, f, hf, hP⟩ := hRes L
    refine ⟨(DerivedCategory.isGE_iff _ a).2 ?_, (DerivedCategory.isLE_iff _ b).2 ?_⟩
    · intro i hi
      exact (h.2 L P ⟨eL⟩ f hf hP M i (Or.inl hi)).of_iso
        ((DerivedCategory.homologyFunctor C i).mapIso (compare L P eL f hf hP M)).symm
    · intro i hi
      exact (h.2 L P ⟨eL⟩ f hf hP M i (Or.inr hi)).of_iso
        ((DerivedCategory.homologyFunctor C i).mapIso (compare L P eL f hf hP M)).symm
  · intro h
    refine ⟨hab, ?_⟩
    intro L P heL f hf hP M i hi
    obtain ⟨eL⟩ := heL
    apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor C i).mapIso
      (compare L P eL f hf hP M))
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff _ a).1 (h M).1 i hi
    · exact (DerivedCategory.isLE_iff _ b).1 (h M).2 i hi

end AbstractTensor

private theorem scalarExtension_tor_flat_model
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
    HasProEtaleTorAmplitude T B ((scalarExtensionFunctor f T).obj K) a b := by
  classical
  let R := proEtaleConstantRing T A
  let S := proEtaleConstantRing T B
  let φ := proEtaleConstantRingMap (T := T) f
  let E := reductionChange T φ
  obtain ⟨P, hf, hb, ⟨e⟩⟩ := (scalarExtension_tor_flat_model T A K a b hTor.1).mp hTor
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
  have hP' : CochainComplex.IsAcyclicTensorKFlat (R := R) P :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP
  let c : (scalarExtensionFunctor f T).obj K ≅ DerivedCategory.Q.obj Q :=
    (scalarExtensionFunctor f T).mapIso e ≪≫ scalarExtensionFunctorKFlatIso f T P hP'
  apply (scalarExtension_tor_flat_model T B _ a b hTor.1).mpr
  exact ⟨Q, hQ, fun i hi ↦ E.map_isZero (hb i hi), ⟨c⟩⟩

private theorem scalarExtension_bounded_of_tor
    (T : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory T A) (a b : ℤ)
    (hTor : HasProEtaleTorAmplitude T A K a b) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)} := by
  classical
  obtain ⟨P, _, hb, ⟨e⟩⟩ := (scalarExtension_tor_flat_model T A K a b hTor.1).mp hTor
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
    Nonempty (scalarExtensionFunctor f T ≅
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

private theorem scalarExtension_models_finiteLocal
    (S : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    (hL : IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses.{u, u} S A
      (fun M ↦ Finite M) L) :
    IsLocallyConstantProEtaleModuleSheaf S A L ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing S A) L) := by
  classical
  obtain ⟨I, U, f, hf, he⟩ := hL
  let B := ULift.{u + 1} A
  let F := (proEtaleModuleRestriction S A).obj L
  let R := (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing S A)
  have hg : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      proetalePrecoverage S := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hf
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage S at hf
    have hw (i : I) : (f i).left = (U i).hom := by
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 S = (U i).hom at hw
      exact (Category.comp_id _).symm.trans hw
    simpa only [hw] using hf
  apply (finiteLocal_iff S A L).mp
  refine ⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom, hg, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := he i
  let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit S A)
  have ha := proEtaleConstantRingUnit_over_locallyBijective S A (U i)
  have hai : Presheaf.IsLocallyInjective ((ProEt.topology S).over (U i)) a := by
    simpa [a, proEtaleModuleScalarUnit, proEtaleConstantRing] using ha.1
  have has : Presheaf.IsLocallySurjective ((ProEt.topology S).over (U i)) a := by
    simpa [a, proEtaleModuleScalarUnit, proEtaleConstantRing] using ha.2
  let E := ConstantScalarComparison.restriction ((ProEt.topology S).over (U i))
    B (R.over (U i)) a
  have := ConstantScalarComparison.constantComparisonHom_isIso
    ((ProEt.topology S).over (U i)) B (R.over (U i)) a M
  let e : F.over (U i) ≅ (constantSheaf ((ProEt.topology S).over (U i))
      (ModuleCat.{u + 1} B)).obj M :=
    E.mapIso eM ≪≫
      (asIso (ConstantScalarComparison.constantComparisonHom
        ((ProEt.topology S).over (U i)) B (R.over (U i)) a M)).symm
  have : (ProEt.sliceEquiv S (U i)).inverse.IsDenseSubsite
      (ProEt.topology (U i).left) ((ProEt.topology S).over (U i)) :=
    ProEt.sliceDense S (U i)
  let D := (ProEt.sliceEquiv S (U i)).sheafCongr
    ((ProEt.topology S).over (U i)) (ProEt.topology (U i).left) (ModuleCat.{u + 1} B)
  let r : D.functor.obj (F.over (U i)) ≅
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} B) (U i).hom (U i).prop).obj F :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let c := ((ProEt.sliceEquiv S (U i)).constantSheafSheafCongrIso
    ((ProEt.topology S).over (U i)) (ProEt.topology (U i).left)
    (ModuleCat.{u + 1} B) (Over.mkIdTerminal (X := U i))).app M
  exact ⟨M, hM, ⟨
    (ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} B) (U i).hom (U i).prop).app F ≪≫
    r.symm ≪≫ D.functor.mapIso e ≪≫ c⟩⟩

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
          ((scalarExtensionFunctor f T).obj K)) := by
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
  let D := SheafOfModules.constantCoefficientScalarExtensionOfUniverses
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
(blueprint: det-sp-scalar-extension-functor).
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
theorem scalarExtensionFunctor_preserves_constructible_tor
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
        ((scalarExtensionFunctor f T).obj K))} ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T B)) i).obj
          ((scalarExtensionFunctor f T).obj K))) ∧
    HasProEtaleTorAmplitude T B ((scalarExtensionFunctor f T).obj K) a b := by
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hB
  have ht := scalarExtension_tor f T K a b hTor
  exact ⟨scalarExtension_bounded_of_tor T B _ a b ht,
    scalarExtension_constructible f T K hbounded hconstructible, ht⟩

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
/-- A line extends by ordinary tensor and remains locally free of rank one.
Source: blueprint proof (3), Stacks 06YQ
(blueprint: det-sp-scalar-extension-functor).
Proof: trivialize L on a cover. It is flat there and therefore globally flat, so its
degree-zero complex is K-flat by lem-weil-pbc-independent-bounded-flat-kflat.
The derived counit computes its extension by ordinary tensor. On the same cover
ordinary tensor sends the free rank-one module A to B, proving rank one locally. -/
theorem scalarExtensionFunctor_line
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (L : proEtaleRingModules T (proEtaleConstantRing T A))
    (hL : L.IsFiniteLocallyFreeOfRank 1) :
    IsIso (scalarExtensionFunctorCounit f T
      ((HomologicalComplex.single _ (.up ℤ) 0).obj L)) ∧
    SheafOfModules.IsFiniteLocallyFreeOfRank
      ((proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj L) 1 := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let R := proEtaleConstantRing T A
  let S := proEtaleConstantRing T B
  have : L.IsFiniteLocallyFreeOfRank 1 := hL
  let F := SheafOfModules.siteSheafTensorRight (A := R) L
  let G := SheafOfModules.siteSheafTensorRight (A := R)
    (WeilConjectures.coefficientTwistLine T L (-1))
  obtain ⟨e⟩ := (WeilConjectures.signedLineTensor_equivalence T R L 1).2
  obtain ⟨d⟩ := (WeilConjectures.signedLineTensor_equivalence T R L (-1)).2
  let eqv : proEtaleRingModules T R ≌ proEtaleRingModules T R :=
    CategoryTheory.Equivalence.mk F G e.symm (by
      simpa only [F, G, WeilConjectures.coefficientTwistLine,
        WeilConjectures.coefficientTwistPower, neg_neg] using d)
  have : PreservesFiniteLimits F := inferInstanceAs (PreservesFiniteLimits eqv.functor)
  have : PreservesFiniteColimits F := inferInstanceAs (PreservesFiniteColimits eqv.functor)
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let collapse := CochainComplex.map₂HomologicalComplexFlipObjSingleIso
    (MonoidalCategory.curriedTensor (proEtaleRingModules T R)) L ≪≫
      NatIso.mapHomologicalComplex (SheafOfModules.siteSheafTensorRightIso R L).symm (.up ℤ)
  have hk : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := R) ((HomologicalComplex.single _ (.up ℤ) 0).obj L) := by
    intro P hP i
    exact ((hP.map F) i).isZero_homology.of_iso
      (HomologicalComplex.homologyMapIso (collapse.app P) i) |>
        (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
  refine ⟨scalarExtensionFunctor_kflat_representation f T _ hk, ?_⟩
  have : L.IsInvertible := (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one L).2 hL
  have hext := (SheafOfModules.scalarExtensionDual_localIsomorphism.{u + 1, u, u + 1}
    R S (proEtaleConstantRingMap (T := T) f) L).1
  have : ((proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj L).IsInvertible := by
    rw [proEtaleRingExtension_obj]
    exact hext
  exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
    ((proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj L)).1 inferInstance

/-- The rank-one derived computation as an explicit isomorphism to ordinary scalar tensor.
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctorLineIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (L : proEtaleRingModules T (proEtaleConstantRing T A))
    (hL : L.IsFiniteLocallyFreeOfRank 1) :
    (scalarExtensionFunctor f T).obj ((DerivedCategory.singleFunctor _ 0).obj L) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj L) :=
  @asIso _ _ _ _
      (scalarExtensionFunctorCounit f T ((HomologicalComplex.single _ (.up ℤ) 0).obj L))
      (scalarExtensionFunctor_line f T L hL).1 ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)) (.up ℤ) 0).app L)

/-- The finite signed Tate line, using the dependency's roots, powers, unit and duals.
The index n denotes the positive exponent m=n+1. The quotient map a is unique.
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
abbrev scalarExtensionTateLine (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type u) [CommRing A] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ) :=
  WeilConjectures.coefficientTwistLine T (R := proEtaleConstantRing T A)
    (tateFiniteLine T ℓ (ULift.{u + 1, u} A) n (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a)) r

/-- Semilinear maps between the signed finite Tate lines, before scalar extension.
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
abbrev ScalarExtensionTateMaps
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :=
  ∀ r : ℤ, scalarExtensionTateLine T ℓ A n a r ⟶
    (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) f)).obj
      (scalarExtensionTateLine T ℓ B n (f.comp a) r)

/-- Root tensors determine degree one; the coefficient map determines degree zero;
positive powers and negative duals are normalized by tensoring and evaluation.
The degree-one root equation uses HEq only to retain the two existing presentations
of that same degree-one line, without unfolding module sheafification during elaboration.
Source: blueprint proof (3) (blueprint: det-sp-scalar-extension-functor). -/
def IsCanonicalScalarExtensionTateMaps
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (c : ScalarExtensionTateMaps f T ℓ n a) : Prop :=
  (∀ (U : T.ProEtᵒᵖ) (s : (proEtaleConstantRing T A).obj.obj U),
    (c 0).val.app U s = (proEtaleConstantRingMap (T := T) f).hom.app U s) ∧
  (∀ (V : T.ProEt) (s : (proEtaleConstantRing T A).obj.obj (Opposite.op V))
      (x : (proEtaleRootsOfUnitySheaf T (ℓ ^ (n + 1))).obj.obj (Opposite.op V))
      (y : (scalarExtensionTateLine T ℓ A n a 1).val.obj (Opposite.op V)),
    HEq y (tateFiniteTensor T ℓ (ULift.{u + 1, u} A) n
      (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a) V s x) →
    HEq ((c 1).val.app (Opposite.op V) y)
      (tateFiniteTensor T ℓ (ULift.{u + 1, u} B) n
        (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp (f.comp a)) V
        ((proEtaleConstantRingMap (T := T) f).hom.app (Opposite.op V) s) x)) ∧
  (∀ (k : ℕ) (U : T.ProEtᵒᵖ)
      (x : (scalarExtensionTateLine T ℓ A n a (Int.ofNat (k + 1))).val.obj U)
      (y : (scalarExtensionTateLine T ℓ A n a 1).val.obj U),
    (c (Int.ofNat (k + 2))).val.app U
        (SheafOfModules.siteSheafTensorTmul (A := proEtaleConstantRing T A) _ _ U x y) =
      SheafOfModules.siteSheafTensorTmul (A := proEtaleConstantRing T B) _ _ U
        ((c (Int.ofNat (k + 1))).val.app U x) ((c 1).val.app U y)) ∧
  ∀ (k : ℕ) (U : T.ProEtᵒᵖ)
      (d : (scalarExtensionTateLine T ℓ A n a (Int.negSucc k)).val.obj U)
      (x : (scalarExtensionTateLine T ℓ A n a (Int.ofNat (k + 1))).val.obj U),
    (((c (Int.negSucc k)).val.app U d).app (Opposite.op (Over.mk (𝟙 U.unop))))
        ((c (Int.ofNat (k + 1))).val.app U x) =
      (proEtaleConstantRingMap (T := T) f).hom.app U
        ((d.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)

private theorem scalarExtensionTateLine_rank
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (A : Type u) [CommRing A] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ) :
    (scalarExtensionTateLine T ℓ A n a r).IsFiniteLocallyFreeOfRank 1 := by
  let R := purTwistFiniteRing T ℓ n
  let S := tateFiniteCoefficient T (ULift.{u + 1, u} A)
  let a' := ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a
  let L := purTwistRootsModule T ℓ n
  have hL : L.IsFiniteLocallyFreeOfRank 1 := by
    obtain ⟨I, U, q, hq, _, he⟩ := ((purTwistRootLocalModels T ℓ).1 n).1
    exact rank_one_of_cover L ⟨I, U, q, hq, he⟩
  have : L.IsInvertible :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one L).2 hL
  have hline := (SheafOfModules.scalarExtensionDual_localIsomorphism.{u + 1, u, u + 1}
    R S (tateFiniteScalar T ℓ (ULift.{u + 1, u} A) n a') L).1
  have : (tateFiniteLine T ℓ (ULift.{u + 1, u} A) n a').IsFiniteLocallyFreeOfRank 1 :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
      (tateFiniteLine T ℓ (ULift.{u + 1, u} A) n a')).1 hline
  exact (WeilConjectures.signedLineTensor_equivalence T S
    (tateFiniteLine T ℓ (ULift.{u + 1, u} A) n a') r).1

section TateComparisonProof
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
private theorem scalarTateSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance] scalarTateSmall

open scoped ChangeOfRings in
private theorem scalarExtension_purSection
    (T : Scheme.{u}) (R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (α : R ⟶ S) (M : proEtaleRingModules T R) (V : T.ProEt)
    (s : S.obj.obj (Opposite.op V)) (x : M.val.obj (Opposite.op V)) :
    SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        α M (Opposite.op V) s x = purScalarSection (X := T) R S α M V s x := by
  have h :=
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app.{u + 1, u, u + 1, u + 1}
    (J := ProEt.topology T) (R := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
    (α := 𝟙 (((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj))
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α M)
  exact congrArg (fun z ↦ z.app (Opposite.op V)
    (s ⊗ₜ[R.obj.obj (Opposite.op V), (α.hom.app (Opposite.op V)).hom] x)) h

private def scalarExtension_ordinaryIso
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : proEtaleRingModules T R) :
    (proEtaleRingExtension φ).obj M ≅
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} φ M :=
  eqToIso (proEtaleRingExtension_obj φ M) ≪≫
    SheafOfModules.ScalarHomOrdinary.extensionIso φ M

open scoped ChangeOfRings in
private theorem scalarExtension_ordinaryIso_one
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : proEtaleRingModules T R) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    (scalarExtension_ordinaryIso T φ M).hom.val.app V
        (reductionTensorSection T φ M V 1 x) =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} φ M V 1 x := by
  dsimp only [scalarExtension_ordinaryIso, Iso.trans_hom]
  have h := SheafOfModules.ScalarHomOrdinary.extensionIso_unit φ M V x
  convert h using 1
  dsimp only [reductionTensorSection, completedAdicChangeTensor]
  change (SheafOfModules.ScalarHomOrdinary.extensionIso φ M).hom.val.app V
    ((eqToHom (proEtaleRingExtension_obj φ M)).val.app V
      ((eqToHom (proEtaleRingExtension_obj φ M).symm).val.app V _)) = _
  have hh := congrArg (fun z ↦ z.val.app V
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app V
        ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)))
    (eqToHom_trans (proEtaleRingExtension_obj φ M).symm (proEtaleRingExtension_obj φ M))
  exact congrArg (fun z ↦ (SheafOfModules.ScalarHomOrdinary.extensionIso φ M).hom.val.app V z)
    hh

private theorem scalarExtension_ordinaryIso_tmul
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : proEtaleRingModules T R) (V : T.ProEtᵒᵖ)
    (s : S.obj.obj V) (x : M.val.obj V) :
    (scalarExtension_ordinaryIso T φ M).hom.val.app V
        (reductionTensorSection T φ M V s x) =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} φ M V s x := by
  have h := tensorSection_smul T φ M V s 1 x
  rw [mul_one] at h
  rw [← h, map_smul, scalarExtension_ordinaryIso_one]
  simpa only [mul_one] using
    SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1} φ M V s 1 x

private theorem scalarExtension_ordinaryIso_inv_tmul
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : proEtaleRingModules T R) (V : T.ProEtᵒᵖ)
    (s : S.obj.obj V) (x : M.val.obj V) :
    (scalarExtension_ordinaryIso T φ M).inv.val.app V
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} φ M V s x) =
        reductionTensorSection T φ M V s x := by
  have h := congrArg (fun y ↦ (scalarExtension_ordinaryIso T φ M).inv.val.app V y)
    (scalarExtension_ordinaryIso_tmul T φ M V s x)
  have hh := congrArg (fun z : (proEtaleRingExtension φ).obj M ⟶ (proEtaleRingExtension φ).obj M ↦
    z.val.app V (reductionTensorSection T φ M V s x)) (scalarExtension_ordinaryIso T φ M).hom_inv_id
  change (scalarExtension_ordinaryIso T φ M).inv.val.app V
    ((scalarExtension_ordinaryIso T φ M).hom.val.app V
      (reductionTensorSection T φ M V s x)) = reductionTensorSection T φ M V s x at hh
  exact h.symm.trans hh

private theorem scalarExtension_semilinear_dual_ext
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (α : R ⟶ S) (M P : proEtaleRingModules T R) (Q : proEtaleRingModules T S)
    (e : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α P ≅ Q)
    (c d : M ⟶ (proEtaleRingRestrictScalars α).obj
      ((SheafOfModules.homFunctor (R := S)).obj (Opposite.op Q) |>.obj
        (SheafOfModules.unit _)))
    (h : ∀ (U : T.ProEtᵒᵖ) (φ : M.val.obj U) (x : P.val.obj U),
      ((c.val.app U φ).app (Opposite.op (Over.mk (𝟙 U.unop))))
          (e.hom.val.app U (SheafOfModules.scalarExtensionSection α P U 1 x)) =
        ((d.val.app U φ).app (Opposite.op (Over.mk (𝟙 U.unop))))
          (e.hom.val.app U (SheafOfModules.scalarExtensionSection α P U 1 x))) :
    c = d := by
  let H := (SheafOfModules.homFunctor (R := S)).obj (Opposite.op Q) |>.obj
    (SheafOfModules.unit _)
  let F := SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1} α M H c
  let G := SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1} α M H d
  let j := ((SheafOfModules.homFunctor (R := S)).mapIso e.op).app
    (SheafOfModules.unit _)
  have hFG : F = G := by
    apply (cancel_mono j.hom).1
    apply SheafOfModules.scalarExtensionDual_hom_ext.{u + 1, u, u + 1} α M P
    intro U s t φ x
    change ((F.val.app U (SheafOfModules.scalarExtensionSection α M U s φ)).app
        (Opposite.op (Over.mk (𝟙 U.unop))))
          (e.hom.val.app U (SheafOfModules.scalarExtensionSection α P U t x)) =
      ((G.val.app U (SheafOfModules.scalarExtensionSection α M U s φ)).app
        (Opposite.op (Over.mk (𝟙 U.unop))))
          (e.hom.val.app U (SheafOfModules.scalarExtensionSection α P U t x))
    dsimp only [F, G]
    rw [SheafOfModules.scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1},
      SheafOfModules.scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1}]
    have ht : e.hom.val.app U (SheafOfModules.scalarExtensionSection α P U t x) =
        t • e.hom.val.app U (SheafOfModules.scalarExtensionSection α P U 1 x) := by
      have hs := SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}
        α P U t 1 x
      rw [mul_one] at hs
      rw [← hs, map_smul]
    rw [ht]
    change S.obj.map (𝟙 U.unop).op s •
      (c.val.app U φ).app (Opposite.op (Over.mk (𝟙 U.unop)))
        (t • e.hom.val.app U (SheafOfModules.scalarExtensionSection α P U 1 x)) =
      S.obj.map (𝟙 U.unop).op s •
      (d.val.app U φ).app (Opposite.op (Over.mk (𝟙 U.unop)))
        (t • e.hom.val.app U (SheafOfModules.scalarExtensionSection α P U 1 x))
    rw [map_smul, map_smul, h U φ x]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  have hh := congrArg (fun z : _ ⟶ H ↦ z.val.app U
    (SheafOfModules.scalarExtensionSection α M U 1 φ)) hFG
  dsimp only [F, G] at hh
  simpa only [SheafOfModules.scalarExtensionLift_tmul, one_smul] using hh

private theorem scalarExtensionTate_degreeOne_unique
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (c d : ScalarExtensionTateMaps f T ℓ n a)
    (hc : IsCanonicalScalarExtensionTateMaps f T ℓ n a c)
    (hd : IsCanonicalScalarExtensionTateMaps f T ℓ n a d) :
    c 1 = d 1 := by
  apply SheafOfModules.scalarExtension_hom_ext.{u + 1, u, u + 1, u + 1}
    (tateFiniteScalar T ℓ (ULift.{u + 1, u} A) n
      (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a))
    (purTwistRootsModule T ℓ n)
  intro U s x
  have hh := eq_of_heq ((hc.2.1 U.unop s x _ (heq_of_eq rfl)).trans
    (hd.2.1 U.unop s x _ (heq_of_eq rfl)).symm)
  have hp := scalarExtension_purSection T (purTwistFiniteRing T ℓ n)
    (proEtaleConstantRing T A)
    (tateFiniteScalar T ℓ (ULift.{u + 1, u} A) n
      (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a)) (purTwistRootsModule T ℓ n)
    U.unop s x
  exact (congrArg (fun z ↦ (c 1).val.app U z) hp).trans
    (hh.trans (congrArg (fun z ↦ (d 1).val.app U z) hp).symm)

private theorem scalarExtensionTate_positive_unique
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (c d : ScalarExtensionTateMaps f T ℓ n a)
    (hc : IsCanonicalScalarExtensionTateMaps f T ℓ n a c)
    (hd : IsCanonicalScalarExtensionTateMaps f T ℓ n a d) :
    ∀ k : ℕ, c (Int.ofNat k) = d (Int.ofNat k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact (hc.1 U s).trans (hd.1 U s).symm
  | one => exact scalarExtensionTate_degreeOne_unique f T ℓ n a c d hc hd
  | more k hprev ih =>
    apply SheafOfModules.scalarTensor_hom_ext.{u + 1, u, u + 1}
      (scalarExtensionTateLine T ℓ A n a (Int.ofNat (k + 1)))
      (scalarExtensionTateLine T ℓ A n a 1)
    intro U x y
    erw [hc.2.2.1, hd.2.2.1, ih]
    have h1 : c 1 = d 1 := by
      have hzero := hprev
      clear hzero
      exact scalarExtensionTate_degreeOne_unique f T ℓ n a c d hc hd
    rw [h1]

private theorem scalarExtensionTate_negative_unique
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (e : ∀ r : ℤ, SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (proEtaleConstantRingMap (T := T) f) (scalarExtensionTateLine T ℓ A n a r) ≅
          scalarExtensionTateLine T ℓ B n (f.comp a) r)
    (c d : ScalarExtensionTateMaps f T ℓ n a)
    (hc : IsCanonicalScalarExtensionTateMaps f T ℓ n a c)
    (hd : IsCanonicalScalarExtensionTateMaps f T ℓ n a d)
    (hpos : ∀ (k : ℕ) (U : T.ProEtᵒᵖ)
      (x : (scalarExtensionTateLine T ℓ A n a (Int.ofNat k)).val.obj U),
      (e (Int.ofNat k)).hom.val.app U
        (SheafOfModules.scalarExtensionSection (proEtaleConstantRingMap (T := T) f)
          _ U 1 x) = (c (Int.ofNat k)).val.app U x)
    (k : ℕ) : c (Int.negSucc k) = d (Int.negSucc k) := by
  let α := proEtaleConstantRingMap (T := T) f
  let P := scalarExtensionTateLine T ℓ A n a (Int.ofNat (k + 1))
  let N := scalarExtensionTateLine T ℓ A n a (Int.negSucc k)
  let Q := scalarExtensionTateLine T ℓ B n (f.comp a) (Int.ofNat (k + 1))
  apply scalarExtension_semilinear_dual_ext T α N P Q (e (.ofNat (k + 1)))
  intro U φ x
  rw [hpos]
  have hp := scalarExtensionTate_positive_unique f T ℓ n a c d hc hd (k + 1)
  have hd' := hd.2.2.2 k U φ x
  rw [← hp] at hd'
  exact (hc.2.2.2 k U φ x).trans hd'.symm

private theorem scalarExtensionTower_pure
    (T : Scheme.{u}) {R S U : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (α : R ⟶ S) (β : S ⟶ U) (γ : R ⟶ U) (h : α ≫ β = γ)
    (M : proEtaleRingModules T R) (V : T.ProEtᵒᵖ)
    (t : U.obj.obj V) (s : S.obj.obj V) (x : M.val.obj V) :
    ((SheafOfModules.scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1} α β M ≪≫
      eqToIso (congrArg (fun z ↦
        SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} z M) h)).hom.val.app V)
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} β
          (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M) V t
          (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α M V s x)) =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        γ M V (t * β.hom.app V s) x := by
  subst γ
  simpa only [Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id,
      SheafOfModules.scalarExtensionTowerIso_hom] using
    SheafOfModules.scalarExtensionTowerForward_tmul.{u + 1, u, u + 1, u + 1}
      α β M V t s x

private theorem scalarExtensionTower_purSection
    (T : Scheme.{u}) {R S U : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (α : R ⟶ S) (β : S ⟶ U) (γ : R ⟶ U) (h : α ≫ β = γ)
    (M : proEtaleRingModules T R) (V : T.ProEt)
    (s : S.obj.obj (Opposite.op V)) (x : M.val.obj (Opposite.op V)) :
    ((SheafOfModules.scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1} α β M ≪≫
      eqToIso (congrArg (fun z ↦
        SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} z M) h)).hom.val.app
          (Opposite.op V))
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} β
          (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M)
          (Opposite.op V) 1 (purScalarSection (X := T) R S α M V s x)) =
      purScalarSection (X := T) R U γ M V (β.hom.app (Opposite.op V) s) x := by
  let b := SheafOfModules.scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1} α β M ≪≫
    eqToIso (congrArg (fun z ↦
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} z M) h)
  have hA := scalarExtension_purSection T R S α M V s x
  have hB := scalarExtension_purSection T R U γ M V (β.hom.app (Opposite.op V) s) x
  have ht := scalarExtensionTower_pure T α β γ h M (Opposite.op V) 1 s x
  have h₁ := congrArg (fun t : U.obj.obj (Opposite.op V) ↦
    SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
      γ M (Opposite.op V) t x) (one_mul (β.hom.app (Opposite.op V) s))
  exact (congrArg (fun z ↦ b.hom.val.app (Opposite.op V)
    (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} β
      (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M)
      (Opposite.op V) 1 z)) hA.symm).trans (ht.trans (h₁.trans hB))

private structure ScalarExtensionComposite
    (T : Scheme.{u}) {R S U : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (α : R ⟶ S) (β : S ⟶ U) (γ : R ⟶ U) (M : proEtaleRingModules T R) where
  iso : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} β
    (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M) ≅
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} γ M
  normalized : ∀ (V : T.ProEt) (s : S.obj.obj (Opposite.op V))
    (x : M.val.obj (Opposite.op V)),
    iso.hom.val.app (Opposite.op V)
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} β
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M)
        (Opposite.op V) 1 (purScalarSection (X := T) R S α M V s x)) =
      purScalarSection (X := T) R U γ M V (β.hom.app (Opposite.op V) s) x

private def scalarExtension_composite
    (T : Scheme.{u}) {R S U : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (α : R ⟶ S) (β : S ⟶ U) (γ : R ⟶ U) (h : α ≫ β = γ)
    (M : proEtaleRingModules T R) : ScalarExtensionComposite T α β γ M := by
  subst γ
  refine ⟨SheafOfModules.scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1} α β M, ?_⟩
  intro V s x
  simpa only [Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id] using
    scalarExtensionTower_purSection T α β (α ≫ β) rfl M V s x

attribute [local irreducible] scalarExtension_composite

-- Keep the tensor and dual APIs abstract during elaboration.
set_option backward.isDefEq.respectTransparency true

private def scalarExtension_tensorSecondIso
    (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M : proEtaleRingModules T R) {L K : proEtaleRingModules T R} (b : L ≅ K) :
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} L).obj M ≅
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} K).obj M where
  hom := SheafOfModules.siteSheafTensorSecondMap.{u + 1, u, u + 1, u + 1} M b.hom
  inv := SheafOfModules.siteSheafTensorSecondMap.{u + 1, u, u + 1, u + 1} M b.inv
  hom_inv_id := by
    apply SheafOfModules.scalarTensor_hom_ext.{u + 1, u, u + 1} M L
    intro U x y
    have h₁ := SheafOfModules.scalarTensor_second_tmul.{u + 1, u, u + 1}
      (R := R) M (P := L) (P' := K) b.hom U x y
    have h₂ := SheafOfModules.scalarTensor_second_tmul.{u + 1, u, u + 1}
      (R := R) M (P := K) (P' := L) b.inv U x (b.hom.val.app U y)
    have h := congrArg (fun z : L ⟶ L ↦ z.val.app U y) b.hom_inv_id
    change b.inv.val.app U (b.hom.val.app U y) = y at h
    exact (congrArg (fun z ↦
      (SheafOfModules.siteSheafTensorSecondMap.{u + 1, u, u + 1, u + 1}
        M b.inv).val.app U z) h₁).trans
      (h₂.trans (congrArg (fun z ↦
        SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} M L U x z) h))
  inv_hom_id := by
    apply SheafOfModules.scalarTensor_hom_ext.{u + 1, u, u + 1} M K
    intro U x y
    have h₁ := SheafOfModules.scalarTensor_second_tmul.{u + 1, u, u + 1}
      (R := R) M (P := K) (P' := L) b.inv U x y
    have h₂ := SheafOfModules.scalarTensor_second_tmul.{u + 1, u, u + 1}
      (R := R) M (P := L) (P' := K) b.hom U x (b.inv.val.app U y)
    have h := congrArg (fun z : K ⟶ K ↦ z.val.app U y) b.inv_hom_id
    change b.hom.val.app U (b.inv.val.app U y) = y at h
    exact (congrArg (fun z ↦
      (SheafOfModules.siteSheafTensorSecondMap.{u + 1, u, u + 1, u + 1}
        M b.hom).val.app U z) h₁).trans
      (h₂.trans (congrArg (fun z ↦
        SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} M K U x z) h))

private def scalarExtension_positiveComparison
    (T : Scheme.{u}) (R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (α : R ⟶ S) (L : proEtaleRingModules T R) (K : proEtaleRingModules T S)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L ≅ K) :
    ∀ k : ℕ, SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      α (WeilConjectures.coefficientTwistPower T L k) ≅
        WeilConjectures.coefficientTwistPower T K k
  | 0 => SheafOfModules.scalarExtensionUnitIso α
  | 1 => b
  | k + 2 => SheafOfModules.scalarTensorBinaryIso α
      (WeilConjectures.coefficientTwistPower T L (k + 1)) L ≪≫
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L)).mapIso
        (scalarExtension_positiveComparison T R S α L K b (k + 1)) ≪≫
    scalarExtension_tensorSecondIso T S
      (WeilConjectures.coefficientTwistPower T K (k + 1)) b

private theorem scalarExtension_positiveComparison_tmul
    (T : Scheme.{u}) (R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (α : R ⟶ S) (L : proEtaleRingModules T R) (K : proEtaleRingModules T S)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L ≅ K)
    (k : ℕ) (U : T.ProEtᵒᵖ) (s : S.obj.obj U)
    (x : (WeilConjectures.coefficientTwistPower T L (k + 1)).val.obj U)
    (y : L.val.obj U) :
    (scalarExtension_positiveComparison T R S α L K b (k + 2)).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        α (WeilConjectures.coefficientTwistPower T L (k + 2)) U s
        (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
          (WeilConjectures.coefficientTwistPower T L (k + 1)) L U x y)) =
    SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (WeilConjectures.coefficientTwistPower T K (k + 1)) K U
        ((scalarExtension_positiveComparison T R S α L K b (k + 1)).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
            α (WeilConjectures.coefficientTwistPower T L (k + 1)) U s x))
        (b.hom.val.app U
          (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U 1 y)) := by
  change (SheafOfModules.siteSheafTensorSecondMap.{u + 1, u, u + 1, u + 1}
    (WeilConjectures.coefficientTwistPower T K (k + 1)) b.hom).val.app U
      (((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L)).map
          (scalarExtension_positiveComparison T R S α L K b (k + 1)).hom).val.app U
            ((SheafOfModules.scalarTensorBinaryForward α
              (WeilConjectures.coefficientTwistPower T L (k + 1)) L).val.app U
                (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
                  α (WeilConjectures.coefficientTwistPower T L (k + 2)) U s
                  (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
                    (WeilConjectures.coefficientTwistPower T L (k + 1)) L U x y)))) = _
  let F := (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
    (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L)).map
      (scalarExtension_positiveComparison T R S α L K b (k + 1)).hom
  let G := SheafOfModules.siteSheafTensorSecondMap.{u + 1, u, u + 1, u + 1}
    (WeilConjectures.coefficientTwistPower T K (k + 1)) b.hom
  have hB := SheafOfModules.scalarTensorBinaryForward_tmul.{u + 1, u, u + 1}
    (R := R) (S := S) α (WeilConjectures.coefficientTwistPower T L (k + 1)) L U s x y
  have hF := SheafOfModules.scalarTensor_first_tmul.{u + 1, u, u + 1} (R := S)
    (N := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      α (WeilConjectures.coefficientTwistPower T L (k + 1)))
    (N' := WeilConjectures.coefficientTwistPower T K (k + 1))
    (scalarExtension_positiveComparison T R S α L K b (k + 1)).hom
    (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L) U
    (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
      α (WeilConjectures.coefficientTwistPower T L (k + 1)) U s x)
    (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U 1 y)
  have hG := SheafOfModules.scalarTensor_second_tmul.{u + 1, u, u + 1} (R := S)
    (P := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L)
    (P' := K) (WeilConjectures.coefficientTwistPower T K (k + 1)) b.hom U
    ((scalarExtension_positiveComparison T R S α L K b (k + 1)).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        α (WeilConjectures.coefficientTwistPower T L (k + 1)) U s x))
    (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U 1 y)
  exact (congrArg (fun z ↦ G.val.app U (F.val.app U z)) hB).trans
    ((congrArg (fun z ↦ G.val.app U z) hF).trans hG)

private def scalarExtension_negativeComparison
    (T : Scheme.{u}) (R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (α : R ⟶ S) (L : proEtaleRingModules T R) (K : proEtaleRingModules T S)
    [L.IsInvertible]
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L ≅ K) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α
      (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R)
        L (SheafOfModules.unit.{u, u + 1, u + 1} _)) ≅
      SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := S)
        K (SheafOfModules.unit.{u, u + 1, u + 1} _) :=
  SheafOfModules.scalarExtensionDualIso.{u + 1, u, u + 1} α L ≪≫
    ((SheafOfModules.homFunctor (R := S)).mapIso b.symm.op).app (SheafOfModules.unit _)

private theorem scalarExtension_negativeComparison_eval
    (T : Scheme.{u}) (R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (α : R ⟶ S) (L : proEtaleRingModules T R) (K : proEtaleRingModules T S)
    [L.IsInvertible]
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L ≅ K)
    (U : T.ProEtᵒᵖ) (s t : S.obj.obj U)
    (d : (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R)
        L (SheafOfModules.unit.{u, u + 1, u + 1} _)).val.obj U)
    (x : L.val.obj U) :
    (((scalarExtension_negativeComparison T R S α L K b).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        α (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R)
        L (SheafOfModules.unit.{u, u + 1, u + 1} _)) U s d)).app
          (Opposite.op (Over.mk (𝟙 U.unop))))
      (b.hom.val.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U t x)) =
      s * t * α.hom.app U (d.app (Opposite.op (Over.mk (𝟙 U.unop))) x) := by
  change (((SheafOfModules.scalarExtensionDualMap α L).val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        α (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R)
        L (SheafOfModules.unit.{u, u + 1, u + 1} _)) U s d)).app
          (Opposite.op (Over.mk (𝟙 U.unop))))
    (b.inv.val.app U (b.hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U t x))) = _
  have hi := congrArg (fun z :
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L ⟶
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L ↦ z.val.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U t x))
    b.hom_inv_id
  change b.inv.val.app U (b.hom.val.app U
    (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U t x)) = _ at hi
  let D := (SheafOfModules.scalarExtensionDualMap α L).val.app U
    (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
      α (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R)
        L (SheafOfModules.unit.{u, u + 1, u + 1} _)) U s d)
  exact (congrArg (fun z :
      (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L).val.obj U ↦
      D.app (Opposite.op (Over.mk (𝟙 U.unop))) z) hi).trans
    (SheafOfModules.scalarExtensionDualMap_tmul.{u + 1, u, u + 1} α L U s t d x)

private def scalarExtension_signedComparison
    (T : Scheme.{u}) (R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (α : R ⟶ S) (L : proEtaleRingModules T R) (K : proEtaleRingModules T S)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L ≅ K)
    (hL : ∀ k : ℕ, (WeilConjectures.coefficientTwistPower T L (k + 1)).IsInvertible) :
    ∀ r : ℤ, SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      α (WeilConjectures.coefficientTwistLine T L r) ≅
        WeilConjectures.coefficientTwistLine T K r
  | .ofNat k => scalarExtension_positiveComparison T R S α L K b k
  | .negSucc k => by
    letI := hL k
    exact scalarExtension_negativeComparison T R S α
      (WeilConjectures.coefficientTwistPower T L (k + 1))
      (WeilConjectures.coefficientTwistPower T K (k + 1))
      (scalarExtension_positiveComparison T R S α L K b (k + 1))

section SignedComparisonEvaluation
attribute [local irreducible] scalarExtension_positiveComparison

private theorem scalarExtension_signedComparison_eval
    (T : Scheme.{u}) (R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (α : R ⟶ S) (L : proEtaleRingModules T R) (K : proEtaleRingModules T S)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L ≅ K)
    (hL : ∀ k : ℕ, (WeilConjectures.coefficientTwistPower T L (k + 1)).IsInvertible)
    (k : ℕ) (U : T.ProEtᵒᵖ) (s t : S.obj.obj U)
    (d : (WeilConjectures.coefficientTwistLine T L (.negSucc k)).val.obj U)
    (x : (WeilConjectures.coefficientTwistPower T L (k + 1)).val.obj U) :
    (((scalarExtension_signedComparison T R S α L K b hL (.negSucc k)).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        α (WeilConjectures.coefficientTwistLine T L (.negSucc k)) U s d)).app
          (Opposite.op (Over.mk (𝟙 U.unop))))
      ((scalarExtension_positiveComparison T R S α L K b (k + 1)).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          α (WeilConjectures.coefficientTwistPower T L (k + 1)) U t x)) =
      s * t * α.hom.app U (d.app (Opposite.op (Over.mk (𝟙 U.unop))) x) := by
  let _ := hL k
  exact scalarExtension_negativeComparison_eval T R S α
    (WeilConjectures.coefficientTwistPower T L (k + 1))
    (WeilConjectures.coefficientTwistPower T K (k + 1))
    (scalarExtension_positiveComparison T R S α L K b (k + 1)) U s t d x

end SignedComparisonEvaluation

set_option backward.isDefEq.respectTransparency false in
private theorem scalarExtensionTate_degreeOne_scalar_comp
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :
    tateFiniteScalar T ℓ (ULift.{u + 1, u} A) n
      (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a) ≫
        proEtaleConstantRingMap (T := T) f =
      tateFiniteScalar T ℓ (ULift.{u + 1, u} B) n
        (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp (f.comp a)) := by
  dsimp only [tateFiniteScalar, proEtaleConstantRingMap]
  rw [← CategoryTheory.Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem scalarExtensionTate_degreeOne_exists
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :
    ∃ b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (proEtaleConstantRingMap (T := T) f) (scalarExtensionTateLine T ℓ A n a 1) ≅
        scalarExtensionTateLine T ℓ B n (f.comp a) 1,
    ∀ (V : T.ProEt)
      (s : (proEtaleConstantRing T A).obj.obj (Opposite.op V))
      (x : (proEtaleRootsOfUnitySheaf T (ℓ ^ (n + 1))).obj.obj (Opposite.op V))
      (y : (scalarExtensionTateLine T ℓ A n a 1).val.obj (Opposite.op V)),
      HEq y (tateFiniteTensor T ℓ (ULift.{u + 1, u} A) n
        (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a) V s x) →
      HEq (b.hom.val.app (Opposite.op V)
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := T) f)
          (scalarExtensionTateLine T ℓ A n a 1) (Opposite.op V) 1 y))
        (tateFiniteTensor T ℓ (ULift.{u + 1, u} B) n
          (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp (f.comp a)) V
          ((proEtaleConstantRingMap (T := T) f).hom.app (Opposite.op V) s) x) := by
  dsimp only [scalarExtensionTateLine, WeilConjectures.coefficientTwistLine,
    WeilConjectures.coefficientTwistPower]
  let α := tateFiniteScalar T ℓ (ULift.{u + 1, u} A) n
    (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a)
  let β := proEtaleConstantRingMap (T := T) f
  let γ := tateFiniteScalar T ℓ (ULift.{u + 1, u} B) n
    (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp (f.comp a))
  let h := scalarExtensionTate_degreeOne_scalar_comp f T ℓ n a
  let c := scalarExtension_composite T α β γ h (purTwistRootsModule T ℓ n)
  refine ⟨c.iso, ?_⟩
  intro V s x y hy
  have hy' := eq_of_heq hy
  subst y
  exact heq_of_eq (c.normalized V s x)

set_option backward.isDefEq.respectTransparency false in
private theorem scalarExtensionTate_comparisons_of_degreeOne
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (proEtaleConstantRingMap (T := T) f) (scalarExtensionTateLine T ℓ A n a 1) ≅
        scalarExtensionTateLine T ℓ B n (f.comp a) 1)
    (hb : ∀ (V : T.ProEt)
      (s : (proEtaleConstantRing T A).obj.obj (Opposite.op V))
      (x : (proEtaleRootsOfUnitySheaf T (ℓ ^ (n + 1))).obj.obj (Opposite.op V))
      (y : (scalarExtensionTateLine T ℓ A n a 1).val.obj (Opposite.op V)),
      HEq y (tateFiniteTensor T ℓ (ULift.{u + 1, u} A) n
        (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a) V s x) →
      HEq (b.hom.val.app (Opposite.op V)
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := T) f)
          (scalarExtensionTateLine T ℓ A n a 1) (Opposite.op V) 1 y))
        (tateFiniteTensor T ℓ (ULift.{u + 1, u} B) n
          (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp (f.comp a)) V
          ((proEtaleConstantRingMap (T := T) f).hom.app (Opposite.op V) s) x)) :
    ∃ e : ∀ r : ℤ, SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (proEtaleConstantRingMap (T := T) f) (scalarExtensionTateLine T ℓ A n a r) ≅
          scalarExtensionTateLine T ℓ B n (f.comp a) r,
      IsCanonicalScalarExtensionTateMaps f T ℓ n a
        (fun r ↦ SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := T) f) _ ≫
          (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) f)).map (e r).hom) := by
  classical
  let R := proEtaleConstantRing T A
  let S := proEtaleConstantRing T B
  let α := proEtaleConstantRingMap (T := T) f
  let L := scalarExtensionTateLine T ℓ A n a 1
  let K := scalarExtensionTateLine T ℓ B n (f.comp a) 1
  have hL : ∀ k : ℕ, (WeilConjectures.coefficientTwistPower T L (k + 1)).IsInvertible := by
    intro k
    have hr : (WeilConjectures.coefficientTwistPower T L (k + 1)).IsFiniteLocallyFreeOfRank 1 :=
      scalarExtensionTateLine_rank T ℓ A n a (.ofNat (k + 1))
    exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one.{u + 1, u, u + 1}
      (WeilConjectures.coefficientTwistPower T L (k + 1))).2 hr
  let e := scalarExtension_signedComparison T R S α L K b hL
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro U s
    change (SheafOfModules.scalarExtensionUnitIso α).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        α (scalarExtensionTateLine T ℓ A n a 0) U 1 s) = _
    exact (SheafOfModules.scalarExtensionUnitIso_tmul.{u + 1, u, u + 1}
      α U 1 s).trans (one_mul (α.hom.app U s))
  · intro V s x y hy
    change HEq (b.hom.val.app (Opposite.op V)
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        α L (Opposite.op V) 1 y)) _
    exact hb V s x y hy
  · intro k U x y
    exact scalarExtension_positiveComparison_tmul T R S α L K b k U 1 x y
  · intro k U d x
    exact (scalarExtension_signedComparison_eval T R S α L K b hL k U 1 1 d x).trans
      (by simp only [one_mul]; rfl)

private theorem scalarExtensionTate_comparisons
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :
    ∃ e : ∀ r : ℤ, SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (proEtaleConstantRingMap (T := T) f) (scalarExtensionTateLine T ℓ A n a r) ≅
          scalarExtensionTateLine T ℓ B n (f.comp a) r,
      IsCanonicalScalarExtensionTateMaps f T ℓ n a
        (fun r ↦ SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := T) f) _ ≫
          (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) f)).map
            (e r).hom) := by
  obtain ⟨b, hb⟩ := scalarExtensionTate_degreeOne_exists f T ℓ n a
  exact scalarExtensionTate_comparisons_of_degreeOne f T ℓ n a b hb

end TateComparisonProof

/-- There is exactly one semilinear family with the root, unit, power and dual formulas.
Source: blueprint proof (3), Stacks 03EK, 03EM
(blueprint: det-sp-scalar-extension-functor).
Proof: the normalized scalar-extension tower gives the degree-one comparison on
root tensors, and the unit comparison gives degree zero. Construct positive powers
recursively with the proved binary tensor comparison and tensor maps. Every positive
power is invertible by the root-line local models. Its proved dual comparison,
followed by precomposition with the inverse positive comparison, gives the negative
map and the evaluation formula. Restrict these linear comparisons along the scalar
embedding. Root-tensor generation and induction give positive uniqueness; evaluation
on the surjective positive comparison gives negative uniqueness. -/
theorem scalarExtensionTateMaps_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :
    ∃! c : ScalarExtensionTateMaps f T ℓ n a,
      IsCanonicalScalarExtensionTateMaps f T ℓ n a c := by
  classical
  let α := proEtaleConstantRingMap (T := T) f
  obtain ⟨e, he⟩ := scalarExtensionTate_comparisons f T ℓ n a
  let c : ScalarExtensionTateMaps f T ℓ n a := fun r ↦
    SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α _ ≫
      (proEtaleRingRestrictScalars α).map (e r).hom
  refine ⟨c, he, ?_⟩
  intro d hd
  funext r
  cases r with
  | ofNat k => exact scalarExtensionTate_positive_unique f T ℓ n a d c hd he k
  | negSucc k =>
    exact (scalarExtensionTate_negative_unique f T ℓ n a e c d he hd
      (fun k U x ↦ rfl) k).symm

/-- The finite Tate scalar maps, fixed uniquely in every signed degree.
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionTateMaps
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) : ScalarExtensionTateMaps f T ℓ n a :=
  (scalarExtensionTateMaps_existsUnique f T ℓ n a).exists.choose

/-- The signed Tate base-change isomorphism is uniquely fixed on scalar tensor sections.
Source: blueprint proof (3) (blueprint: det-sp-scalar-extension-functor).
Proof: compose the proved ordinary-to-explicit scalar-extension isomorphism with
the signed comparison constructed above. Its value on b tensor x is b times the
normalized semilinear map, by the pure-section formula and linearity. Uniqueness of
the semilinear family identifies that map with scalarExtensionTateMaps. The ordinary
sheafification unit and tensor generation give uniqueness of the isomorphism. -/
theorem scalarExtensionTateIso_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ) :
    ∃! e : (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj
        (scalarExtensionTateLine T ℓ A n a r) ≅
          scalarExtensionTateLine T ℓ B n (f.comp a) r,
      ∀ (U : T.ProEtᵒᵖ) (b : (proEtaleConstantRing T B).obj.obj U)
        (x : (scalarExtensionTateLine T ℓ A n a r).val.obj U),
        e.hom.val.app U
            (reductionTensorSection T (proEtaleConstantRingMap (T := T) f) _ U b x) =
          b • (@id ((scalarExtensionTateLine T ℓ B n (f.comp a) r).val.obj U)
            ((scalarExtensionTateMaps f T ℓ n a r).val.app U x)) := by
  classical
  let α := proEtaleConstantRingMap (T := T) f
  obtain ⟨e, he⟩ := scalarExtensionTate_comparisons f T ℓ n a
  let c : ScalarExtensionTateMaps f T ℓ n a := fun r ↦
    SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α _ ≫
      (proEtaleRingRestrictScalars α).map (e r).hom
  have hc : c = scalarExtensionTateMaps f T ℓ n a :=
    (scalarExtensionTateMaps_existsUnique f T ℓ n a).unique he
      (scalarExtensionTateMaps_existsUnique f T ℓ n a).exists.choose_spec
  let d := scalarExtension_ordinaryIso T α (scalarExtensionTateLine T ℓ A n a r) ≪≫ e r
  have hd : ∀ (U : T.ProEtᵒᵖ) (b : (proEtaleConstantRing T B).obj.obj U)
      (x : (scalarExtensionTateLine T ℓ A n a r).val.obj U),
      d.hom.val.app U (reductionTensorSection T α _ U b x) =
        b • (show (scalarExtensionTateLine T ℓ B n (f.comp a) r).val.obj U from
          (scalarExtensionTateMaps f T ℓ n a r).val.app U x) := by
    intro U b x
    change (e r).hom.val.app U
      ((scalarExtension_ordinaryIso T α _).hom.val.app U
        (reductionTensorSection T α _ U b x)) = _
    rw [scalarExtension_ordinaryIso_tmul]
    have hs := SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}
      α (scalarExtensionTateLine T ℓ A n a r) U b 1 x
    rw [mul_one] at hs
    rw [← hs, map_smul]
    change b • (show (scalarExtensionTateLine T ℓ B n (f.comp a) r).val.obj U from
      (c r).val.app U x) = _
    rw [hc]
  refine ⟨d, hd, ?_⟩
  intro q hq
  apply Iso.ext
  apply (SheafOfModules.toSheaf _).map_injective
  apply reductionTensor_hom_ext T α _
  intro U b x
  exact (hq U b x).trans (hd U b x).symm

/-- The ordinary canonical comparison (A_T(r)) tensor B_T ≅ B_T(r).
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionTateIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ) :
    (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj
        (scalarExtensionTateLine T ℓ A n a r) ≅
      scalarExtensionTateLine T ℓ B n (f.comp a) r :=
  (scalarExtensionTateIso_existsUnique f T ℓ n a r).exists.choose

/-- The Tate comparison computes derived extension in every signed degree and the
finite twists are rank-one locally free.
Source: blueprint proof (3), Stacks 06YQ
(blueprint: det-sp-scalar-extension-functor).
Proof: det-def-sp-tate-twist-locally-free trivializes the root line and every power
and dual on one cover. Hence every signed line is rank one and flat. Its degree-zero
complex is K-flat by lem-weil-pbc-independent-bounded-flat-kflat, so the universal
counit is invertible. Follow that counit with the localization of the ordinary
canonical scalarExtensionTateIso to obtain the derived comparison. -/
theorem scalarExtensionFunctor_tate
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ) :
    (scalarExtensionTateLine T ℓ A n a r).IsFiniteLocallyFreeOfRank 1 ∧
    (scalarExtensionTateLine T ℓ B n (f.comp a) r).IsFiniteLocallyFreeOfRank 1 ∧
    IsIso (scalarExtensionFunctorCounit f T
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (scalarExtensionTateLine T ℓ A n a r))) := by
  have hA := scalarExtensionTateLine_rank T ℓ A n a r
  have hB := scalarExtensionTateLine_rank T ℓ B n (f.comp a) r
  exact ⟨hA, hB, (scalarExtensionFunctor_line f T _ hA).1⟩

/-- The canonical derived Tate comparison, formed from the universal counit and
ordinary normalized comparison through the standard single-complex factorization.
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctorTateIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ) :
    (scalarExtensionFunctor f T).obj
        ((DerivedCategory.singleFunctor _ 0).obj (scalarExtensionTateLine T ℓ A n a r)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (scalarExtensionTateLine T ℓ B n (f.comp a) r) :=
  @asIso _ _ _ _
      (scalarExtensionFunctorCounit f T
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (scalarExtensionTateLine T ℓ A n a r)))
      (scalarExtensionFunctor_tate f T ℓ n a r).2.2 ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)) (.up ℤ) 0).app
          (scalarExtensionTateLine T ℓ A n a r)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (scalarExtensionTateIso f T ℓ n a r)

/-- Signed Kummer comparisons are fixed by the power map on roots, the identity on
coefficients, tensor products in positive degrees, and dual evaluation in negative degrees.
Source: blueprint proof (3) (blueprint: det-sp-scalar-extension-functor). -/
def IsCanonicalScalarExtensionTateLevelMaps
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (A : Type u) [CommRing A]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A)
    (c : ∀ r : ℤ, scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) r ⟶ scalarExtensionTateLine T ℓ A m a r) : Prop :=
  (∀ (U : T.ProEtᵒᵖ) (s : (proEtaleConstantRing T A).obj.obj U),
    (c 0).val.app U s = s) ∧
  (∀ (V : T.ProEt) (s : (proEtaleConstantRing T A).obj.obj (Opposite.op V))
      (x : (proEtaleRootsOfUnitySheaf T (ℓ ^ (n + 1))).obj.obj (Opposite.op V))
      (y : (scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) 1).val.obj (Opposite.op V)),
    HEq y (tateFiniteTensor T ℓ (ULift.{u + 1, u} A) n
      (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1)))))) V s x) →
    HEq ((c 1).val.app (Opposite.op V) y)
      (tateFiniteTensor T ℓ (ULift.{u + 1, u} A) m
        (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a) V s
        ((proEtaleRootsOfUnityTransition T (ℓ ^ (m + 1)) (ℓ ^ (n + 1))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))).hom.app (Opposite.op V) x))) ∧
  (∀ (k : ℕ) (U : T.ProEtᵒᵖ)
      (x : (scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) (Int.ofNat (k + 1))).val.obj U)
      (y : (scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) 1).val.obj U),
    (c (Int.ofNat (k + 2))).val.app U
        (SheafOfModules.siteSheafTensorTmul (A := proEtaleConstantRing T A) _ _ U x y) =
      SheafOfModules.siteSheafTensorTmul (A := proEtaleConstantRing T A) _ _ U
        ((c (Int.ofNat (k + 1))).val.app U x) ((c 1).val.app U y)) ∧
  ∀ (k : ℕ) (U : T.ProEtᵒᵖ)
      (d : (scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) (Int.negSucc k)).val.obj U)
      (x : (scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) (Int.ofNat (k + 1))).val.obj U),
    (((c (Int.negSucc k)).val.app U d).app (Opposite.op (Over.mk (𝟙 U.unop))))
        ((c (Int.ofNat (k + 1))).val.app U x) =
      (d.app (Opposite.op (Over.mk (𝟙 U.unop)))) x

private def scalarExtension_positiveIso
    (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {L K : proEtaleRingModules T R} (b : L ≅ K) :
    ∀ k : ℕ, WeilConjectures.coefficientTwistPower T L k ≅
      WeilConjectures.coefficientTwistPower T K k
  | 0 => Iso.refl _
  | 1 => b
  | k + 2 => (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} L).mapIso
      (scalarExtension_positiveIso T R b (k + 1)) ≪≫
        scalarExtension_tensorSecondIso T R
          (WeilConjectures.coefficientTwistPower T K (k + 1)) b

private theorem scalarExtension_positiveIso_tmul
    (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {L K : proEtaleRingModules T R} (b : L ≅ K) (k : ℕ) (U : T.ProEtᵒᵖ)
    (x : (WeilConjectures.coefficientTwistPower T L (k + 1)).val.obj U)
    (y : L.val.obj U) :
    (scalarExtension_positiveIso T R b (k + 2)).hom.val.app U
      (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (WeilConjectures.coefficientTwistPower T L (k + 1)) L U x y) =
        SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
          (WeilConjectures.coefficientTwistPower T K (k + 1)) K U
          ((scalarExtension_positiveIso T R b (k + 1)).hom.val.app U x)
          (b.hom.val.app U y) := by
  change (SheafOfModules.siteSheafTensorSecondMap.{u + 1, u, u + 1, u + 1}
      (WeilConjectures.coefficientTwistPower T K (k + 1)) b.hom).val.app U
    (((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} L).map
      (scalarExtension_positiveIso T R b (k + 1)).hom).val.app U
        (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (WeilConjectures.coefficientTwistPower T L (k + 1)) L U x y)) = _
  let G := SheafOfModules.siteSheafTensorSecondMap.{u + 1, u, u + 1, u + 1}
    (WeilConjectures.coefficientTwistPower T K (k + 1)) b.hom
  have hF := SheafOfModules.scalarTensor_first_tmul.{u + 1, u, u + 1} (R := R)
    (N := WeilConjectures.coefficientTwistPower T L (k + 1))
    (N' := WeilConjectures.coefficientTwistPower T K (k + 1))
    (scalarExtension_positiveIso T R b (k + 1)).hom L U x y
  have hG := SheafOfModules.scalarTensor_second_tmul.{u + 1, u, u + 1} (R := R)
    (P := L) (P' := K) (WeilConjectures.coefficientTwistPower T K (k + 1)) b.hom U
    ((scalarExtension_positiveIso T R b (k + 1)).hom.val.app U x) y
  exact (congrArg (fun z ↦ G.val.app U z) hF).trans hG

private def scalarExtension_signedIso
    (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {L K : proEtaleRingModules T R} (b : L ≅ K) :
    ∀ r : ℤ, WeilConjectures.coefficientTwistLine T L r ≅
      WeilConjectures.coefficientTwistLine T K r
  | .ofNat k => scalarExtension_positiveIso T R b k
  | .negSucc k => ((SheafOfModules.homFunctor (R := R)).mapIso
      (scalarExtension_positiveIso T R b (k + 1)).symm.op).app (SheafOfModules.unit _)

private theorem scalarExtension_signedIso_eval
    (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {L K : proEtaleRingModules T R} (b : L ≅ K) (k : ℕ) (U : T.ProEtᵒᵖ)
    (d : (WeilConjectures.coefficientTwistLine T L (.negSucc k)).val.obj U)
    (x : (WeilConjectures.coefficientTwistPower T L (k + 1)).val.obj U) :
    (((scalarExtension_signedIso T R b (.negSucc k)).hom.val.app U d).app
      (Opposite.op (Over.mk (𝟙 U.unop))))
        ((scalarExtension_positiveIso T R b (k + 1)).hom.val.app U x) =
      d.app (Opposite.op (Over.mk (𝟙 U.unop))) x := by
  change d.app (Opposite.op (Over.mk (𝟙 U.unop)))
    ((scalarExtension_positiveIso T R b (k + 1)).inv.val.app U
      ((scalarExtension_positiveIso T R b (k + 1)).hom.val.app U x)) = _
  have h := congrArg (fun z ↦ z.val.app U x)
    (scalarExtension_positiveIso T R b (k + 1)).hom_inv_id
  change (scalarExtension_positiveIso T R b (k + 1)).inv.val.app U
    ((scalarExtension_positiveIso T R b (k + 1)).hom.val.app U x) = x at h
  rw [h]

private theorem scalarExtensionTateLevel_unique
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type u) [CommRing A]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A)
    (d e : ∀ r : ℤ, scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) r ≅ scalarExtensionTateLine T ℓ A m a r)
    (hd : IsCanonicalScalarExtensionTateLevelMaps T ℓ A m n hmn a (fun r ↦ (d r).hom))
    (he : IsCanonicalScalarExtensionTateLevelMaps T ℓ A m n hmn a (fun r ↦ (e r).hom)) :
    d = e := by
  let R := proEtaleConstantRing T A
  let a' := ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a
  have h1 : (d 1).hom = (e 1).hom := by
    apply SheafOfModules.scalarExtension_hom_ext.{u + 1, u, u + 1, u + 1}
      (tateFiniteScalar T ℓ (ULift.{u + 1, u} A) n
        (a'.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1)))))) (purTwistRootsModule T ℓ n)
    intro U s x
    have hh := eq_of_heq ((hd.2.1 U.unop s x _ (heq_of_eq rfl)).trans
      (he.2.1 U.unop s x _ (heq_of_eq rfl)).symm)
    have hη := scalarExtension_purSection T (purTwistFiniteRing T ℓ n) R
      (tateFiniteScalar T ℓ (ULift.{u + 1, u} A) n
        (a'.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1)))))) (purTwistRootsModule T ℓ n) U.unop s x
    exact (congrArg (fun z ↦ (d 1).hom.val.app U z) hη).trans
      (hh.trans (congrArg (fun z ↦ (e 1).hom.val.app U z) hη).symm)
  have hp : ∀ q : ℕ, (d (.ofNat q)).hom = (e (.ofNat q)).hom := by
    intro q
    induction q using Nat.twoStepInduction with
    | zero =>
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact (hd.1 U s).trans (he.1 U s).symm
    | one => exact h1
    | more q hprev ih =>
      apply SheafOfModules.scalarTensor_hom_ext.{u + 1, u, u + 1}
        (scalarExtensionTateLine T ℓ A n
          (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
            (ZMod (ℓ ^ (m + 1))))) (.ofNat (q + 1)))
        (scalarExtensionTateLine T ℓ A n
          (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
            (ZMod (ℓ ^ (m + 1))))) 1)
      intro U x y
      have hx := congrArg (fun z :
          scalarExtensionTateLine T ℓ A n
            (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
              (ZMod (ℓ ^ (m + 1))))) (.ofNat (q + 1)) ⟶
          scalarExtensionTateLine T ℓ A m a (.ofNat (q + 1)) ↦ z.val.app U x) ih
      have hy := congrArg (fun z :
          scalarExtensionTateLine T ℓ A n
            (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
              (ZMod (ℓ ^ (m + 1))))) 1 ⟶
          scalarExtensionTateLine T ℓ A m a 1 ↦ z.val.app U y) h1
      exact (hd.2.2.1 q U x y).trans
        ((congrArg₂ (fun x' y' ↦
          SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
            (scalarExtensionTateLine T ℓ A m a (.ofNat (q + 1)))
            (scalarExtensionTateLine T ℓ A m a 1) U x' y') hx hy).trans
              (he.2.2.1 q U x y).symm)
  funext r
  apply Iso.ext
  cases r with
  | ofNat q => exact hp q
  | negSucc q =>
    apply SheafOfModules.scalarDual_hom_ext.{u + 1, u, u + 1}
      (scalarExtensionTateLine T ℓ A m a (.ofNat (q + 1)))
    intro U z x
    let y := (e (.ofNat (q + 1))).inv.val.app U x
    have hy : (e (.ofNat (q + 1))).hom.val.app U y = x := by
      have h := congrArg (fun z ↦ z.val.app U x) (e (.ofNat (q + 1))).inv_hom_id
      exact h
    have hpv := congrArg (fun z :
        scalarExtensionTateLine T ℓ A n
          (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
            (ZMod (ℓ ^ (m + 1))))) (.ofNat (q + 1)) ⟶
        scalarExtensionTateLine T ℓ A m a (.ofNat (q + 1)) ↦ z.val.app U y)
      (hp (q + 1))
    let F := ((d (.negSucc q)).hom.val.app U z).app
      (Opposite.op (Over.mk (𝟙 U.unop)))
    let G := ((e (.negSucc q)).hom.val.app U z).app
      (Opposite.op (Over.mk (𝟙 U.unop)))
    exact (congrArg F (hpv.trans hy).symm).trans
      ((hd.2.2.2 q U z y).trans ((he.2.2.2 q U z y).symm.trans (congrArg G hy)))


/-- Independence of every signed finite Tate line from the sufficiently large exponent,
with the Kummer-induced comparison fixed uniquely.
Source: blueprint proof (3) (blueprint: det-sp-scalar-extension-functor).
Proof: clause (2) of det-def-sp-tate-twist-locally-free identifies the root lines by
the actual Kummer power map. On the primitive-root cover it sends the chosen generator
to the chosen generator, so is an isomorphism. Take the identity on the unit, tensor
powers of this map in positive degrees, and precomposition by its inverse on duals
in negative degrees. Evaluation specifies the dual uniquely.
The root formula and tensor sheafification give uniqueness at positive degrees;
nondegenerate evaluation gives it at negative degrees. -/
theorem scalarExtensionTateLevelIso_existsUnique
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (A : Type u) [CommRing A] [Finite A]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A) :
    ∃! e : ∀ r : ℤ, scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) r ≅ scalarExtensionTateLine T ℓ A m a r,
      IsCanonicalScalarExtensionTateLevelMaps T ℓ A m n hmn a (fun r ↦ (e r).hom) := by
  classical
  let a' := ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a
  let E := ULift.{u} (Padic ℓ)
  let Ω := AlgebraicClosure (Padic ℓ)
  let ι : E →ₐ[Padic ℓ] Ω :=
    (Algebra.ofId (Padic ℓ) Ω).comp ULift.algEquiv.toAlgHom
  have hA : ∀ x : ULift.{u + 1, u} A, (ℓ ^ (m + 1)) • x = 0 := by
    have hz : ((ℓ ^ (m + 1) : ℕ) : ULift.{u + 1, u} A) = 0 := by
      have h := congrArg a' (ZMod.natCast_self (ℓ ^ (m + 1)))
      simpa only [map_natCast, map_zero] using h
    intro x
    rw [nsmul_eq_mul, hz, zero_mul]
  obtain ⟨I, U, v, ζ, e₀, hcov, hζ, he₀, hfinite, hrest⟩ :=
    tateTwist_locallyFree.{u, 0, 0} T ℓ E Ω ι
  obtain ⟨a₀, hk₀, _⟩ := hfinite (ULift.{u + 1, u} A) m hA
  have ha : a₀ = a' := Subsingleton.elim _ _
  subst a₀
  obtain ⟨k, hk⟩ := hk₀ n hmn
  have : IsIso k := hk.1
  let R := proEtaleConstantRing T A
  let b : scalarExtensionTateLine T ℓ A n
      (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
        (ZMod (ℓ ^ (m + 1))))) 1 ≅ scalarExtensionTateLine T ℓ A m a 1 := asIso k
  let e := scalarExtension_signedIso T R b
  have he : IsCanonicalScalarExtensionTateLevelMaps T ℓ A m n hmn a
      (fun r ↦ (e r).hom) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro U s
      rfl
    · intro V s x y hy
      have hy' := eq_of_heq hy
      subst y
      exact heq_of_eq (hk.2 V s x)
    · intro q U x y
      exact scalarExtension_positiveIso_tmul T R b q U x y
    · intro q U d x
      exact scalarExtension_signedIso_eval T R b q U d x
  refine ⟨e, he, ?_⟩
  intro d hd
  exact scalarExtensionTateLevel_unique T ℓ A m n hmn a d e hd he

/-- The unique signed Kummer comparison used in exponent independence.
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionTateLevelIso
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (A : Type u) [CommRing A] [Finite A]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A) :=
  (scalarExtensionTateLevelIso_existsUnique T ℓ A m n hmn a).exists.choose

section TateExponentProof
set_option backward.isDefEq.respectTransparency true
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
private theorem scalarTateExponentSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance] scalarTateExponentSmall

private theorem scalarExtensionTateMaps_spec
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :
    IsCanonicalScalarExtensionTateMaps f T ℓ n a
      (scalarExtensionTateMaps f T ℓ n a) :=
  (scalarExtensionTateMaps_existsUnique f T ℓ n a).exists.choose_spec

private theorem scalarExtensionTateLevelIso_spec
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (A : Type u) [CommRing A] [Finite A]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A) :
    IsCanonicalScalarExtensionTateLevelMaps T ℓ A m n hmn a
      (fun r ↦ (scalarExtensionTateLevelIso T ℓ A m n hmn a r).hom) :=
  (scalarExtensionTateLevelIso_existsUnique T ℓ A m n hmn a).exists.choose_spec

attribute [local irreducible] scalarExtensionTateMaps scalarExtensionTateLevelIso

private theorem scalarExtensionTate_positive_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A) :
    let aN := a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
      (ZMod (ℓ ^ (m + 1))))
    ∀ q : ℕ,
      scalarExtensionTateMaps f T ℓ n aN (.ofNat q) ≫
          (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) f)).map
            (scalarExtensionTateLevelIso T ℓ B m n hmn (f.comp a) (.ofNat q)).hom =
        (scalarExtensionTateLevelIso T ℓ A m n hmn a (.ofNat q)).hom ≫
          scalarExtensionTateMaps f T ℓ m a (.ofNat q) := by
  dsimp only
  let aN := a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
    (ZMod (ℓ ^ (m + 1))))
  let cN := scalarExtensionTateMaps f T ℓ n aN
  let cM := scalarExtensionTateMaps f T ℓ m a
  let kA := scalarExtensionTateLevelIso T ℓ A m n hmn a
  let kB := scalarExtensionTateLevelIso T ℓ B m n hmn (f.comp a)
  have hcN : IsCanonicalScalarExtensionTateMaps f T ℓ n aN cN :=
    scalarExtensionTateMaps_spec f T ℓ n aN
  have hcM : IsCanonicalScalarExtensionTateMaps f T ℓ m a cM :=
    scalarExtensionTateMaps_spec f T ℓ m a
  have hkA : IsCanonicalScalarExtensionTateLevelMaps T ℓ A m n hmn a
      (fun r ↦ (kA r).hom) :=
    scalarExtensionTateLevelIso_spec T ℓ A m n hmn a
  have hkB : IsCanonicalScalarExtensionTateLevelMaps T ℓ B m n hmn (f.comp a)
      (fun r ↦ (kB r).hom) :=
    scalarExtensionTateLevelIso_spec T ℓ B m n hmn (f.comp a)
  let β := proEtaleConstantRingMap (T := T) f
  have h1 : cN 1 ≫ (proEtaleRingRestrictScalars β).map (kB 1).hom =
      (kA 1).hom ≫ cM 1 := by
    let α := tateFiniteScalar T ℓ (ULift.{u + 1, u} A) n
      (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp aN)
    apply SheafOfModules.scalarExtension_hom_ext α (purTwistRootsModule T ℓ n)
    intro U s x
    change (kB 1).hom.val.app U ((cN 1).val.app U
      (SheafOfModules.scalarExtensionSection α _ U s x)) =
        (cM 1).val.app U ((kA 1).hom.val.app U
          (SheafOfModules.scalarExtensionSection α _ U s x))
    have hη := scalarExtension_purSection T (purTwistFiniteRing T ℓ n)
      (proEtaleConstantRing T A) α (purTwistRootsModule T ℓ n) U.unop s x
    rw [hη]
    erw [eq_of_heq (hcN.2.1 U.unop s x _ (heq_of_eq rfl)),
      eq_of_heq (hkB.2.1 U.unop (β.hom.app U s) x _ (heq_of_eq rfl)),
      eq_of_heq (hkA.2.1 U.unop s x _ (heq_of_eq rfl)),
      eq_of_heq (hcM.2.1 U.unop s _ _ (heq_of_eq rfl))]
  intro q
  induction q using Nat.twoStepInduction with
  | zero =>
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change (kB 0).hom.val.app U ((cN 0).val.app U s) =
      (cM 0).val.app U ((kA 0).hom.val.app U s)
    rw [hcN.1, hkB.1, hkA.1, hcM.1]
  | one => exact h1
  | more q _ ih =>
    apply SheafOfModules.scalarTensor_hom_ext.{u + 1, u, u + 1}
      (scalarExtensionTateLine T ℓ A n aN (.ofNat (q + 1)))
      (scalarExtensionTateLine T ℓ A n aN 1)
    intro U x y
    change (kB (.ofNat (q + 2))).hom.val.app U
      ((cN (.ofNat (q + 2))).val.app U
        (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
          (A := proEtaleConstantRing T A) _ _ U x y)) =
      (cM (.ofNat (q + 2))).val.app U
        ((kA (.ofNat (q + 2))).hom.val.app U
          (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
          (A := proEtaleConstantRing T A) _ _ U x y))
    erw [hcN.2.2.1, hkB.2.2.1, hkA.2.2.1, hcM.2.2.1]
    have hx := congrArg (fun z : scalarExtensionTateLine T ℓ A n aN (.ofNat (q + 1)) ⟶
      (proEtaleRingRestrictScalars β).obj
        (scalarExtensionTateLine T ℓ B m (f.comp a) (.ofNat (q + 1))) ↦ z.val.app U x) ih
    have hy := congrArg (fun z : scalarExtensionTateLine T ℓ A n aN 1 ⟶
      (proEtaleRingRestrictScalars β).obj (scalarExtensionTateLine T ℓ B m (f.comp a) 1) ↦
        z.val.app U y) h1
    change (kB (.ofNat (q + 1))).hom.val.app U
      ((cN (.ofNat (q + 1))).val.app U x) =
      (cM (.ofNat (q + 1))).val.app U ((kA (.ofNat (q + 1))).hom.val.app U x) at hx
    change (kB 1).hom.val.app U ((cN 1).val.app U y) =
      (cM 1).val.app U ((kA 1).hom.val.app U y) at hy
    rw [hx, hy]

private theorem scalarExtensionTate_semilinear_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A) (r : ℤ) :
    let aN := a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
      (ZMod (ℓ ^ (m + 1))))
    scalarExtensionTateMaps f T ℓ n aN r ≫
        (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) f)).map
          (scalarExtensionTateLevelIso T ℓ B m n hmn (f.comp a) r).hom =
      (scalarExtensionTateLevelIso T ℓ A m n hmn a r).hom ≫
        scalarExtensionTateMaps f T ℓ m a r := by
  let aN := a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
    (ZMod (ℓ ^ (m + 1))))
  let cN := scalarExtensionTateMaps f T ℓ n aN
  let cM := scalarExtensionTateMaps f T ℓ m a
  let kA := scalarExtensionTateLevelIso T ℓ A m n hmn a
  let kB := scalarExtensionTateLevelIso T ℓ B m n hmn (f.comp a)
  let β := proEtaleConstantRingMap (T := T) f
  have hcN : IsCanonicalScalarExtensionTateMaps f T ℓ n aN cN :=
    scalarExtensionTateMaps_spec f T ℓ n aN
  have hcM : IsCanonicalScalarExtensionTateMaps f T ℓ m a cM :=
    scalarExtensionTateMaps_spec f T ℓ m a
  have hkA : IsCanonicalScalarExtensionTateLevelMaps T ℓ A m n hmn a
      (fun r ↦ (kA r).hom) :=
    scalarExtensionTateLevelIso_spec T ℓ A m n hmn a
  have hkB : IsCanonicalScalarExtensionTateLevelMaps T ℓ B m n hmn (f.comp a)
      (fun r ↦ (kB r).hom) :=
    scalarExtensionTateLevelIso_spec T ℓ B m n hmn (f.comp a)
  cases r with
  | ofNat q => exact scalarExtensionTate_positive_square f T ℓ m n hmn a q
  | negSucc q =>
    let P := scalarExtensionTateLine T ℓ A n aN (.ofNat (q + 1))
    let N := scalarExtensionTateLine T ℓ A n aN (.negSucc q)
    let Q := scalarExtensionTateLine T ℓ B m (f.comp a) (.ofNat (q + 1))
    let e : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} β P ≅ Q :=
      (scalarExtension_ordinaryIso T β P).symm ≪≫
        scalarExtensionTateIso f T ℓ n aN (.ofNat (q + 1)) ≪≫ kB (.ofNat (q + 1))
    apply scalarExtension_semilinear_dual_ext T β N P Q e
    intro U φ x
    have he : e.hom.val.app U
        (SheafOfModules.scalarExtensionSection β P U 1 x) =
        (kB (.ofNat (q + 1))).hom.val.app U ((cN (.ofNat (q + 1))).val.app U x) := by
      change (kB (.ofNat (q + 1))).hom.val.app U
        ((scalarExtensionTateIso f T ℓ n aN (.ofNat (q + 1))).hom.val.app U
          ((scalarExtension_ordinaryIso T β P).inv.val.app U
            (SheafOfModules.scalarExtensionSection β P U 1 x))) = _
      rw [scalarExtension_ordinaryIso_inv_tmul]
      have hn := (scalarExtensionTateIso_existsUnique f T ℓ n aN
        (.ofNat (q + 1))).exists.choose_spec U 1 x
      change (scalarExtensionTateIso f T ℓ n aN (.ofNat (q + 1))).hom.val.app U
        (reductionTensorSection T β P U 1 x) = _ at hn
      exact congrArg ((kB (.ofNat (q + 1))).hom.val.app U)
        (by simpa only [one_smul, id, cN] using hn)
    rw [he]
    change ((kB (.negSucc q)).hom.val.app U ((cN (.negSucc q)).val.app U φ)).app
        (Opposite.op (Over.mk (𝟙 U.unop)))
          ((kB (.ofNat (q + 1))).hom.val.app U ((cN (.ofNat (q + 1))).val.app U x)) =
      ((cM (.negSucc q)).val.app U ((kA (.negSucc q)).hom.val.app U φ)).app
        (Opposite.op (Over.mk (𝟙 U.unop)))
          ((kB (.ofNat (q + 1))).hom.val.app U ((cN (.ofNat (q + 1))).val.app U x))
    have hp := congrArg (fun z : _ ⟶ (proEtaleRingRestrictScalars β).obj Q ↦ z.val.app U x)
      (scalarExtensionTate_positive_square f T ℓ m n hmn a (q + 1))
    change (kB (.ofNat (q + 1))).hom.val.app U ((cN (.ofNat (q + 1))).val.app U x) =
      (cM (.ofNat (q + 1))).val.app U ((kA (.ofNat (q + 1))).hom.val.app U x) at hp
    erw [hkB.2.2.2, hcN.2.2.2, hp, hcM.2.2.2, hkA.2.2.2]

end TateExponentProof

/-- Scalar extension of Tate lines commutes with the canonical exponent comparisons.
Thus the canonical comparison (A(r))_B≅B(r) is independent of the common exponent.
Source: blueprint proof (3) (blueprint: det-sp-scalar-extension-functor).
Proof: on degree-one root tensors both paths apply the same Kummer power map and f
to the scalar. In degree zero both apply f. Tensoring proves the positive cases.
Evaluate both negative maps on a positive section; the evaluation formulas give the
same image under f. Nondegeneracy gives equality. Pure tensors then give the scalar
extension square in every signed degree, and the derived counits preserve it. -/
theorem scalarExtensionTateIso_exponent_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A) (r : ℤ) :
    (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).map
        (scalarExtensionTateLevelIso T ℓ A m n hmn a r).hom ≫
      (scalarExtensionTateIso f T ℓ m a r).hom =
    (scalarExtensionTateIso f T ℓ n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) r).hom ≫
      (scalarExtensionTateLevelIso T ℓ B m n hmn (f.comp a) r).hom := by
  let aN := a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
    (ZMod (ℓ ^ (m + 1))))
  let β := proEtaleConstantRingMap (T := T) f
  apply (SheafOfModules.toSheaf _).map_injective
  apply reductionTensor_hom_ext T β (scalarExtensionTateLine T ℓ A n aN r)
  intro U s x
  change (scalarExtensionTateIso f T ℓ m a r).hom.val.app U
    (((proEtaleRingExtension β).map
      (scalarExtensionTateLevelIso T ℓ A m n hmn a r).hom).val.app U
        (reductionTensorSection T β _ U s x)) =
    (scalarExtensionTateLevelIso T ℓ B m n hmn (f.comp a) r).hom.val.app U
      ((scalarExtensionTateIso f T ℓ n aN r).hom.val.app U
        (reductionTensorSection T β _ U s x))
  erw [reductionTensor_map]
  erw [(scalarExtensionTateIso_existsUnique f T ℓ m a r).exists.choose_spec,
    (scalarExtensionTateIso_existsUnique f T ℓ n aN r).exists.choose_spec, map_smul]
  exact congrArg (fun y ↦ s • y)
    (congrArg (fun z : scalarExtensionTateLine T ℓ A n aN r ⟶
      (proEtaleRingRestrictScalars β).obj (scalarExtensionTateLine T ℓ B m (f.comp a) r) ↦
        z.val.app U x) (scalarExtensionTate_semilinear_square f T ℓ m n hmn a r)).symm

/-- The constant ring maps compose as the specified ring homomorphisms do.
Source: blueprint proof (4) (blueprint: det-sp-scalar-extension-functor).
Proof: RingHom.ulift respects composition. The constant-sheaf functor preserves
composition, so its images of f and g compose to its image of g.comp f. -/
theorem scalarExtensionFunctor_ringMap_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    proEtaleConstantRingMap (T := T) f ≫ proEtaleConstantRingMap (T := T) g =
      proEtaleConstantRingMap (T := T) (g.comp f) := by
  unfold proEtaleConstantRingMap
  rw [← Functor.map_comp]
  rfl

/-- The unique composition comparison fixed by balanced tensor on K-flat models.
Source: blueprint proof (4), Stacks 0G7E, 06YY
(blueprint: det-sp-scalar-extension-functor).
Proof: lem-pur-kflat-change-of-rings makes P tensor B K-flat, so both counits compute
successive extension. The published reductionBalance sends c tensor (b tensor p)
to c*g(b) tensor p, with inverse inserting 1. It is natural on chain maps and
preserves quasi-isomorphisms between K-flat models. The localization equivalence
lem-weil-pbc-site-derived-tensor-descent descends it through roofs to the displayed
natural isomorphism. Every derived object has a K-flat representative, and counits
are invertible on those representatives, so the normalization determines it uniquely. -/
theorem scalarExtensionFunctor_composition_existsUnique
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    ∃! α : scalarExtensionFunctor f T ⋙ scalarExtensionFunctor g T ≅
        scalarExtensionFunctor (g.comp f) T,
      ∀ (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
        CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := proEtaleConstantRing T A) P →
        α.hom.app (DerivedCategory.Q.obj P) ≫ scalarExtensionFunctorCounit (g.comp f) T P =
          (scalarExtensionFunctor g T).map (scalarExtensionFunctorCounit f T P) ≫
            scalarExtensionFunctorCounit g T
              ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P) ≫
            DerivedCategory.Q.map (reductionBalance T
              (proEtaleConstantRingMap (T := T) f) (proEtaleConstantRingMap (T := T) g)
              (proEtaleConstantRingMap (T := T) (g.comp f))
              (scalarExtensionFunctor_ringMap_comp f g T) P) := by
  obtain ⟨τ, hτ, huniq⟩ := derivedReductionComposition T
    (proEtaleConstantRingMap (T := T) f) (proEtaleConstantRingMap (T := T) g)
    (proEtaleConstantRingMap (T := T) (g.comp f))
    (scalarExtensionFunctor_ringMap_comp f g T)
  have := hτ.1
  refine ⟨asIso τ, ?_, ?_⟩
  · intro P hP
    exact hτ.2 P hP
  · intro α hα
    apply Iso.ext
    exact huniq α.hom ⟨inferInstance, hα⟩

/-- Canonical α, selected from its unique K-flat balancing characterization.
Source: blueprint clause (4) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctor_composition
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    scalarExtensionFunctor f T ⋙ scalarExtensionFunctor g T ≅
      scalarExtensionFunctor (g.comp f) T :=
  (scalarExtensionFunctor_composition_existsUnique f g T).exists.choose

private theorem scalarExtensionFunctor_composition_spec
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
      ∀ (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
        CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := proEtaleConstantRing T A) P →
        (scalarExtensionFunctor_composition f g T).hom.app (DerivedCategory.Q.obj P) ≫
            scalarExtensionFunctorCounit (g.comp f) T P =
          (scalarExtensionFunctor g T).map (scalarExtensionFunctorCounit f T P) ≫
            scalarExtensionFunctorCounit g T
              ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P) ≫
            DerivedCategory.Q.map (reductionBalance T
              (proEtaleConstantRingMap (T := T) f) (proEtaleConstantRingMap (T := T) g)
              (proEtaleConstantRingMap (T := T) (g.comp f))
              (scalarExtensionFunctor_ringMap_comp f g T) P) :=
  (scalarExtensionFunctor_composition_existsUnique f g T).exists.choose_spec

attribute [local irreducible] scalarExtensionFunctor_composition

/-- Naturality of this particular normalized α for every derived morphism.
Source: blueprint proof (4) (blueprint: det-sp-scalar-extension-functor).
Proof: balance commutes with chain maps. Resolve the middle term of a roof by
lem-pc-kflat-resolution; the tensor functors invert its quasi-isomorphism by
lem-pur-derived-change-of-rings. Naturality for both roof arrows gives the equation. -/
theorem scalarExtensionFunctor_composition_naturality
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u})
    (K L : proEtaleDerivedCategory T A) (v : K ⟶ L) :
    (scalarExtensionFunctor g T).map ((scalarExtensionFunctor f T).map v) ≫
        (scalarExtensionFunctor_composition f g T).hom.app L =
      (scalarExtensionFunctor_composition f g T).hom.app K ≫
        (scalarExtensionFunctor (g.comp f) T).map v := by
  exact (scalarExtensionFunctor_composition f g T).hom.naturality v

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false in
private theorem scalarExtensionFunctor_identity_data
    {A : Type u} [CommRing A] (T : Scheme.{u}) :
    ∃ ε : scalarExtensionFunctor (RingHom.id A) T ≅ 𝟭 _,
      ∀ (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
        ∃ v : (reductionChangeComplex T
            (proEtaleConstantRingMap (T := T) (RingHom.id A))).obj P ⟶ P,
          (∀ (i : ℤ) (U : T.ProEtᵒᵖ)
            (s : (proEtaleConstantRing T A).obj.obj U) (x : (P.X i).val.obj U),
            (v.f i).val.app U (reductionTensorSection T
              (proEtaleConstantRingMap (T := T) (RingHom.id A)) (P.X i) U s x) = s • x) ∧
          ε.hom.app (DerivedCategory.Q.obj P) =
            scalarExtensionFunctorCounit (RingHom.id A) T P ≫ DerivedCategory.Q.map v := by
  obtain ⟨e, he, _⟩ :=
    WeilConjectures.OrdinaryFieldRealization.extendUnit_existsUnique T A
  refine ⟨e, fun P ↦ ?_⟩
  simpa only [scalarExtensionFunctorCounit,
    WeilConjectures.OrdinaryFieldRealization.coefficientMap, proEtaleConstantRingMap,
    RingHom.ulift] using he P

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
/-- The identity extension has a unique multiplication-normalized unitor.
Source: blueprint proof (4), Stacks 06YY
(blueprint: det-sp-scalar-extension-functor).
Proof: the inverse of the ordinary tensor unit is p ↦ 1 tensor p. Compose its
localization with the derived counit on a K-flat model. The two multiplication
maps are inverse and natural, so descend by lem-weil-pbc-site-derived-tensor-descent.
Pure tensors determine the chain map uniquely, and K-flat resolutions determine the
natural isomorphism uniquely. -/
theorem scalarExtensionFunctor_identity_existsUnique
    {A : Type u} [CommRing A] (T : Scheme.{u}) :
    ∃! ε : scalarExtensionFunctor (RingHom.id A) T ≅ 𝟭 _,
      ∀ (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
        CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := proEtaleConstantRing T A) P →
        ∃ v : (reductionChangeComplex T
            (proEtaleConstantRingMap (T := T) (RingHom.id A))).obj P ⟶ P,
          (∀ (i : ℤ) (U : T.ProEtᵒᵖ)
            (s : (proEtaleConstantRing T A).obj.obj U) (x : (P.X i).val.obj U),
            (v.f i).val.app U (reductionTensorSection T
              (proEtaleConstantRingMap (T := T) (RingHom.id A)) (P.X i) U s x) = s • x) ∧
          ε.hom.app (DerivedCategory.Q.obj P) =
            scalarExtensionFunctorCounit (RingHom.id A) T P ≫ DerivedCategory.Q.map v := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨e, he⟩ := scalarExtensionFunctor_identity_data (A := A) T
  refine ⟨e, fun P _ ↦ he P, ?_⟩
  intro ε hε
  apply Iso.ext
  apply derived_natTrans_ext.{u + 2, u + 1, u + 2, u + 2, u + 2} _ _
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := proEtaleConstantRing T A) P)
  · intro X
    obtain ⟨P, p, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (R := proEtaleConstantRing T A) X
    exact ⟨P, p, hp, hq⟩
  · intro P hP
    obtain ⟨v, hv, hεv⟩ := hε P hP
    obtain ⟨w, hw, hew⟩ := he P
    rw [hεv, hew]
    have hvw : v = w := by
      apply HomologicalComplex.hom_ext
      intro i
      apply (SheafOfModules.toSheaf _).map_injective
      apply reductionTensor_hom_ext T
        (proEtaleConstantRingMap (T := T) (RingHom.id A)) (P.X i)
      intro U s x
      exact (hv i U s x).trans (hw i U s x).symm
    rw [hvw]

/-- The canonical identity-extension unitor, normalized by multiplication.
Source: blueprint clause (4) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctor_identity
    {A : Type u} [CommRing A] (T : Scheme.{u}) :
    scalarExtensionFunctor (RingHom.id A) T ≅ 𝟭 _ :=
  (scalarExtensionFunctor_identity_existsUnique (A := A) T).exists.choose

attribute [local irreducible] scalarExtensionFunctorCounit
  completedAdicChangeData

private theorem scalarExtension_ringMap_id
    (T : Scheme.{u}) (A : Type u) [CommRing A] :
    proEtaleConstantRingMap (T := T) (RingHom.id A) = 𝟙 _ := by
  exact CategoryTheory.Functor.map_id
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1})
    (CommRingCat.of (ULift.{u + 1, u} A))

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
private theorem scalarExtensionFunctor_unit_coherence
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    ∀ K : proEtaleDerivedCategory T A,
      (scalarExtensionFunctor_composition f (RingHom.id B) T).hom.app K =
        (scalarExtensionFunctor_identity (A := B) T).hom.app
          ((scalarExtensionFunctor f T).obj K) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨e, he⟩ := scalarExtensionFunctor_identity_data (A := B) T
  have heid : e = scalarExtensionFunctor_identity (A := B) T :=
    (scalarExtensionFunctor_identity_existsUnique (A := B) T).unique
      (fun P _ ↦ he P)
      (scalarExtensionFunctor_identity_existsUnique (A := B) T).exists.choose_spec
  let c : scalarExtensionFunctor f T ⋙ scalarExtensionFunctor (RingHom.id B) T ≅
      scalarExtensionFunctor f T :=
    Functor.isoWhiskerLeft (scalarExtensionFunctor f T) e ≪≫ Functor.rightUnitor _
  have hc : c = scalarExtensionFunctor_composition f (RingHom.id B) T := by
    apply (scalarExtensionFunctor_composition_existsUnique f (RingHom.id B) T).unique
    · intro P hP
      obtain ⟨v, hv, hev⟩ := he
        ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P)
      change (reductionChangeComplex T
        (proEtaleConstantRingMap (T := T) (RingHom.id B))).obj
          ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P) ⟶
            (reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P at v
      have hbal : v = reductionBalance T
          (proEtaleConstantRingMap (T := T) f)
          (proEtaleConstantRingMap (T := T) (RingHom.id B))
          (proEtaleConstantRingMap (T := T) ((RingHom.id B).comp f))
          (scalarExtensionFunctor_ringMap_comp f (RingHom.id B) T) P := by
        apply reductionBalance_hom_ext T
          (proEtaleConstantRingMap (T := T) f)
          (proEtaleConstantRingMap (T := T) (RingHom.id B))
          (proEtaleConstantRingMap (T := T) ((RingHom.id B).comp f))
          (scalarExtensionFunctor_ringMap_comp f (RingHom.id B) T) P
        intro i U s r x
        have hv' := hv i U s (reductionTensorSection T
          (proEtaleConstantRingMap (T := T) f) (P.X i) U r x)
        apply hv'.trans
        erw [reductionBalance_tmul, tensorSection_smul]
        have his : (proEtaleConstantRingMap (T := T) (RingHom.id B)).hom.app U r = r :=
          congrArg (fun z ↦ z.hom.app U r) (scalarExtension_ringMap_id T B)
        exact congrArg (fun z ↦ reductionTensorSection T
          (proEtaleConstantRingMap (T := T) f) (P.X i) U (s * z) x) his.symm
      have hn : (scalarExtensionFunctor (RingHom.id B) T).map
          (scalarExtensionFunctorCounit f T P) ≫ e.hom.app (DerivedCategory.Q.obj
            ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P)) =
        e.hom.app ((scalarExtensionFunctor f T).obj (DerivedCategory.Q.obj P)) ≫
          scalarExtensionFunctorCounit f T P :=
        e.hom.naturality (scalarExtensionFunctorCounit f T P)
      dsimp only [c, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, NatTrans.comp_app]
      erw [Category.comp_id]
      change e.hom.app ((scalarExtensionFunctor f T).obj (DerivedCategory.Q.obj P)) ≫
          scalarExtensionFunctorCounit f T P = _
      erw [← hn, hev, hbal]
      rfl
    · exact scalarExtensionFunctor_composition_spec f (RingHom.id B) T
  intro K
  erw [← hc]
  change e.hom.app ((scalarExtensionFunctor f T).obj K) ≫ 𝟙 _ = _
  erw [Category.comp_id, heid]

private theorem scalarExtensionBalance_cocycle
    (T : Scheme.{u}) {R S U V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (θ : U ⟶ V)
    (χ : R ⟶ U) (ω : S ⟶ V) (ζ : R ⟶ V)
    (hχ : φ ≫ ψ = χ) (hω : ψ ≫ θ = ω)
    (hζ : χ ≫ θ = ζ) (hζ' : φ ≫ ω = ζ)
    (P : CochainComplex (reductionModules T R) ℤ) :
    (reductionChangeComplex T θ).map (reductionBalance T φ ψ χ hχ P) ≫
        reductionBalance T χ θ ζ hζ P =
      reductionBalance T ψ θ ω hω ((reductionChangeComplex T φ).obj P) ≫
        reductionBalance T φ ω ζ hζ' P := by
  subst χ
  subst ω
  subst ζ
  exact reductionBalance_cocycle T φ ψ θ P

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
private theorem scalarExtensionFunctor_associativity
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (T : Scheme.{u}) :
    ∀ K : proEtaleDerivedCategory T A,
      (scalarExtensionFunctor h T).map
          ((scalarExtensionFunctor_composition f g T).hom.app K) ≫
        (scalarExtensionFunctor_composition (g.comp f) h T).hom.app K =
      (scalarExtensionFunctor_composition g h T).hom.app
          ((scalarExtensionFunctor f T).obj K) ≫
        (scalarExtensionFunctor_composition f (h.comp g) T).hom.app K := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let F := scalarExtensionFunctor f T
  let G := scalarExtensionFunctor g T
  let H := scalarExtensionFunctor h T
  let α := scalarExtensionFunctor_composition f g T
  let β := scalarExtensionFunctor_composition (g.comp f) h T
  let γ := scalarExtensionFunctor_composition g h T
  let δ := scalarExtensionFunctor_composition f (h.comp g) T
  let lhs : (F ⋙ G) ⋙ H ⟶ scalarExtensionFunctor (h.comp (g.comp f)) T :=
    Functor.whiskerRight α.hom H ≫ β.hom
  let rhs : (F ⋙ G) ⋙ H ⟶ scalarExtensionFunctor (h.comp (g.comp f)) T :=
    (Functor.associator F G H).hom ≫ Functor.whiskerLeft F γ.hom ≫ δ.hom
  suffices heq : lhs = rhs by
    intro K
    simpa only [lhs, rhs, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp]
      using congrArg (fun η ↦ η.app K) heq
  apply derived_natTrans_ext.{u + 2, u + 1, u + 2, u + 2, u + 2} _ _
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := proEtaleConstantRing T A) P ∧ ∀ i : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _
          (SheafOfModules.monoidalCategory (proEtaleConstantRing T A)) (P.X i)))
  · intro X
    obtain ⟨P, p, hk, hf, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (R := proEtaleConstantRing T A) X
    exact ⟨P, p, ⟨hk, hf⟩, hp⟩
  · intro P hP
    let φ := proEtaleConstantRingMap (T := T) f
    let ψ := proEtaleConstantRingMap (T := T) g
    let θ := proEtaleConstantRingMap (T := T) h
    let E := (reductionChangeComplex T φ).obj P
    have hE := reductionChange_isKFlat T φ P hP.1 hP.2
    have nfg := (scalarExtensionFunctor_composition_spec f g T) P hP.1
    have ngfh := (scalarExtensionFunctor_composition_spec (g.comp f) h T) P hP.1
    have nfgh := (scalarExtensionFunctor_composition_spec f (h.comp g) T) P hP.1
    have ngh := (scalarExtensionFunctor_composition_spec g h T) E hE
    have hi := scalarExtensionFunctor_kflat_representation (h.comp (g.comp f)) T P hP.1
    apply (cancel_mono (scalarExtensionFunctorCounit (h.comp (g.comp f)) T P)).1
    dsimp only [lhs, rhs, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app]
    simp only [Category.id_comp]
    simp only [Category.assoc]
    simp only [α, β, γ, δ, H, G, F] at *
    have nfgH := congrArg (fun z ↦ (scalarExtensionFunctor h T).map z) nfg
    simp only [Functor.map_comp] at nfgH
    have nγ := γ.hom.naturality (scalarExtensionFunctorCounit f T P)
    have nθ := scalarExtensionFunctor_map h T
      (reductionBalance T φ ψ (proEtaleConstantRingMap (T := T) (g.comp f))
        (scalarExtensionFunctor_ringMap_comp f g T) P)
    erw [ngfh, nfgh]
    slice_lhs 1 2 => erw [nfgH]
    simp only [Category.assoc]
    slice_rhs 1 2 => erw [← nγ]
    simp only [Category.assoc]
    slice_rhs 2 3 => erw [ngh]
    simp only [Category.assoc]
    slice_lhs 3 4 => erw [nθ]
    simp only [Category.assoc]
    congr 3
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact scalarExtensionBalance_cocycle T φ ψ θ _ _ _
      (scalarExtensionFunctor_ringMap_comp f g T)
      (scalarExtensionFunctor_ringMap_comp g h T)
      (scalarExtensionFunctor_ringMap_comp (g.comp f) h T)
      (scalarExtensionFunctor_ringMap_comp f (h.comp g) T) P

/-- The g=id unitor law and the associativity diagram for A→B→C→D.
Source: blueprint proof (4) (blueprint: det-sp-scalar-extension-functor).
Proof: for g=id the balanced map multiplies the two B scalars, which is exactly
the normalized identity unitor. For three maps both paths send d tensor
(c tensor (b tensor p)) to d*h(c)*h(g(b)) tensor p. Multiplicativity of h and
associativity in D identify these coefficients. Equality on local pure tensors
gives equality of chain maps; localization and the K-flat normalization descend
this equality to all derived objects. This is the rebracketing coherence, and
iterating it gives the pentagon with the usual unit identifications. -/
theorem scalarExtensionFunctor_coherence
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    (∀ K : proEtaleDerivedCategory T A,
      (scalarExtensionFunctor_composition f (RingHom.id B) T).hom.app K =
        (scalarExtensionFunctor_identity (A := B) T).hom.app
          ((scalarExtensionFunctor f T).obj K)) ∧
    (∀ (D : Type u) [CommRing D] (h : C →+* D) (K : proEtaleDerivedCategory T A),
      (scalarExtensionFunctor h T).map
          ((scalarExtensionFunctor_composition f g T).hom.app K) ≫
        (scalarExtensionFunctor_composition (g.comp f) h T).hom.app K =
      (scalarExtensionFunctor_composition g h T).hom.app
          ((scalarExtensionFunctor f T).obj K) ≫
        (scalarExtensionFunctor_composition f (h.comp g) T).hom.app K) := by
  exact ⟨scalarExtensionFunctor_unit_coherence f T,
    fun D _ h ↦ scalarExtensionFunctor_associativity f g h T⟩

end AlgebraicGeometry.ProEtale
