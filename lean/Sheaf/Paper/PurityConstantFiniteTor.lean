/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.FiniteCtfTriangulated
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.Derived.Invertible

/-! # The coefficient unit is finite Tor constructible
Source: blueprint main-20261015, lem-pur-gysin-structure, proof step 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] Sheaf.monoidalCategory in
private def constant_unit_iso {D : Type*} [Category D]
    (J : GrothendieckTopology D) (A : Type*) [Category A] [MonoidalCategory A]
    [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal] :
    (constantSheaf J A).obj (MonoidalCategory.tensorUnit A) ≅
      MonoidalCategory.tensorUnit (Sheaf J A) :=
  (Functor.Monoidal.εIso (presheafToSheaf J A)).symm

private theorem single_homology_property {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms]
    (A : C) (hA : Q A) : Q ((DerivedCategory.homologyFunctor C 0).obj
      ((DerivedCategory.singleFunctor C 0).obj A)) :=
  Q.prop_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app A).symm hA

private def tensor_amplitude
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (Y : Scheme.{u}) (a b : ℤ)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) : Prop :=
  ∀ (M : Sheaf Y.smallEtaleTopology A) (q : ℤ), q < a ∨ b < q →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((Etale.derivedTensor A Y).obj K).obj ((DerivedCategory.singleFunctor _ 0).obj M)))

private theorem amplitude_eq (Λ : Type (u + 1)) [CommRing Λ] (Y : Scheme.{u})
    (a b : ℤ) :
    Etale.DerivedCategory.hasTorAmplitudeIn Λ Y a b =
      tensor_amplitude (ModuleCat.{u + 1} Λ) Y a b := rfl

private theorem constant_properties
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u}) (Q : ObjectProperty (Sheaf Y.smallEtaleTopology A))
    [Q.IsClosedUnderIsomorphisms]
    (hunit : Q (MonoidalCategory.tensorUnit (Sheaf Y.smallEtaleTopology A))) :
    let K := (DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology A) 0).obj
      ((constantSheaf Y.smallEtaleTopology A).obj (MonoidalCategory.tensorUnit A))
    Q ((DerivedCategory.homologyFunctor _ 0).obj K) ∧
    tensor_amplitude A Y 0 0 K := by
  let S := DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology A) 0
  let e₀ := constant_unit_iso Y.smallEtaleTopology A
  refine ⟨single_homology_property Q _ (Q.prop_of_iso e₀.symm hunit), ?_⟩
  intro M q hq
  let e := S.mapIso e₀ ≪≫ Etale.singleFunctorObjUnitIso A Y
  let d := ((Etale.derivedTensor A Y).flip.obj (S.obj M)).mapIso e ≪≫
    Etale.derivedTensorLeftUnitor A Y (S.obj M)
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor _ q).mapIso d)
  rcases hq with hq | hq
  · exact (DerivedCategory.isGE_iff (S.obj M) 0).mp inferInstance q hq
  · exact (DerivedCategory.isLE_iff (S.obj M) 0).mp inferInstance q hq

private theorem constant_etale_finiteTor (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (Y : Scheme.{u}) :
    Etale.DerivedCategory.isBoundedConstructible Λ Y
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ))) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn Λ Y 0 0
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ))) := by
  let C := Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let S := DerivedCategory.singleFunctor C 0
  let K := S.obj ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (ModuleCat.of Λ Λ))
  let Q : ObjectProperty C := fun A ↦ Scheme.IsConstructibleSheaf A
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e hA ↦ hA.of_iso e⟩
  obtain ⟨hzero, ht⟩ := constant_properties (ModuleCat.{u + 1} Λ) Y Q
    (Scheme.isConstructibleSheaf_unit Y Λ)
  have hz (q : ℤ) (hq : q < 0 ∨ 0 < q) :
      IsZero ((DerivedCategory.homologyFunctor C q).obj K) := by
    rcases hq with hq | hq
    · exact (DerivedCategory.isGE_iff K 0).mp inferInstance q hq
    · exact (DerivedCategory.isLE_iff K 0).mp inferInstance q hq
  have hc : Etale.DerivedCategory.isBoundedConstructible Λ Y K := by
    refine ⟨fun q ↦ ?_, 0, 0, le_rfl, hz⟩
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    rcases lt_trichotomy q 0 with hq | rfl | hq
    · exact Scheme.IsConstructibleSheaf.of_isZero (hz q (.inl hq))
    · exact hzero
    · exact Scheme.IsConstructibleSheaf.of_isZero (hz q (.inr hq))
  refine ⟨hc, ?_⟩
  rw [amplitude_eq]
  exact ht

/-- The constant rank-one coefficient complex has Tor amplitude [0,0] and constructible
cohomology in the intrinsic presentation.
Source: blueprint main-20261015, lem-pur-gysin-structure, first paragraph, tensor-unit argument
(blueprint: lem-pur-constant-finite-tor).

Proof: the coefficient quotient is finite at a positive level. The intrinsic realization
of the constant fixed-scalar sheaf is the free rank-one module over the constant ring
sheaf, by the scalar sheafification unit. This comparison is exact and commutes with
single complexes, so its cohomology vanishes away from zero. On the one-stratum partition
consisting of the whole scheme the surviving sheaf is already constant with finite fibre,
hence constructible. The free rank-one module is flat. Its degree-zero complex is K-flat:
tensoring it with an acyclic complex is that complex via the degreewise maps a tensor x
maps to ax and x maps to 1 tensor x. Thus its derived tensor with any degree-zero sheaf is
that sheaf in degree zero. Independence of K-flat resolutions transfers this calculation to
every representative in the definition of HasProEtaleTorAmplitude. Choose [0,0]. -/
theorem constant_finiteTor (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (.of P.field.k)) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((finiteCoefficientIntrinsicRealization Y P.Ring).mapDerivedCategory.obj
        (P.derivedSheaf h Y false)) := by
  let : ∀ x : Y, Invertible (P.coefficients.l : Y.residueField x) := fun x ↦
    (show IsUnit (P.coefficients.l : Y.residueField x) from by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk Y a x).map (Y.residue x).hom).invertible
  let K := (DerivedCategory.singleFunctor (EtSheaves P Y) 0).obj (P.constantEtale Y)
  obtain ⟨hc, ht⟩ := constant_etale_finiteTor P.Coefficient Y
  obtain ⟨hc, ht⟩ := finiteCoefficient_comparison_preserves_torAmplitude
    P.field P.coefficients.l P.coefficients.different P.extension P.level P.level_pos
    Y 0 0 le_rfl K hc ht
  let F := comparisonUpperStar (Modules P) Y
  let G := finiteCoefficientIntrinsicRealization Y P.Ring
  have : G.Additive := finiteCoefficientIntrinsicRealization_additive Y P.Ring
  have : PreservesFiniteLimits G :=
    finiteCoefficientIntrinsicRealization_preservesFiniteLimits Y P.Ring
  have : PreservesFiniteColimits G :=
    finiteCoefficientIntrinsicRealization_preservesFiniteColimits Y P.Ring
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y) :=
    (Scheme.finite_ctf_isTriangulated P.coefficients.l P.extension P.level P.level_pos Y).1
  let d : (finiteCoefficientIntrinsicDerivedComparison Y P.Ring).obj K ≅
      G.mapDerivedCategory.obj (P.derivedSheaf h Y false) :=
    (Functor.mapDerivedCategoryCompIso F G).app K ≪≫
      G.mapDerivedCategory.mapIso ((F.mapDerivedCategorySingleFunctor 0).app
        (P.constantEtale Y))
  exact (finiteTorConstructible _ _ _ _ _).prop_of_iso d ⟨hc, 0, 0, ht⟩

end WeilConjectures.PurityFiniteSetting
