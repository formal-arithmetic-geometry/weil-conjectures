/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Mathlib.Topology.KrullDimension
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.PointFgCompleteComplexes
public import Sheaf.Paper.PointSectionsDerivedReductionData
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.PointReductionUnits
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.IntegralCompactSupportPrescribedReductions

import Sheaf.Paper.PointReductionUnitNormalization
import Sheaf.Paper.PointTorAmplitudeRealization
import Sheaf.Paper.FiniteCompactSupportUniformTor
import Sheaf.CategoryTheory.DerivedCategory.PerfectCohomologyAssembly
import Sheaf.CategoryTheory.DerivedCategory.ScalarPerfectCohomologyAndPidModels
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr

/-! # Integral sections and perfect finite reductions

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-thm-sf-package/thm-pod-point-perfectness.proof.md, Step 2
(blueprint: lem-sf-integral-sections-perfect-reduction).

The integral section values already belong to the recorded bounded, finitely generated,
derived-complete full subcategory. The main statement asserts perfectness of both values,
isomorphy of the specified coefficient maps, and finite free models in one common interval.
The canonical localization equivalence puts the recorded small section values into the
standard localization used by the quotient-tensor API; it changes no coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionDerivedExtension
/-- Canonical transport from the small module localization to the standard one.
Source: Stacks Tag 05RU, uniqueness of localization
(blueprint: lem-sf-integral-sections-perfect-reduction). -/
def sfSectionsCoefficientLift (A : Type (u + 1)) [CommRing A] :=
  (Localization.uniq
    (@DerivedCategory.Q (ModuleCat.{u + 1} A) _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _))
    (@DerivedCategory.Q (ModuleCat.{u + 1} A) _ _ (HasDerivedCategory.standard _))
    (HomologicalComplex.quasiIso _ (.up ℤ))).functor

/-- Exact section functors commute with the canonical change of module localization.
Both sides are lifts of the identical termwise functor, and the comparison is fixed by
its commutation with localization. This changes only the Hom universe.
Source: Stacks Tag 05RU, uniqueness of localization
(blueprint: lem-sf-integral-sections-perfect-reduction). -/
def sfSectionsCoefficientLiftIso
    {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 2} C]
    (A : Type (u + 1)) [CommRing A] (F : C ⥤ ModuleCat.{u + 1} A)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (@Functor.mapDerivedCategory _ _ _ _ _ _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) F _ _ _) ⋙
        sfSectionsCoefficientLift A ≅
      (@Functor.mapDerivedCategory _ _ _ _ _ _ _
        (HasDerivedCategory.standard _) F _ _ _) := by
  let h₁ : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let h₂ : HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} A) :=
    HasDerivedCategory.standard _
  let Q₁ := @DerivedCategory.Q (ModuleCat.{u + 1} A) _ _ h₁
  let Q₂ := @DerivedCategory.Q (ModuleCat.{u + 1} A) _ _ h₂
  let W := HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ)
  let F₁ := @Functor.mapDerivedCategory _ _ _ _ _ _ _ h₁ F _ _ _
  let F₂ := @Functor.mapDerivedCategory _ _ _ _ _ _ _ h₂ F _ _ _
  let H := F.mapHomologicalComplex (.up ℤ)
  let e : DerivedCategory.Q ⋙ (F₁ ⋙ sfSectionsCoefficientLift A) ≅ H ⋙ Q₂ :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ h₁ F _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft H (Localization.compUniqFunctor Q₁ Q₂ W)
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ)) (H ⋙ Q₂)
      (F₁ ⋙ sfSectionsCoefficientLift A) := ⟨e⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (H ⋙ Q₂) (H ⋙ Q₂)
    (F₁ ⋙ sfSectionsCoefficientLift A) F₂ (Iso.refl _)

/-- Identity structure on the geometric coefficient point.
Source: blueprint point-perfectness proof, Step 2
(blueprint: lem-sf-integral-sections-perfect-reduction). -/
instance sfSectionsPointOver (D : FiniteFieldDatum.{u}) :
    (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

/-- Positive finite coefficients have the recorded finite-ring structure.
Source: coefficient extension, clause 4
(blueprint: lem-sf-integral-sections-perfect-reduction). -/
instance sfSectionsFiniteCoefficient (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Products in the ordinary defining tower use exact completed-coefficient products.
Source: blueprint point-perfectness proof, Step 2
(blueprint: lem-sf-integral-sections-perfect-reduction). -/
instance sfSectionsOrdinaryHasProduct (K : sfIntegralConstructibleCategory l E X) :
    HasProduct (sfDirectImageTerm l E (X ↘ Spec (.of D.k)) K.obj) := by
  let : HasCountableProducts
      (DerivedCategory (scalarReductionSource.{u, u} l E (Spec (.of D.k)))) :=
    integralOperationsDerivedCountableProducts l E (Spec (.of D.k))
  infer_instance

/-- Retain the projection of the very Roos realization selected by `integralImage`.
This adds no choice of image object or coefficient action.
Source: blueprint point-perfectness proof, Step 2; definition of integral ordinary image
(blueprint: lem-sf-integral-sections-perfect-reduction). -/
def sfSectionsOrdinaryProjection (K : sfIntegralConstructibleCategory l E X) :
    (integralImage D l hl E X K).obj ⟶
      ∏ᶜ (sfDirectImageTerm l E (X ↘ Spec (.of D.k)) K.obj) := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (X ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  let h := sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
    E (X ↘ Spec (.of D.k)) K.obj K.property
  letI := h.1.choose
  let L : SfIntegralDirectImage l E (X ↘ Spec (.of D.k)) K.obj := h.1.choose_spec.some
  exact L.projection

/-- Retain a defining Roos projection of the actual integral compact-support value.
The vertex and its distinguished Roos triangle are selected from exactly the existence
proof used by `sfIntegralCompactSupportValue`. These are choices of a limit presentation,
up to an isomorphism preserving the projections, rather than an arbitrary comparison map.
Source: blueprint point-perfectness proof, Step 2; Bhatt--Scholze, Definition 6.7.6
(blueprint: lem-sf-integral-sections-perfect-reduction). -/
def sfSectionsCompactProjection (c : Compactification (X ↘ Spec (.of D.k)))
    (K : sfIntegralConstructibleCategory l E X) :
    (sfIntegralCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl) c K).obj ⟶
      ∏ᶜ (sfCompactSupportTerm l E c K.obj) := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (X ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  letI : HasCountableProducts
      (DerivedCategory (scalarReductionSource.{u, u} l E (Spec (.of D.k)))) :=
    integralOperationsDerivedCountableProducts l E (Spec (.of D.k))
  let h := (exists_isDerivedLimit_and_iso
    (fun n : ℕ ↦ sfCompactSupportTerm l E c K.obj n)
    (fun n : ℕ ↦ sfCompactSupportTransition l E c K.obj n)).1
  exact (Classical.choose_spec h).choose

/-- The quotient comparison on sections, with integral module localization transported
by its universal equivalence. It is the tensor adjunct of the specified projection,
conjugated by the exact-section localization comparisons, with no arbitrary map chosen.
Source: blueprint point-perfectness proof, Step 2; Stacks Tags 05RU and 07A6
(blueprint: lem-sf-integral-sections-perfect-reduction). -/
def sfSectionsReductionFromProjection (n : ℕ)
    (M : DerivedCategory (scalarReductionSource.{u, u} l E (Spec (.of D.k))))
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1)))
    (q : M ⟶ (scalarReductionDerivedRestriction l E (Spec (.of D.k)) n).obj N) :
    (pointReductionModuleTensor l E n).obj
      ((sfSectionsCoefficientLift
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))).obj
        ((pointFibreIntegralAmbient D l E).obj M)) ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))
        ).mapDerivedCategory.obj N :=
  (pointReductionModuleTensor l E n).map
    ((sfSectionsCoefficientLiftIso
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
      (pointIntegralSections l E D.k)).hom.app M) ≫
  ((pointUnitIntegralModuleAdjunction l E n).choose.homEquiv _ _).symm
    ((pointIntegralSections l E D.k).mapDerivedCategory.map q ≫
      (pointUnitIntegralDerivedSectionsRestrictionIso D l E n).hom.app N)

/-- The ordinary coefficient comparison for the recorded integral section complex.
Source: blueprint point-perfectness proof, Step 2; Stacks Tag 07A6
(blueprint: lem-sf-integral-sections-perfect-reduction). -/
def sfOrdinarySectionsReductionComparison
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    (pointReductionModuleTensor l E n).obj
      ((sfSectionsCoefficientLift
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))).obj
        (integralOrdinarySections D l hl E X K).obj) ⟶
      finiteOrdinarySections D l E X (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K.obj) :=
  sfSectionsReductionFromProjection D l E n (integralImage D l hl E X K).obj
    (sfFiniteDerivedDirectImage l E (X ↘ Spec (.of D.k)) K.obj n)
    (sfSectionsOrdinaryProjection D l hl E X K ≫
      Pi.π (sfDirectImageTerm l E (X ↘ Spec (.of D.k)) K.obj) n)

/-- The compact coefficient comparison for the recorded integral section complex.
Source: blueprint point-perfectness proof, Step 2; Stacks Tag 07A6
(blueprint: lem-sf-integral-sections-perfect-reduction). -/
def sfCompactSectionsReductionComparison
    (c : Compactification (X ↘ Spec (.of D.k)))
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    (pointReductionModuleTensor l E n).obj
      ((sfSectionsCoefficientLift
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))).obj
        (integralCompactSections D l hl E X c K).obj) ⟶
      finiteCompactSections D l E X c (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K.obj) :=
  sfSectionsReductionFromProjection D l E n
    (sfIntegralCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl) c K).obj
    ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj K.obj))
    (sfSectionsCompactProjection D l hl E X c K ≫ Pi.π (sfCompactSupportTerm l E c K.obj) n)

private theorem sfSectionsPerfectOfFiniteCohomology
    {R : Type (u + 1)} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} R)]
    (C : DerivedCategory (ModuleCat.{u + 1} R))
    (s : Finset ℤ)
    (hs : ∀ i : ℤ, i ∉ s → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj C))
    (hf : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj C)) :
    DerivedCategory.IsPerfectRingComplex C := by
  apply DerivedCategory.isPerfectRingComplex_of_perfect_cohomology C
  · obtain ⟨a, ha⟩ := s.finite_toSet.bddBelow
    obtain ⟨b, hb⟩ := s.finite_toSet.bddAbove
    refine ⟨a, b, fun i hi ↦ hs i ?_⟩
    intro his
    rcases hi with hi | hi
    · exact (not_le_of_gt hi) (ha his)
    · exact (not_le_of_gt hi) (hb his)
  · intro i
    let M := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj C
    have : Module.Finite R M := hf i
    have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    obtain ⟨r, v, hv⟩ := Module.Finite.exists_fin' R M
    obtain ⟨m, w, _, _, _, hp, _⟩ :=
      (DerivedCategory.scalar_perfect_cohomology_and_pid_models R).2 M r v hv
    exact hp

private theorem sfSectionsIntegralPerfect
    (C : (DerivedCategory.pointFgComplete
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
      (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})).FullSubcategory) :
    @DerivedCategory.IsPerfectRingComplex _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) C.obj := by
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
  have hpid : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) := by
    have hdvr := (Padic.extension_integers_dvr l E
      (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
    exact hdvr.2.2.2.2.2.2.2.2.1
  letI : IsPrincipalIdealRing R :=
    IsPrincipalIdealRing.of_surjective ULift.ringEquiv.symm.toRingHom
      ULift.ringEquiv.symm.surjective
  letI : IsDomain R := ULift.ringEquiv.toMulEquiv.isDomain
  obtain ⟨s, hs⟩ := C.property.1
  exact @sfSectionsPerfectOfFiniteCohomology _ _ _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) C.obj s hs C.property.2.1

include hl in
private theorem sfSectionsFiniteModel (n : ℕ) (a b : ℤ) (hab : a ≤ b)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1)))
    (hN : intrinsicFiniteTorsionConstructible l E (n + 1) (by omega)
      (Spec (.of D.k)) N)
    (hTor : HasProEtaleTorAmplitude (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1)) N a b) :
    ∃ P : CochainComplex (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) ℤ,
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (P.X i) ∧
        Module.Finite
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (P.X i)) ∧
      Nonempty ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))
        ).mapDerivedCategory.obj N ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨P, hP, hf, ⟨eP⟩, _⟩ := (point_tor_amplitude_realization D l hl E
    (n + 1) (by omega) a b hab ⟨N, hN⟩ hTor _ rfl).2.2
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  let Q₁ := @DerivedCategory.Q (ModuleCat.{u + 1} A) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
  let Q₂ := @DerivedCategory.Q (ModuleCat.{u + 1} A) _ _
    (HasDerivedCategory.standard _)
  let e := (sfSectionsCoefficientLiftIso A
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))).symm.app N ≪≫
      (sfSectionsCoefficientLift A).mapIso eP ≪≫
        (Localization.compUniqFunctor Q₁ Q₂
          (HomologicalComplex.quasiIso _ (.up ℤ))).app P
  refine ⟨P, ?_, ?_, hf, ⟨e⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ hP i (Or.inl hi)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ hP i (Or.inr hi)

private theorem sfSectionsAdjointIsIso
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {L : C ⥤ D} {R : D ⥤ C} {T : A ⥤ B} {U : B ⥤ A}
    (a : L ⊣ R) (b : T ⊣ U) (G : C ⥤ A) (H : D ⥤ B)
    (e : R ⋙ G ≅ H ⋙ U) (N : C)
    (χ : T.obj (G.obj N) ≅ H.obj (L.obj N))
    (hχ : b.unit.app (G.obj N) ≫ U.map χ.hom =
      G.map (a.unit.app N) ≫ e.hom.app (L.obj N))
    (M : D) (q : N ⟶ R.obj M) (hq : IsIso ((a.homEquiv N M).symm q)) :
    IsIso ((b.homEquiv (G.obj N) (H.obj M)).symm (G.map q ≫ e.hom.app M)) := by
  let f := (a.homEquiv N M).symm q
  have hf : q = a.unit.app N ≫ R.map f :=
    (Equiv.apply_symm_apply (a.homEquiv N M) q).symm
  have hm : (b.homEquiv _ _).symm (G.map q ≫ e.hom.app M) =
      χ.hom ≫ H.map f := by
    apply (b.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, b.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, hχ, hf, Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun z ↦ G.map (a.unit.app N) ≫ z) (e.hom.naturality f)
  have : IsIso f := hq
  rw [hm]
  infer_instance

private theorem sfSectionsAdjointIsIsoNat
    {C D A B C' : Type*} [Category C] [Category D] [Category A] [Category B]
    [Category C'] {L : C ⥤ D} {R : D ⥤ C} {T : A ⥤ B} {U : B ⥤ A}
    (a : L ⊣ R) (b : T ⊣ U) (G : C ⥤ A) (H : D ⥤ B)
    (e : R ⋙ G ≅ H ⋙ U) (I : C' ⥤ C)
    (χ : I ⋙ G ⋙ T ≅ I ⋙ L ⋙ H)
    (hχ : Functor.whiskerLeft (I ⋙ G) b.unit ≫ Functor.whiskerRight χ.hom U =
      Functor.whiskerRight (Functor.whiskerLeft I a.unit) G ≫
        Functor.whiskerLeft (I ⋙ L) e.hom)
    (N : C') (M : D) (q : I.obj N ⟶ R.obj M)
    (hq : IsIso ((a.homEquiv (I.obj N) M).symm q)) :
    IsIso ((b.homEquiv (G.obj (I.obj N)) (H.obj M)).symm
      (G.map q ≫ e.hom.app M)) :=
  sfSectionsAdjointIsIso a b G H e (I.obj N) (χ.app N)
    (NatTrans.congr_app hχ N) M q hq

include hl in
private theorem sfSectionsReductionIsIso (n : ℕ)
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (T : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1)))
    (q : N.obj ⟶ (scalarReductionDerivedRestriction l E (Spec (.of D.k)) n).obj T)
    (hq : IsIso (((derivedScalarExtensionRestrictionAdjunction l E
      (Spec (.of D.k)) n).choose.homEquiv N.obj T).symm q)) :
    IsIso (sfSectionsReductionFromProjection D l E n N.obj T q) := by
  let χ := ((pointReductionUnitNormalization D l E hl).1 n).exists.choose
  have hχ := ((pointReductionUnitNormalization D l E hl).1 n).exists.choose_spec
  have hi := sfSectionsAdjointIsIsoNat
    (derivedScalarExtensionRestrictionAdjunction l E (Spec (.of D.k)) n).choose
    (pointUnitIntegralModuleAdjunction l E n).choose
    (pointIntegralSections l E D.k).mapDerivedCategory
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
    (pointUnitIntegralDerivedSectionsRestrictionIso D l E n)
    (sfIntegralConstructible l E (Spec (.of D.k))).ι χ hχ N T q hq
  unfold sfSectionsReductionFromProjection
  exact IsIso.comp_isIso' (by infer_instance) hi

/-- Integral ordinary and compact sections are perfect, their canonical coefficient
comparisons are isomorphisms, and their positive reductions have finite free models
in the single interval [a,b+2d]. Bounded finite generation and completeness are
already part of the return types of the two recorded integral section values.
The quotient-tensor expressions use only the canonical change of localization.

Source: blueprint thm-pod-point-perfectness.proof.md, Step 2; Stacks Tags 066E and 068V
(blueprint: lem-sf-integral-sections-perfect-reduction).

Proof (the four steps of the node):
1. Apply lem-sf-integral-direct-image-constructible and lem-coef-integral-compact-support
   to the structure map X → Spec k, using finite type, separatedness, dim X ≤ d and
   the uniform Tor interval. Both integral images are constructible over the point;
   their canonical finite comparisons are isomorphisms. The compact reductions have
   Tor interval [a,b+2d]. All integral sheaves here are completed coefficient sheaves.
2. Each reduction of K is intrinsically bounded constructible by the integral-category
   definition. cor-sf-direct-image-ctf-proetale gives the same interval [a,b+2d] for
   ordinary finite images. lem-sf-point-tor-amplitude-realization realizes both finite
   point outputs by finite free complexes supported in exactly that interval.
3. Apply lem-weil-point-sections-finiteness (2) to both integral point images. These
   give the bounded finitely generated derived-complete section values used here.
   lem-pod-point-sections-derived-reduction composed with the image comparisons gives
   the asserted isomorphisms. Their coefficient maps are the tensor adjuncts of the
   Roos projections: the restriction/sections square is identity on sections and
   the module unit is x ↦ 1 tensor x. Localization uniqueness transports these same
   maps to the standard module localization. Transfer the finite free models along
   the comparisons, with a and b+2d unchanged for every positive exponent.
4. By lem-weil-l-adic-extension-integers-dvr the integral ring is a local PID, hence
   Noetherian. lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion makes each
   bounded finite section complex pseudo-coherent. Its unique maximal residue field
   is A₁. The finite free reduction at exponent 1 has vanishing cohomology outside
   [a,b+2d]. lem-weil-pbc-pseudocoherent-maximal-fibre-perfect therefore makes each
   integral section complex perfect. Canonical localization equivalence preserves
   finite-projective representatives, so this is perfectness in the recorded model.
-/
theorem integralSections_perfect_reduction
    (c : Compactification (X ↘ Spec (.of D.k)))
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (K : sfIntegralConstructibleCategory l E X) (a b : ℤ)
    (_hTor : ∀ n : ℕ, HasProEtaleTorAmplitude X
      (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj K.obj) a b) :
    @DerivedCategory.IsPerfectRingComplex _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
      (integralOrdinarySections D l hl E X K).obj ∧
    @DerivedCategory.IsPerfectRingComplex _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
      (integralCompactSections D l hl E X c K).obj ∧
    ∀ n : ℕ,
      IsIso (sfOrdinarySectionsReductionComparison D l hl E X K n) ∧
      IsIso (sfCompactSectionsReductionComparison D l hl E X c K n) ∧
      ∀ C : (DerivedCategory.pointFgComplete
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
          (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})).FullSubcategory,
        (C = integralOrdinarySections D l hl E X K ∨
          C = integralCompactSections D l hl E X c K) →
        ∃ P : CochainComplex (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) ℤ,
          P.IsStrictlyGE a ∧ P.IsStrictlyLE (b + 2 * (d : ℤ)) ∧
          (∀ i : ℤ, Module.Free
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (P.X i) ∧
            Module.Finite
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (P.X i)) ∧
          Nonempty ((pointReductionModuleTensor l E n).obj
            ((sfSectionsCoefficientLift
              (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))).obj C.obj) ≅
            DerivedCategory.Q.obj P) := by
  classical
  refine ⟨sfSectionsIntegralPerfect l E (integralOrdinarySections D l hl E X K),
    sfSectionsIntegralPerfect l E (integralCompactSections D l hl E X c K), ?_⟩
  intro n
  have hab : a ≤ b := (_hTor 0).1
  have habd : a ≤ b + 2 * (d : ℤ) := by omega
  obtain ⟨lo, hi, _, hK⟩ := K.property.2
  have hKn := (hK n).1
  let f : Over.mk (X ↘ Spec (.of D.k)) ⟶ Over.mk (𝟙 (Spec (.of D.k))) :=
    Over.homMk (X ↘ Spec (.of D.k)) (by simp)
  letI : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of D.k))).hom :=
    ‹LocallyOfFiniteType (X ↘ Spec (.of D.k))›
  letI : QuasiCompact (Over.mk (X ↘ Spec (.of D.k))).hom :=
    ‹QuasiCompact (X ↘ Spec (.of D.k))›
  letI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
  letI : QuasiCompact (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
  letI : IsSeparated f.left := ‹IsSeparated (X ↘ Spec (.of D.k))›
  letI : LocallyOfFiniteType f.left :=
    ‹LocallyOfFiniteType (X ↘ Spec (.of D.k))›
  letI : QuasiCompact f.left := ‹QuasiCompact (X ↘ Spec (.of D.k))›
  have ho := ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude
    D l hl E (n + 1) (by omega) _ _ f d _hd a b
    ⟨hKn, a, b, _hTor n⟩ (_hTor n)
  letI : (X ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  have hc := (ProEtale.finiteCompactSupport_uniformTor_after_denseRefinement
    D l hl E (X ↘ Spec (.of D.k)) c d _hd).2.2.2.2.2
    (n + 1) (by omega) a b hab _ hKn (_hTor n)
  have hfo := sfSectionsFiniteModel D l hl E n a (b + 2 * (d : ℤ)) habd _ ho.1 ho.2
  have hfc := sfSectionsFiniteModel D l hl E n a (b + 2 * (d : ℤ)) habd _
    hc.2.2.1 hc.2.2.2.1
  have hio : IsIso (sfOrdinarySectionsReductionComparison D l hl E X K n) := by
    apply sfSectionsReductionIsIso D l hl E n (integralImage D l hl E X K)
    let h := sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
      E (X ↘ Spec (.of D.k)) K.obj K.property
    letI := h.1.choose
    let L : SfIntegralDirectImage l E (X ↘ Spec (.of D.k)) K.obj := h.1.choose_spec.some
    exact (h.2.1 L).2.2.1 n
  have hic : IsIso (sfCompactSectionsReductionComparison D l hl E X c K n) := by
    apply sfSectionsReductionIsIso D l hl E n
      (sfIntegralCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl) c K)
    letI : HasCountableProducts
        (DerivedCategory (scalarReductionSource.{u, u} l E (Spec (.of D.k)))) :=
      integralOperationsDerivedCountableProducts l E (Spec (.of D.k))
    let h := (exists_isDerivedLimit_and_iso
      (fun n : ℕ ↦ sfCompactSupportTerm l E c K.obj n)
      (fun n : ℕ ↦ sfCompactSupportTransition l E c K.obj n)).1
    let hp := Classical.choose_spec h
    exact (integralCompactSupport_prescribedReductions l E c D hl d _hd a b hab
      K.obj K.property _hTor (Classical.choose h) hp.choose hp.choose_spec.choose
      hp.choose_spec.choose_spec).2.1 n
  refine ⟨hio, hic, ?_⟩
  intro C hC
  rcases hC with rfl | rfl
  · obtain ⟨P, ha, hb, hf, ⟨eP⟩⟩ := hfo
    exact ⟨P, ha, hb, hf, ⟨asIso
      (sfOrdinarySectionsReductionComparison D l hl E X K n) ≪≫ eP⟩⟩
  · obtain ⟨P, ha, hb, hf, ⟨eP⟩⟩ := hfc
    exact ⟨P, ha, hb, hf, ⟨asIso
      (sfCompactSectionsReductionComparison D l hl E X c K n) ≪≫ eP⟩⟩

end WeilConjectures
