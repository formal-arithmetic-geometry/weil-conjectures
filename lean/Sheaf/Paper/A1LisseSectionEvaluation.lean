/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.GlobalGeometricFrobenius
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.FieldCohomologyScalarExtension
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Canonical evaluation of ordinary sections at a geometric point

Source: Deligne, Weil II (1.1.7), (1.1.10)--(1.1.14), pp. 150--153;
Stacks 07A7, 0941 (blueprint: def-a1-lisse-section-evaluation).
The evaluation uses the whole-system adjunction counit before rationalization.
The only selected comparison is uniquely determined on pure tensors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures
namespace A1SectionEvaluation
open FrobeniusExchange

/-- The scalar-size comparison is uniquely fixed by removing the two ULifts on a
pure tensor. Source: Deligne, Weil II (1.1.10), scalar extension convention
(blueprint: def-a1-lisse-section-evaluation).
Proof: the displayed balanced tensor map has inverse sending a tensor a tensor m
to up(a) tensor up(m). Balancing gives both maps; the inverse laws and naturality
are checked on pure tensors, which span. Thus the normalization determines the
natural isomorphism uniquely. -/
theorem coefficientModulesIso_existsUnique {F Ω : Type u} [Field F] [Field Ω]
    (φ : F →+* Ω) :
    ∃! e : frobeniusCoefficientModules.{u, u} φ ≅ ModuleCat.extendScalars.{u, u, u} φ,
      ∀ (M : ModuleCat.{u} F) (a : Ω) (m : M),
        e.hom.app M
          (ULift.up a ⊗ₜ[ULift.{u} F, frobeniusCoefficientLiftHom φ] ULift.up m) =
            a ⊗ₜ[F, φ] m := by
  sorry

/-- The unique normalized coefficient comparison, including the identity field map.
Source: Deligne, Weil II (1.1.10)
(blueprint: def-a1-lisse-section-evaluation). -/
def coefficientModulesIso {F Ω : Type u} [Field F] [Field Ω] (φ : F →+* Ω) :=
  (coefficientModulesIso_existsUnique φ).exists.choose

/-- H^0 of the large derived scalar transport is the usual scalar extension of H^0.
Source: Deligne, Weil II (1.1.10); exact scalar extension
(blueprint: def-a1-lisse-section-evaluation). -/
def coefficientCohomologyIso {F Ω : Type u} [Field F] [Field Ω] (φ : F →+* Ω)
    (C : (DerivedCategory.pointFiniteDimensional F).FullSubcategory) :
    (@DerivedCategory.homologyFunctor (ModuleCat.{u} Ω) _ _
      (HasDerivedCategory.standard _) 0).obj
        ((frobeniusCohomologyCoefficientExtension φ).obj C.obj) ≅
      (ModuleCat.extendScalars φ).obj
        ((DerivedCategory.coefficientFdCohomology F 0).obj C) := by
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} Ω) := HasDerivedCategory.standard _
  letI : (frobeniusCoefficientModules φ).Additive := by
    dsimp [frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteLimits (frobeniusCoefficientModules φ) := by
    dsimp [frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteColimits (frobeniusCoefficientModules φ) := by
    dsimp [frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  exact (@CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso
    (ModuleCat.{u} F) (ModuleCat.{u} Ω) _ _ _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u} _)
    (HasDerivedCategory.standard _) (frobeniusCoefficientModules φ) _ _ _ 0).symm.app
      C.obj ≪≫ (coefficientModulesIso φ).app
      ((DerivedCategory.coefficientFdCohomology F 0).obj C)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary integral direct-image functor, in its specified system model.
Source: Stacks 0941 (blueprint: def-a1-lisse-section-evaluation). -/
def integralImage :
    sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left ⥤
      sfIntegralConstructibleCategory l E (Spec (.of D.k)) := by
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) := ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  exact directImageFunctor l E D.k (zlClosurePrimeUnit D l hl) (D.geometricFiber Y₀).hom

/-- The ordinary counit on completed integral objects: pullback realization,
whole-system counit, and inverse completeness unit.
Source: Stacks 07A7, 0941 (blueprint: def-a1-lisse-section-evaluation). -/
def integralCounit (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (@constructibleIntegralPullback l _ E _ _ _ _ _ (D.geometricFiber Y₀).hom
      (sfWeilPrimeInvertible D l hl Y₀) (frobeniusPointPrimeInvertible D l hl)).obj
        ((integralImage (D := D) (l := l) (hl := hl) (Y₀ := Y₀) (E := E)).obj M) ⟶ M :=
  let X := (D.geometricFiber Y₀).left
  let s := Spec (.of D.k)
  let a := (D.geometricFiber Y₀).hom
  let A := integralComparisonDerivedSequencePullback l E a
  let R := systemDirect l E a
  let B := reduction l E X
  let S := (models l E).system s
  let T := (models l E).system X
  letI := (models l E).complete X M
  ObjectProperty.homMk
    (((models l E).pullback a).realization.hom.app
        ((integralImage (D := D) (l := l) (hl := hl) (Y₀ := Y₀) (E := E)).obj M).obj ≫
      (coefficientSequenceLimit l E X).map
        (A.map (S.adjunction.counit.app (R.obj (B.obj M.obj))) ≫
          (systemAdjunction l E a).counit.app (B.obj M.obj)) ≫
      inv (T.adjunction.unit.app M.obj))

/-- The integral germ at a k-point. Its first factor is the inverse pullback unit;
the next two factors identify z*a* with the identity; the last applies the counit.
Source: Stacks 07A7 (blueprint: def-a1-lisse-section-evaluation). -/
def integralGerm (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (integralImage (D := D) (l := l) (hl := hl) (Y₀ := Y₀) (E := E)).obj M ⟶
      (@constructibleIntegralPullback l _ E _ _ _ _ _ z
        (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀)).obj M :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  let comparisons := (integralPullbackComparisonRealization l
    (ULift.{u} ℚ_[l]) (ULift.{u} ℚ_[l]) (AlgHom.id ℚ_[l] (ULift.{u} ℚ_[l]))).choose
  ObjectProperty.homMk
    ((integralComparisonUnit l E comparisons (Spec (.of D.k))
        ((integralImage (D := D) (l := l) (hl := hl) (Y₀ := Y₀) (E := E)).obj M)).inv ≫
      eqToHom (congrArg (fun f ↦ (integralDerivedPullback l E f).obj
        ((integralImage (D := D) (l := l) (hl := hl) (Y₀ := Y₀) (E := E)).obj M).obj) hz.symm) ≫
      (((integralPullbackComposition l E).choose z
        (D.geometricFiber Y₀).hom).hom.app
          ((integralImage (D := D) (l := l) (hl := hl) (Y₀ := Y₀) (E := E)).obj M)).hom ≫
      (integralDerivedPullback l E z).map (integralCounit (D := D) (l := l) (hl := hl)
        (Y₀ := Y₀) (E := E) M).hom)

/-- Ordinary rational evaluation is the localization of that actual integral germ.
Source: Deligne, Weil II (1.1.7); Stacks 07A7
(blueprint: def-a1-lisse-section-evaluation). -/
def rationalGerm (c₀ : Compactification Y₀.hom)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (frobeniusCohomologyRationalFunctor D l hl E Y₀ c₀ false).obj M ⟶
      (pointRationalFibre D l hl E).obj
        ((@rationalDerivedPullback l _ E _ _ _ _ _ z
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀)).obj M) :=
  (pointRationalFibre D l hl E).map
    ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).map
      (integralGerm (D := D) (l := l) (hl := hl) (Y₀ := Y₀) (E := E) z hz M.obj) ≫
        (@localPullbackObjectIso l _ E _ _ _ _ _ z
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀) M).inv)

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The published global H^0 module, carrying the specified ordinary Frobenius.
Source: Deligne, Weil II (1.1.10), (1.1.14)
(blueprint: def-a1-lisse-section-evaluation). -/
def sections (c₀ : Compactification Y₀.hom)
    (K : sfCommonStageWeilComplex D l hl Y₀ Ω) : ModuleCat.{u} Ω :=
  (globalGeometricFrobeniusQbarCohomology D l hl Y₀ Ω c₀ K false 0).a

/-- The scalar-extended finite-stage module underlying the recorded stalk.
Source: Deligne, Weil II (1.1.7), (1.1.10)
(blueprint: def-a1-lisse-section-evaluation). -/
def stalkTarget (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) : ModuleCat.{u} Ω :=
  (ModuleCat.extendScalars (frobeniusCohomologyStageEmbedding l Ω K.carrier.stage)).obj
    ((DerivedCategory.coefficientFdCohomology
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.carrier.stage) 0).obj
      ((pointRationalFibre D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.carrier.stage)).obj
          ((@rationalDerivedPullback l _
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.carrier.stage)
            _ _ _ _ _ z (frobeniusPointPrimeInvertible D l hl)
            (sfWeilPrimeInvertible D l hl Y₀)).obj K.carrier.obj)))

/-- The stalk pullback comparison on H^0. Source: Deligne, Weil II (1.1.7)
(blueprint: def-a1-lisse-section-evaluation). -/
def stalkPullbackIso (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (DerivedCategory.coefficientQbarCohomology l Ω 0).mapIso
    ((pointQbarFibre D l hl Ω).mapIso
      (localQbarPullbackStageIso l Ω z K.carrier))

/-- The literal stage point-fibre comparison on H^0. Source: Deligne, Weil II (1.1.7)
(blueprint: def-a1-lisse-section-evaluation). -/
def stalkFibreIso (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (DerivedCategory.coefficientQbarCohomology l Ω 0).mapIso
    (localQbarFibreObjIso l Ω D hl
      ((GeneralAlgebraicallyClosedCoefficients.inclusion K.carrier.stage).obj
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.carrier.stage) z).obj
            K.carrier.obj)))

/-- The exact-scalar and tensor-tower comparison on the literal point fibre.
Source: Deligne, Weil II (1.1.10)
(blueprint: def-a1-lisse-section-evaluation). -/
def stalkScalarIso (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  let F := K.carrier.stage
  let φ := (Shrink.algEquiv ℚ_[l] F.val).toRingHom
  let ψ := F.val.subtype
  let C := (pointRationalFibre D l hl
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj
      ((rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) z).obj K.carrier.obj)
  (ModuleCat.extendScalars ψ).mapIso
    ((DerivedCategory.fieldDerivedHomologyIso φ 0).app C.obj) ≪≫
      (ModuleCat.extendScalarsComp φ ψ).symm.app
        ((DerivedCategory.coefficientFdCohomology
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) 0).obj C)

/-- Identify the recorded stalk with scalar extension of its literal-stage fibre.
Source: Deligne, Weil II (1.1.7), (1.1.10)
(blueprint: def-a1-lisse-section-evaluation). -/
def stalkIso (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    localQbarStalk l Ω D hl Y₀ K z ≅ stalkTarget D l hl Y₀ Ω K z :=
  stalkPullbackIso D l hl Y₀ Ω K z ≪≫ stalkFibreIso D l hl Y₀ Ω K z ≪≫
    stalkScalarIso D l hl Y₀ Ω K z

/-- Evaluation is H^0 of the localized integral counit, with the recorded source
and stalk comparisons. It is independent of any chosen arbitrary linear map.
Source: Deligne, Weil II (1.1.7), (1.1.10)--(1.1.14)
(blueprint: def-a1-lisse-section-evaluation). -/
def evaluation (c₀ : Compactification Y₀.hom)
    (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    @Quiver.Hom (ModuleCat.{u} Ω) inferInstance
      (sections D l hl Y₀ Ω c₀ K) (localQbarStalk l Ω D hl Y₀ K z) := by
  let F := K.carrier.stage
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F
  let φ := frobeniusCohomologyStageEmbedding l Ω F
  let C := (frobeniusCohomologyRationalFunctor D l hl E Y₀ c₀ false).obj K.carrier.obj
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} Ω) := HasDerivedCategory.standard _
  let e := (DerivedCategory.homologyFunctor (ModuleCat.{u} Ω) 0).mapIso
    (eqToIso (frobeniusCohomologyQbarSourceEq D l hl Y₀ Ω c₀ false K.carrier))
  let eStalk := stalkIso D l hl Y₀ Ω K z
  exact e.hom ≫ (coefficientCohomologyIso φ C).hom ≫
    (ModuleCat.extendScalars φ).map
      ((DerivedCategory.coefficientFdCohomology E 0).map
        (rationalGerm D l hl Y₀ E c₀ z hz K.carrier.obj)) ≫
    eStalk.inv

end A1SectionEvaluation
end WeilConjectures
