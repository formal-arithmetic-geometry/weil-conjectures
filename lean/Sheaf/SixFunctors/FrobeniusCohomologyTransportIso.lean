/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Sheaf.Paper.FieldDerivedScalarTower
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfCommonStageDirectImage
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.CommonStageCompactWeilCohomology
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.SixFunctors.FrobeniusSquareCartesian
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.FrobeniusGeometricExchange
import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.Paper.CompactificationCoherence
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import Sheaf.AlgebraicGeometry.FrobeniusOpenSquare
import Sheaf.Paper.SfIntegralConstructible
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Paper.IntegralDerivedOperationsOnSlices

/-!
# Invertibility of Frobenius cohomology transport

Source: Deligne, *La conjecture de Weil II*, (1.1.7), (1.1.10)--(1.1.14),
and the Weil blueprint (blueprint: lem-weil-frobenius-cohomology-transport-iso).

The statement records invertibility of the canonical point transports, the two
Frobenius exchange components, and their induced maps in every cohomological
degree, for each of the four coefficient realizations.
The realization helpers expose the canonical functors on arbitrary common-stage
morphisms used by the naturality statement, retaining the recorded transport values.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

open FrobeniusExchange

section CoefficientRealization

/-- The coefficient embedding between the two canonical common-size lifts.
Source: Deligne, Weil II (1.1.10), coefficient realization
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCoefficientLiftHom {F : Type u} [Field F] {Ω : Type v} [Field Ω]
    (φ : F →+* Ω) : ULift.{v, u} F →+* ULift.{u, v} Ω :=
  (ULift.ringEquiv : ULift.{u, v} Ω ≃+* Ω).symm.toRingHom.comp
    (φ.comp (ULift.ringEquiv : ULift.{v, u} F ≃+* F).toRingHom)

/-- The ordinary exact scalar-and-size transport underlying the recorded derived functor.
Source: Deligne, Weil II (1.1.10), coefficient realization
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCoefficientModules {F : Type u} [Field F] {Ω : Type v} [Field Ω]
    (φ : F →+* Ω) : ModuleCat.{u} F ⥤ ModuleCat.{max u v} Ω :=
  let ψ := frobeniusCoefficientLiftHom φ
  ModuleCat.uliftFunctor.{v, u} F ⋙
    ModuleCat.restrictScalars.{max u v, max u v, u}
      (ULift.ringEquiv : ULift.{v, u} F ≃+* F).toRingHom ⋙
    ModuleCat.extendScalars.{max u v, max u v, max u v} ψ ⋙
    ModuleCat.restrictScalars.{max u v, v, max u v}
      (ULift.ringEquiv : ULift.{u, v} Ω ≃+* Ω).symm.toRingHom

/-- Balanced tensor multiplication uniquely fixes the size-compatible tower comparison.
Source: Deligne, Weil II (1.1.10), coefficient extension
(blueprint: lem-weil-frobenius-cohomology-transport-iso).
Proof: send a tensor up(b tensor m) to (a * up(ψ b)) tensor up(m).
Balancing over both fields proves well-definedness. The inverse sends a tensor
up(m) to a tensor up(1 tensor m); the tensor relations prove both inverse laws.
Pure tensors generate, proving naturality and uniqueness. -/
theorem frobeniusCoefficientModulesTower_existsUnique
    {F G : Type u} [Field F] [Field G] {Ω : Type v} [Field Ω]
    (φ : F →+* G) (ψ : G →+* Ω) :
    ∃! e : ModuleCat.extendScalars.{u, u, u} φ ⋙ frobeniusCoefficientModules ψ ≅
        frobeniusCoefficientModules (ψ.comp φ),
      ∀ (M : ModuleCat.{u} F) (a : ULift.{u, v} Ω) (b : G) (m : M),
        e.hom.app M
          (a ⊗ₜ[ULift.{v, u} G, frobeniusCoefficientLiftHom ψ]
            ULift.up (b ⊗ₜ[F, φ] m)) =
          (a * ULift.up (ψ b)) ⊗ₜ[ULift.{v, u} F, frobeniusCoefficientLiftHom (ψ.comp φ)]
            ULift.up m := by
  sorry

/-- The derived tower comparison is the image of the specified balanced tensor map.
Source: Deligne, Weil II (1.1.10), common-stage realization
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCoefficientTower {F G : Type u} [Field F] [Field G]
    {Ω : Type v} [Field Ω] (φ : F →+* G) (ψ : G →+* Ω) :
    DerivedCategory.fieldDerivedScalarExtension φ ⋙
        frobeniusCohomologyCoefficientExtension ψ ≅
      frobeniusCohomologyCoefficientExtension (ψ.comp φ) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} F) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u} (ModuleCat.{u} G) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  let A := frobeniusCoefficientModules ψ
  let B := frobeniusCoefficientModules (ψ.comp φ)
  letI : A.Additive := by
    dsimp [A, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteLimits A := by
    dsimp [A, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteColimits A := by
    dsimp [A, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : B.Additive := by
    dsimp [B, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteLimits B := by
    dsimp [B, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteColimits B := by
    dsimp [B, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  exact (Functor.mapDerivedCategoryCompIso _ A).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (frobeniusCoefficientModulesTower_existsUnique φ ψ).exists.choose

end CoefficientRealization

section GeometricFunctors
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

/-- The actual rational RΓ or RΓ_c functor used by the transport component.
Source: Deligne, Weil II (1.1.14); the retained coefficient-stage recipe
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRationalFunctor (c₀ : Compactification Y₀.hom) (compact : Bool) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  modelRationalFunctor l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) E ⋙ pointRationalFibre D l hl E



/-- The actual localized operation, before the point fibre is applied.
Source: Deligne, Weil II (1.1.14), ordinary and compact recipes
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRationalOperation (c₀ : Compactification Y₀.hom) (compact : Bool) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  modelRationalFunctor l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) E

/-- The integral coefficient mate retained by the ordinary or compact recipe.
Source: Deligne, Weil II (1.1.14), coefficient descent
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyIntegralScalar (c₀ : Compactification Y₀.hom) (compact : Bool)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  modelScalar l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) E L ι

/-- Rational operation comparison, uniquely normalized by the integral coefficient mate.
Source: Deligne, Weil II (1.1.14), coefficient descent
(blueprint: lem-weil-frobenius-cohomology-transport-iso).
Proof: localize the displayed integral comparison and its inverse. The scalar
linearity of its components makes the localized maps natural on every rational
Hom. The raw localization has the same integral object representatives, so the
component equation fixes every component and proves uniqueness. -/
theorem frobeniusCohomologyRationalOperationScalar_existsUnique
    (c₀ : Compactification Y₀.hom) (compact : Bool)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :
    ∃! b : frobeniusCohomologyRationalOperation D l hl E Y₀ c₀ compact ⋙
        sfRationalScalarExtension l E (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
      sfRationalScalarExtension l E (D.geometricFiber Y₀).left 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
        frobeniusCohomologyRationalOperation D l hl L Y₀ c₀ compact,
      ∀ K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left,
        HEq (b.hom.app K)
          ((sfRationalConstructibleLocalization l L (Spec (.of D.k))).map
            ((frobeniusCohomologyIntegralScalar D l hl E Y₀ c₀ compact L ι).hom.app K.obj)) := by
  sorry

/-- The normalized rational operation scalar comparison.
Source: Deligne, Weil II (1.1.14), coefficient descent
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRationalOperationScalar
    (c₀ : Compactification Y₀.hom) (compact : Bool)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :=
  (frobeniusCohomologyRationalOperationScalar_existsUnique D l hl E Y₀ c₀ compact L ι).exists.choose

/-- Cohomology scalar comparison: the localized operation mate followed by the
recorded point-fibre scalar comparison, with their actual associators.
Source: Deligne, Weil II (1.1.14), coefficient descent
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRationalScalar
    (c₀ : Compactification Y₀.hom) (compact : Bool)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :
    frobeniusCohomologyRationalFunctor D l hl E Y₀ c₀ compact ⋙
        DerivedCategory.pointFdScalarExtension ι.toRingHom ≅
      sfRationalScalarExtension l E (D.geometricFiber Y₀).left 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
        frobeniusCohomologyRationalFunctor D l hl L Y₀ c₀ compact :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (frobeniusCohomologyRationalOperation D l hl E Y₀ c₀ compact)
      (pointRationalFibreScalarIso D l hl E L ι).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (frobeniusCohomologyRationalOperationScalar D l hl E Y₀ c₀ compact L ι)
      (pointRationalFibre D l hl L) ≪≫ Functor.associator _ _ _

end GeometricFunctors

section CommonStageFunctors
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (stageSystem)
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The canonical embedding of the actual small coefficient model into Ω.
Source: Deligne, Weil II (1.1.10), finite fields of definition
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyStageEmbedding (E : Index l Ω) : Coefficient.{u} l Ω E →+* Ω :=
  E.val.subtype.comp (Shrink.algEquiv ℚ_[l] E.val).toRingHom

/-- Inclusion followed by realization is the original embedding, including E=L.
Source: Deligne, Weil II (1.1.10), coefficient convention
(blueprint: lem-weil-frobenius-cohomology-transport-iso).
Proof: expand coefficientInclusion, cancel the Shrink equivalence with its inverse,
and use the defining subtype inclusion. Ring-hom extensionality gives equality. -/
theorem frobeniusCohomologyStageEmbedding_comp (E L : Index l Ω) (h : E ≤ L) :
    (frobeniusCohomologyStageEmbedding.{u, v} l Ω L).comp
        (coefficientInclusion.{u} l Ω E L h).toRingHom =
      frobeniusCohomologyStageEmbedding.{u, v} l Ω E := by
  sorry

/-- RΓ or RΓ_c at a finite field of definition, realized in the recorded D(Ω).
Its object values are literally the source values of frobeniusTransportQbar.
Source: Deligne, Weil II (1.1.14), common-stage transport
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRealizedStage (c₀ : Compactification Y₀.hom) (compact : Bool)
    (E : Index l Ω) :
    sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) (D.geometricFiber Y₀).left ⥤
      @DerivedCategory (ModuleCat.{max u v} Ω) _ _ (HasDerivedCategory.standard _) := by
  letI : Algebra ℚ_[l] (Coefficient.{u} l Ω E) :=
    inferInstanceAs (Algebra ℚ_[l] (Shrink.{u} E.val))
  exact frobeniusCohomologyRationalFunctor D l hl (Coefficient.{u} l Ω E) Y₀ c₀ compact ⋙
    (DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω E)).ι ⋙
      frobeniusCohomologyCoefficientExtension.{u, v}
        (frobeniusCohomologyStageEmbedding.{u, v} l Ω E)

/-- The actual comparison from an object's own realization to any enlarged stage.
It uses the localized whole-system mate, the point scalar comparison, and the
specified balanced tensor tower. No comparison is chosen arbitrarily.
Source: Deligne, Weil II (1.1.14), common-stage transport
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRealizedComparison (c₀ : Compactification Y₀.hom) (compact : Bool)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    (L : Index l Ω) (h : K.stage ≤ L) :
    (frobeniusCohomologyRealizedStage D l hl Y₀ Ω c₀ compact K.stage).obj K.obj ≅
      (frobeniusCohomologyRealizedStage D l hl Y₀ Ω c₀ compact L).obj (K.toStage h) :=
  eqToIso (congrArg
      (fun φ ↦ (frobeniusCohomologyCoefficientExtension φ).obj
        ((frobeniusCohomologyRationalFunctor D l hl
          (Coefficient.{u} l Ω K.stage) Y₀ c₀ compact).obj K.obj).obj)
      (frobeniusCohomologyStageEmbedding_comp l Ω K.stage L h).symm) ≪≫
    (frobeniusCoefficientTower
      (coefficientInclusion.{u} l Ω K.stage L h).toRingHom
      (frobeniusCohomologyStageEmbedding.{u, v} l Ω L)).symm.app _ ≪≫
    (frobeniusCohomologyCoefficientExtension
      (frobeniusCohomologyStageEmbedding.{u, v} l Ω L)).mapIso
      ((DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω L)).ι.mapIso
        ((frobeniusCohomologyRationalScalar D l hl
          (Coefficient.{u} l Ω K.stage) Y₀ c₀ compact (Coefficient.{u} l Ω L)
          (coefficientInclusion.{u} l Ω K.stage L h)).app K.obj)) ≪≫
    (frobeniusCohomologyCoefficientExtension
      (frobeniusCohomologyStageEmbedding.{u, v} l Ω L)).mapIso
      ((DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω L)).ι.mapIso
        ((frobeniusCohomologyRationalFunctor D l hl
          (Coefficient.{u} l Ω L) Y₀ c₀ compact).mapIso
            ((operationStageTransitionIso l Ω (D.geometricFiber Y₀).left
              K.stage L h).symm.app K.obj)))

/-- The full common-stage representative formula uniquely determines RΓ and RΓ_c.
Source: Deligne, Weil II (1.1.14), and the common-stage coefficient recipe
(blueprint: lem-weil-frobenius-cohomology-transport-iso).
Proof: send a representative f at L to comparison_K, followed by realized f,
followed by inverse comparison_M. The normalized whole-system scalar mate,
point-fibre scalar comparison and balanced tensor tower obey their coefficient
tower equations, so this formula is unchanged after further extension and
respects eventual equality. It therefore descends to the actual Pair quotient.
At a common stage inverse comparisons cancel, giving preservation of composition;
identity representatives give identity maps. Every arrow has a representative,
so the object and representative formulas determine the functor uniquely. -/
theorem frobeniusCohomologyQbarFunctor_existsUnique
    (c₀ : Compactification Y₀.hom) (compact : Bool) :
    ∃! F : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left ⥤
        @DerivedCategory (ModuleCat.{max u v} Ω) _ _ (HasDerivedCategory.standard _),
      (∀ K, F.obj K =
        (frobeniusCohomologyRealizedStage D l hl Y₀ Ω c₀ compact K.stage).obj K.obj) ∧
      (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω
          (D.geometricFiber Y₀).left)
        (L : Index l Ω) (hK : K.stage ≤ L) (hM : M.stage ≤ L)
        (f : K.toStage hK ⟶ M.toStage hM),
        HEq (F.map (StageSystem.PairCategory.mkHom L hK hM f))
          ((frobeniusCohomologyRealizedComparison D l hl Y₀ Ω c₀ compact K L hK).hom ≫
            (frobeniusCohomologyRealizedStage D l hl Y₀ Ω c₀ compact L).map f ≫
            (frobeniusCohomologyRealizedComparison D l hl Y₀ Ω c₀ compact M L hM).inv)) := by
  sorry

/-- The uniquely prescribed RΓ or RΓ_c on the entire Q̄ℓ Pair category.
Source: Deligne, Weil II (1.1.14), common-stage transport
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyQbarFunctor (c₀ : Compactification Y₀.hom) (compact : Bool) :=
  (frobeniusCohomologyQbarFunctor_existsUnique D l hl Y₀ Ω c₀ compact).exists.choose

set_option linter.defProp false in
/-- The source identification is exactly the object clause of the descent specification.
Source: Deligne, Weil II (1.1.14), common-stage transport
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyQbarSourceEq (c₀ : Compactification Y₀.hom) (compact : Bool)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  (frobeniusCohomologyQbarFunctor_existsUnique D l hl Y₀ Ω c₀ compact).exists.choose_spec.1 K

/-- The recorded common-stage geometric-Frobenius pullback, with l≠p supplying its instances.
Source: Deligne, Weil II (1.1.14), geometric pullback
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyQbarPullback :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  commonStageDerivedPullback l Ω (galois D Y₀)

set_option linter.defProp false in
/-- The target identification uses the recorded literal pullback pair and descent object clause.
Source: Deligne, Weil II (1.1.14), common-stage transport
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyQbarTargetEq (c₀ : Compactification Y₀.hom) (compact : Bool)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  (congrArg (frobeniusCohomologyQbarFunctor D l hl Y₀ Ω c₀ compact).obj
    ((commonStageDerivedPullback_existsUnique l Ω (galois D Y₀)).exists.choose_spec.1 K)).trans
      (frobeniusCohomologyQbarSourceEq D l hl Y₀ Ω c₀ compact
        (commonStagePullbackObject l Ω (galois D Y₀) K))

/-- Actual Q̄ℓ RΓ or RΓ_c map, expressed in the exact source values of the recorded transport.
Source: Deligne, Weil II (1.1.14), common-stage transport
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyQbarMap (c₀ : Compactification Y₀.hom) (compact : Bool)
    {K M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left}
    (f : K ⟶ M) :=
  eqToHom (frobeniusCohomologyQbarSourceEq D l hl Y₀ Ω c₀ compact K).symm ≫
    (frobeniusCohomologyQbarFunctor D l hl Y₀ Ω c₀ compact).map f ≫
    eqToHom (frobeniusCohomologyQbarSourceEq D l hl Y₀ Ω c₀ compact M)

/-- The same functor applied to the recorded Q̄ℓ pullback of an arbitrary Pair morphism.
The equality transports put its endpoints in the exact target values of τ.
Source: Deligne, Weil II (1.1.14), common-stage transport
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyQbarPullbackMap (c₀ : Compactification Y₀.hom) (compact : Bool)
    {K M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left}
    (f : K ⟶ M) :=
  eqToHom (frobeniusCohomologyQbarTargetEq D l hl Y₀ Ω c₀ compact K).symm ≫
    (frobeniusCohomologyQbarFunctor D l hl Y₀ Ω c₀ compact).map
      ((frobeniusCohomologyQbarPullback D l hl Y₀ Ω).map f) ≫
    eqToHom (frobeniusCohomologyQbarTargetEq D l hl Y₀ Ω c₀ compact M)

end CommonStageFunctors

section Exchanges

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

/-- The ordinary finite exchange at the actual structure map to Spec k, in the
intrinsic inverse-image coordinates used by the cohomology transport.
Source: Deligne, Weil II (1.1.14); the exchange factor in the transport definition
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyFiniteDirectExchange (n : ℕ) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  finiteExchange (Padic.coefficientExtensionRing l E (n + 1))
    (D.geometricFiber Y₀).hom (D.geometricFiber Y₀).hom
    (galois D Y₀) (frobeniusPointIso D).hom
    (D.frobenius_square_cartesian Y₀ (sfWeilCohomologyPoint D)
      (frobeniusCohomologyModelMap D Y₀)).2.2.2.2.2.2.2.w

/-- The compact finite exchange to Spec k, retaining exactly the compactification
and the middle Frobenius used by the compact cohomology transport.
Source: Deligne, Weil II (1.1.14); the compact exchange in the transport definition
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyFiniteCompactExchange (c₀ : Compactification Y₀.hom) (n : ℕ) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let F := sfIntrinsicCompactSupport (frobeniusCohomologyCompactification D Y₀ c₀)
    (Padic.coefficientExtensionRing l E (n + 1))
  let e := finiteCompact l E (n + 1) (Nat.succ_pos n)
    (frobeniusCohomologyCompactification D Y₀ c₀) (galois D Y₀)
    (galois D (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀))
    (frobeniusPointIso D).hom
    (D.frobenius_square_cartesian
      (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀)
      (sfWeilCohomologyPoint D)
      (zlCompactificationProper D (frobeniusCohomologyModelMap D Y₀) c₀)).2.2.2.2.2.2.2.w
    (D.frobenius_square_cartesian Y₀
      (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀)
      (zlCompactificationOpen D (frobeniusCohomologyModelMap D Y₀) c₀)).2.2.2.2.2.1
  Functor.whiskerLeft F (openSquareDerivedPullbackModel
      (Padic.coefficientExtensionRing l E (n + 1)) (frobeniusPointIso D).hom).inv ≫
    e ≫ Functor.whiskerRight (openSquareDerivedPullbackModel
      (Padic.coefficientExtensionRing l E (n + 1)) (galois D Y₀)).hom F

/-- The actual integral ordinary or compact exchange at a_Y, with target Spec k.
Only the inherited proof instances are installed; no exchange morphism is selected.
Source: Deligne, Weil II (1.1.14); the recorded support recipe
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyIntegralExchange (c₀ : Compactification Y₀.hom) (compact : Bool) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  modelExchange l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) E

/-- The actual rational ordinary or compact exchange at a_Y, with target Spec k.
Only the inherited proof instances are installed; no exchange morphism is selected.
Source: Deligne, Weil II (1.1.14); the recorded support recipe
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRationalExchange (c₀ : Compactification Y₀.hom) (compact : Bool) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  modelRationalExchange l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) E

/-- The common-stage exchange at a_Y, with the same actual Spec k as target.
Its components are the recorded rational exchanges at their own coefficient stage.
Source: Deligne, Weil II (1.1.14); the common-stage exchange construction
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyQbarExchange (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (c₀ : Compactification Y₀.hom) (compact : Bool) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  commonStageExchange l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) Ω

end Exchanges

/-- The canonical geometric-Frobenius transports are isomorphisms.

Source: Deligne, *La conjecture de Weil II*, (1.1.7), (1.1.10)--(1.1.14),
(blueprint: lem-weil-frobenius-cohomology-transport-iso).

Proof plan, following the node's nine steps:
1. Restriction along the point automorphism is invertible, with inverse restriction.
2. The inverse-image comma category has the initial object supplied by the inverse
   automorphism. Its coprojection is invertible; inverse image already preserves sheaves.
3. The constant-coefficient structure comparison is an isomorphism. Exact sections,
   exact inverse image and the derived localization preserve these isomorphisms.
4. Their composite is finite/integral point transport. Rationalization preserves
   isomorphisms, as do restriction to summands and common-stage coefficient extension.
5. The direct exchange is the mate of the Frobenius-square pullback isomorphism
   along the equivalences induced by the two scheme automorphisms. Apply
   lem-weil-mate-iso-along-equivalences and lem-weil-isomorphism-derived-pullback-equivalence.
6. The compact exchange is the proper direct mate followed by proper image of
   the open-square exchange. Both are isomorphisms; compactification comparisons are too.
7. Integral exchanges are induced on the Roos derived limits by the finite
   exchanges. Apply lem-weil-derived-limit-levelwise-iso. Localize for rational
   coefficients, then pass to a common coefficient stage for the algebraic closure.
8. Specialize the direct/compact exchanges to the structure map a_Y. Full
   subcategory inclusions reflect their invertibility on the constructible domain.
9. Each transport is iota followed by the point fibre of its exchange, hence an
   isomorphism. Applying H^i preserves it for every integer i. Naturality is stated
   below using the actual operation functors, and common-stage scalar compatibility.
-/
theorem frobeniusCohomologyTransport_isIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (c₀ : Compactification Y₀.hom)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω
      (D.geometricFiber Y₀).left) :
    ((∀ N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)),
        IsIso ((frobeniusCohomologyCoefficientExtension.{u, v} (N.stage.val.subtype.comp
          (Shrink.algEquiv ℚ_[l] N.stage.val).toRingHom)).map
            (frobeniusPointTransportRational D l hl
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage) N.obj).hom)) ∧
      (∀ (Ω' : Type u) [Field Ω'] [Algebra ℚ_[l] Ω'] [IsAlgClosure ℚ_[l] Ω']
        (N : generalAlgebraicallyClosedConstructibleCategory l Ω' (Spec (.of D.k))),
        IsIso (frobeniusPointTransportQbar D l hl Ω' N)) ∧
      IsIso ((frobeniusCohomologyQbarExchange D l hl Y₀ Ω c₀ false).app K) ∧
      IsIso ((frobeniusCohomologyQbarExchange D l hl Y₀ Ω c₀ true).app K) ∧
      IsIso (frobeniusCohomologyTransport D l hl Y₀ Ω c₀ K).1 ∧
      IsIso (frobeniusCohomologyTransport D l hl Y₀ Ω c₀ K).2 ∧
      ∀ i : ℤ,
        IsIso (frobeniusCohomologyMap D l hl Y₀ Ω c₀ K i).1 ∧
        IsIso (frobeniusCohomologyMap D l hl Y₀ Ω c₀ K i).2) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
        [FiniteDimensional ℚ_[l] E] (c₁ : Compactification Y₀.hom)
        (n : ℕ)
        (Kp : (intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_pos n) (Spec (.of D.k))).FullSubcategory)
        (K₁ : (intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_pos n) (D.geometricFiber Y₀).left).FullSubcategory),
        IsIso (frobeniusPointTransportFiniteConstructible D l hl E n Kp) ∧
        IsIso ((frobeniusCohomologyFiniteDirectExchange D l E Y₀ n).app K₁.obj) ∧
        IsIso ((frobeniusCohomologyFiniteCompactExchange D l E Y₀ c₁ n).app K₁.obj) ∧
        IsIso (frobeniusCohomologyTransportFinite D l hl E Y₀ c₁ n K₁).1 ∧
        IsIso (frobeniusCohomologyTransportFinite D l hl E Y₀ c₁ n K₁).2 ∧
        ∀ i : ℤ,
          IsIso (frobeniusCohomologyMapFinite D l hl E Y₀ c₁ n K₁ i).1 ∧
          IsIso (frobeniusCohomologyMapFinite D l hl E Y₀ c₁ n K₁ i).2) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
        [FiniteDimensional ℚ_[l] E] (c₁ : Compactification Y₀.hom)
        (Kp : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
        (K₁ : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left),
        IsIso (frobeniusPointTransportIntegralConstructible D l hl E Kp) ∧
        IsIso ((frobeniusCohomologyIntegralExchange D l hl E Y₀ c₁ false).app K₁) ∧
        IsIso ((frobeniusCohomologyIntegralExchange D l hl E Y₀ c₁ true).app K₁) ∧
        IsIso (frobeniusCohomologyTransportIntegral D l hl E Y₀ c₁ K₁).1 ∧
        IsIso (frobeniusCohomologyTransportIntegral D l hl E Y₀ c₁ K₁).2 ∧
        ∀ i : ℤ,
          IsIso (frobeniusCohomologyMapIntegral D l hl E Y₀ c₁ K₁ i).1 ∧
          IsIso (frobeniusCohomologyMapIntegral D l hl E Y₀ c₁ K₁ i).2) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
        [FiniteDimensional ℚ_[l] E] (c₁ : Compactification Y₀.hom)
        (Kp : sfRationalConstructibleCategory l E (Spec (.of D.k)))
        (K₁ : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left),
        IsIso (frobeniusPointTransportRational D l hl E Kp) ∧
        IsIso ((frobeniusCohomologyRationalExchange D l hl E Y₀ c₁ false).app K₁) ∧
        IsIso ((frobeniusCohomologyRationalExchange D l hl E Y₀ c₁ true).app K₁) ∧
        IsIso (frobeniusCohomologyTransportRational D l hl E Y₀ c₁ K₁).1 ∧
        IsIso (frobeniusCohomologyTransportRational D l hl E Y₀ c₁ K₁).2 ∧
        ∀ i : ℤ,
          IsIso (frobeniusCohomologyMapRational D l hl E Y₀ c₁ K₁ i).1 ∧
          IsIso (frobeniusCohomologyMapRational D l hl E Y₀ c₁ K₁ i).2) := by
  sorry

section Naturality

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

/-- The canonical finite cohomology functor before taking cohomological degree.
`compact = false` selects RΓ and `compact = true` selects RΓ_c with the retained c₀.
Source: Deligne, Weil II (1.1.14); the two composites of the transport definition
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyFiniteFunctor (c₀ : Compactification Y₀.hom) (n : ℕ)
    (compact : Bool) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  (if compact then
    sfIntrinsicCompactSupport (frobeniusCohomologyCompactification D Y₀ c₀)
      (Padic.coefficientExtensionRing l E (n + 1))
  else proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom
    (Padic.coefficientExtensionRing l E (n + 1))) ⋙
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.{u + 2, u + 1}

/-- The actual integral RΓ or RΓ_c functor used by the transport component.
Source: Deligne, Weil II (1.1.14); the retained coefficient-stage recipe
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyIntegralFunctor (c₀ : Compactification Y₀.hom) (compact : Bool) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  modelFunctor l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) E ⋙ pointIntegralFibre D l hl E

/-- The recorded integral geometric-Frobenius pullback, with prime invertibility
supplied by l ≠ p rather than by an additional hypothesis.
Source: Deligne, Weil II (1.1.14); the geometric-Frobenius convention
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyIntegralPullback :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  constructibleIntegralPullback l E (galois D Y₀)

/-- The recorded rational geometric-Frobenius pullback, with prime invertibility
supplied by l ≠ p rather than by an additional hypothesis.
Source: Deligne, Weil II (1.1.14); the geometric-Frobenius convention
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRationalPullback :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  rationalDerivedPullback l E (galois D Y₀)

/-- Naturality of both cohomology transports on the actual coefficient categories.
The rational square quantifies over every rationalized morphism. The fourth
conjunct quantifies over every morphism of the algebraically closed Pair category
and uses the recorded frobeniusCohomologyTransport itself. Its horizontal maps
are the descended RΓ/RΓ_c and geometric-pullback functors in the literal
source and target coordinates of that transport.
Source: Deligne, Weil II (1.1.14)
(blueprint: lem-weil-frobenius-cohomology-transport-iso).

Proof: apply the finite/integral/rational point-transport naturality square to
Rf_* f and Rf_! f. Paste it with the naturality square of the recorded ordinary
mate, respectively the proper mate followed by the open exchange, and apply the
point-fibre functor. The intermediate point-pullback maps cancel. Rational
pullback uses its specified integral-object equality. For algebraically closed
coefficients enlarge to a common finite stage and use the scalar-compatibility
square of point transport and the descended exchange. These identify the same
square on every representative. Applying H^i preserves the equality. -/
theorem frobeniusCohomologyTransport_natural (c₀ : Compactification Y₀.hom) :
    (∀ (n : ℕ) (K L : (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_pos n) (D.geometricFiber Y₀).left).FullSubcategory) (f : K ⟶ L),
      (frobeniusCohomologyFiniteFunctor D l E Y₀ c₀ n false).map f.hom ≫
          (frobeniusCohomologyTransportFinite D l hl E Y₀ c₀ n L).1 =
        (frobeniusCohomologyTransportFinite D l hl E Y₀ c₀ n K).1 ≫
          (frobeniusCohomologyFiniteFunctor D l E Y₀ c₀ n false).map
            ((finiteDerivedPullback l E n (galois D Y₀)).map f.hom) ∧
      (frobeniusCohomologyFiniteFunctor D l E Y₀ c₀ n true).map f.hom ≫
          (frobeniusCohomologyTransportFinite D l hl E Y₀ c₀ n L).2 =
        (frobeniusCohomologyTransportFinite D l hl E Y₀ c₀ n K).2 ≫
          (frobeniusCohomologyFiniteFunctor D l E Y₀ c₀ n true).map
            ((finiteDerivedPullback l E n (galois D Y₀)).map f.hom)) ∧
    (∀ (K L : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) (f : K ⟶ L),
      (frobeniusCohomologyIntegralFunctor D l hl E Y₀ c₀ false).map f ≫
          (frobeniusCohomologyTransportIntegral D l hl E Y₀ c₀ L).1 =
        (frobeniusCohomologyTransportIntegral D l hl E Y₀ c₀ K).1 ≫
          (frobeniusCohomologyIntegralFunctor D l hl E Y₀ c₀ false).map
            ((frobeniusCohomologyIntegralPullback D l hl E Y₀).map f) ∧
      (frobeniusCohomologyIntegralFunctor D l hl E Y₀ c₀ true).map f ≫
          (frobeniusCohomologyTransportIntegral D l hl E Y₀ c₀ L).2 =
        (frobeniusCohomologyTransportIntegral D l hl E Y₀ c₀ K).2 ≫
          (frobeniusCohomologyIntegralFunctor D l hl E Y₀ c₀ true).map
            ((frobeniusCohomologyIntegralPullback D l hl E Y₀).map f)) ∧
    (∀ (K L : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) (f : K ⟶ L),
      (frobeniusCohomologyRationalFunctor D l hl E Y₀ c₀ false).map f ≫
          (frobeniusCohomologyTransportRational D l hl E Y₀ c₀ L).1 =
        (frobeniusCohomologyTransportRational D l hl E Y₀ c₀ K).1 ≫
          (frobeniusCohomologyRationalFunctor D l hl E Y₀ c₀ false).map
            ((frobeniusCohomologyRationalPullback D l hl E Y₀).map f) ∧
      (frobeniusCohomologyRationalFunctor D l hl E Y₀ c₀ true).map f ≫
          (frobeniusCohomologyTransportRational D l hl E Y₀ c₀ L).2 =
        (frobeniusCohomologyTransportRational D l hl E Y₀ c₀ K).2 ≫
          (frobeniusCohomologyRationalFunctor D l hl E Y₀ c₀ true).map
            ((frobeniusCohomologyRationalPullback D l hl E Y₀).map f)) ∧
    (∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
      (K L : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
      (f : K ⟶ L),
      frobeniusCohomologyQbarMap D l hl Y₀ Ω c₀ false f ≫
          (frobeniusCohomologyTransport D l hl Y₀ Ω c₀ L).1 =
        (frobeniusCohomologyTransport D l hl Y₀ Ω c₀ K).1 ≫
          frobeniusCohomologyQbarPullbackMap D l hl Y₀ Ω c₀ false f ∧
      frobeniusCohomologyQbarMap D l hl Y₀ Ω c₀ true f ≫
          (frobeniusCohomologyTransport D l hl Y₀ Ω c₀ L).2 =
        (frobeniusCohomologyTransport D l hl Y₀ Ω c₀ K).2 ≫
          frobeniusCohomologyQbarPullbackMap D l hl Y₀ Ω c₀ true f) := by
  sorry

end Naturality

end WeilConjectures
