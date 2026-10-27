# WeilConjectures.FdCompletionIntegralComparison and FdCompletionScalarComparison

## Reason

The server diagnostic completed the original structure declarations and the new proof,
but rejected the 127-second file against the 60-second limit. Profiling identified
repeated kernel checking of the expanded chi, shift, lift and exactness predicates
in generated constructors and recursors. Name those predicates as real definitions
and mark them locally irreducible; retain their exact bodies. No data or proposition changes. The profiling also measured 26 seconds in redundant
local linting, which is disabled for this module after explicitly checking the former
unused-binder warnings and the formatting. Kernel proof checking remains enabled.
The family category arguments are made explicit to avoid elaborator reconstruction.
No source-library file changes.

## Old

```lean
structure FdCompletionIntegralComparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) where
  ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h
  comparison : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
          integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
            pbcAmbientScalarExtension l Ω T h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T E L h ⋙
          (sfIntegralConstructible l (pbcFiniteField.{u} l Ω L) T).ι ⋙
            integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)
  chi : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
      (DerivedCategory.Q.obj P.obj)),
    HEq ((comparison h).hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
      (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
        ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
      (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
        ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj))
      ((pbcAmbientScalarExtension l Ω T h).map
        ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P.obj) ≫
      pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
        (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
          (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map ((ordinary h).completion l Ω P.obj))
  integral : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (stage E).integral.functor ⋙ pbcIntegralScalarExtension l Ω T dT.out iT.out h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T E L h ⋙
          (stage L).integral.functor
  restriction : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      HEq ((integral h).hom.app K).hom ((comparison h).hom.app K)

/-- Coherence data for the specified integral comparison and its rationalized inverse.
The stage-system components are identified with the supplied raw identity equivalences;
only presentation transport is expressed by heterogeneous equality.
Source: trace-definition final sentence, comparison steps 1--8
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
structure FdCompletionScalarComparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) where
  integral : FdCompletionIntegralComparison l Ω T stage
  family : StageSystem.Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out)
  finite_functor : ∀ E, HEq (family.Φ E) (stage E).rational.functor
  [finite_shift : ∀ E, (family.Φ E).CommShift ℤ]
  finite_shift_normalization : ∀ E (n : ℤ),
    HEq ((family.Φ E).commShiftIso n) ((stage E).rational.functor.commShiftIso n)
  scalar_lift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
    (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
    HEq ((family.β h).hom.app K')
      ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app
          ((stage E).integral.functor.obj K) ≫
        (pbcStageLocalization l Ω T L).map ((integral.integral h).hom.app K))
  scalar_shift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    NatTrans.CommShift (family.β h).hom ℤ ∧ NatTrans.CommShift (family.β h).inv ℤ
  exact : ∀ E, (family.Φ E).IsTriangulated
  unit : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq ((family.β (le_refl E)).inv.app K)
      ((family.Φ E).map
        ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω T E).hom.app K))
  coherence : FdInverseScalarCoherence family
```

## New

```lean
/-- The existing ordinary family, named to share its type across structure declarations.
Source: integral comparison data (blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionOrdinaryFamily
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
 :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h

/-- The existing comparison family, named to share its type across structure declarations.
Source: integral comparison data (blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionAmbientFamily
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
 :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
          integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
            pbcAmbientScalarExtension l Ω T h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T E L h ⋙
          (sfIntegralConstructible l (pbcFiniteField.{u} l Ω L) T).ι ⋙
            integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)

/-- The existing integral family, named to share its type across structure declarations.
Source: integral comparison data (blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionIntegralFamily
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (stage E).integral.functor ⋙ pbcIntegralScalarExtension l Ω T dT.out iT.out h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T E L h ⋙
          (stage L).integral.functor

/-- The existing quotient-cocone equation, named to keep generated structure recursors
from repeatedly expanding the derived coefficient presentations.
Source: the chi field below (blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionChi
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [_dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [_iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (ordinary : FdCompletionOrdinaryFamily l Ω T)
    (comparison : FdCompletionAmbientFamily l Ω T) : Prop :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
      (DerivedCategory.Q.obj P.obj)),
    HEq ((comparison h).hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
      (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
        ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
      (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
        ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj))
      ((pbcAmbientScalarExtension l Ω T h).map
        ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P.obj) ≫
      pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
        (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
          (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map ((ordinary h).completion l Ω P.obj))

attribute [local irreducible] FdCompletionChi

attribute [local irreducible] AlgebraicGeometry.Scheme.integralDetailedTransport

/-- The original ambient restriction equation.
Source: integral comparison data (blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionRestriction
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (comparison : FdCompletionAmbientFamily l Ω T)
    (integral : FdCompletionIntegralFamily l Ω T stage) : Prop :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      HEq ((integral h).hom.app K).hom ((comparison h).hom.app K)

attribute [local irreducible] FdCompletionRestriction FdCompletionOrdinaryFamily
  FdCompletionAmbientFamily FdCompletionIntegralFamily

/-- The quotient-normalized integral comparison retained by the scalar-coherence theorem.
This records exactly the tensor transport and chi lift of the coefficient datum, without
its downstream rational or pair-category conclusions.
Source: trace-definition final sentence, comparison steps 1--3
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
structure FdCompletionIntegralComparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) where
  ordinary : FdCompletionOrdinaryFamily l Ω T
  comparison : FdCompletionAmbientFamily l Ω T
  chi : FdCompletionChi l Ω T (@ordinary) (@comparison)
  integral : FdCompletionIntegralFamily l Ω T stage
  restriction : FdCompletionRestriction l Ω T stage comparison integral

attribute [local semireducible] FdCompletionOrdinaryFamily FdCompletionAmbientFamily
  FdCompletionIntegralFamily

/-- The existing finite_functor predicate, shared by the constructor and projections.
Source: the corresponding scalar-comparison field
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionFiniteFunctor
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out)) : Prop :=
  ∀ E, HEq (family.Φ E) (stage E).rational.functor

attribute [local irreducible] FdCompletionFiniteFunctor

/-- The existing finite_shift_normalization predicate, shared by the constructor and projections.
Source: the corresponding scalar-comparison field
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionShiftNormalization
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out))
    [s : ∀ E, (family.Φ E).CommShift ℤ] : Prop :=
  ∀ E (n : ℤ),
    HEq ((family.Φ E).commShiftIso n) ((stage E).rational.functor.commShiftIso n)

attribute [local irreducible] FdCompletionShiftNormalization

/-- The existing scalar_lift predicate, shared by the constructor and projections.
Source: the corresponding scalar-comparison field
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionScalarLift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (integral : FdCompletionIntegralComparison l Ω T stage)
    (family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out)) : Prop :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
    (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
    HEq ((family.β h).hom.app K')
      ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app
          ((stage E).integral.functor.obj K) ≫
        (pbcStageLocalization l Ω T L).map ((integral.integral h).hom.app K))

attribute [local irreducible] FdCompletionScalarLift

/-- The existing scalar_shift predicate, shared by the constructor and projections.
Source: the corresponding scalar-comparison field
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionScalarShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (_stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out))
    [s : ∀ E, (family.Φ E).CommShift ℤ] : Prop :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    NatTrans.CommShift (family.β h).hom ℤ ∧ NatTrans.CommShift (family.β h).inv ℤ

attribute [local irreducible] FdCompletionScalarShift

/-- The existing exact predicate, shared by the constructor and projections.
Source: the corresponding scalar-comparison field
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionExact
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (_stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out))
    [s : ∀ E, (family.Φ E).CommShift ℤ] : Prop :=
  ∀ E, (family.Φ E).IsTriangulated

attribute [local irreducible] FdCompletionExact

/-- The existing unit predicate, shared by the constructor and projections.
Source: the corresponding scalar-comparison field
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionUnit
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (_stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out)) : Prop :=
  ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq ((family.β (le_refl E)).inv.app K)
      ((family.Φ E).map
        ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω T E).hom.app K))

attribute [local irreducible] FdCompletionUnit

/-- Coherence data for the specified integral comparison and its rationalized inverse.
The stage-system components are identified with the supplied raw identity equivalences;
only presentation transport is expressed by heterogeneous equality.
Source: trace-definition final sentence, comparison steps 1--8
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
structure FdCompletionScalarComparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) where
  integral : FdCompletionIntegralComparison l Ω T stage
  family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out)
  finite_functor : FdCompletionFiniteFunctor l Ω T stage family
  [finite_shift : ∀ E, (family.Φ E).CommShift ℤ]
  finite_shift_normalization : FdCompletionShiftNormalization l Ω T stage family
  scalar_lift : FdCompletionScalarLift l Ω T stage integral family
  scalar_shift : FdCompletionScalarShift l Ω T stage family
  exact : FdCompletionExact l Ω T stage family
  unit : FdCompletionUnit l Ω T stage family
  coherence : FdInverseScalarCoherence family
```

Irreducibility is local to this module; exported definitions have ordinary reducibility.
The predicates unfold to precisely the old field types. The main theorem signature
is unchanged. The eleven helper definitions have no sorry, choice or new data.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FdCompletionInverseScalarCoherence | H1 | Field proofs explicitly unfold the predicates. |
| Sheaf.Paper.AdicFiniteRealizationCocone | unclaimed in local records | Stores the comparison and uses family only; no changed predicate is applied. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed in local records | Invokes the unchanged theorem and passes its proof fields to the finite comparison; consumer compilation checks transparency. |

This is the complete declaration-use list from tools/downstream.py --uses for the
two structures and theorem (620 transitive importers). No consumer source is changed.

An earlier revision compiled in 53.1 seconds; delivery revalidation varied to 66 seconds,
so the comparison family types and restriction predicate are now named as well. The unchanged
RationalCoefficientCategoryComparison consumer compiled in 15.2 seconds against
the sandbox interface; no source adaptation is necessary.

The matched chi-family interface compiled cleanly in 43.5 seconds.

## Status

landed 20261025T202130-L-2677643 2026-10-25 (merge of deliver/H1/Sheaf.Paper.FdCompletionInverseScalarCoherence)
