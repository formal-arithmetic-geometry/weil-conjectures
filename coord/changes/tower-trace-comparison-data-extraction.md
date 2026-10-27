# WeilConjectures.TowerTracePurityComparison presentation declarations

## Reason

The remaining normalization lemmas need the actual Stage and construction definitions.
Extract the existing definition block into TowerTracePurityComparisonData so each lemma
can have its own module without importing its consumer and creating a cycle. The item
publicly reexports that module. This changes physical declaration ownership only; every
name, signature, body, visibility and normalized construction stays the same. Docstring
blueprint tags now point to the data node. No target meaning changes.

## Old

In lean/Sheaf/Paper/TowerTracePurityComparison.lean, the following definition block:

```lean
/-- The base field Q_l in the fixed closure, without a new coefficient choice.
Source: purity transport, base coefficient field
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def base : FieldShriekSystem.Index P := ⟨⊥, inferInstance⟩

variable {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))]
  (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]

section QuasiCompactHelpers
variable [QuasiCompact (j ≫ p)]
  (S : ConstructibleExceptionalCoefficients.RingSystem P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := j ≫ p))

/-- Presentation certificates for the actual maps at one finite coefficient field.
The tower realization is the existing integral model; tensor and unit comparisons
are fixed on K-flat representatives. No purity comparison is a field of this record.
Source: tower gamma (1)--(2), realization and projection formula
(blueprint: lem-pur-tower-trace-purity-comparison). -/
structure Stage (M : FieldShriekSystem.Models P) (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P M E j p d) where
  supportClosed : ∀ A : finiteTorConstructibleIntegralCategory P.coefficients.l E.val X,
    finiteTorConstructibleIntegral P.coefficients.l E.val Y
      ((CompleteCompactificationLimit.image P.coefficients.l E.val
        (SpTowerGamma.factorization j p)).obj A.obj)
  rightClosed : ∀ K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y,
    finiteTorConstructibleIntegral P.coefficients.l E.val X
      ((FieldExtensionTowers.exceptional P M j p d m).obj
        ((PurCompactSupport.finiteTorIntegralInclusion P.coefficients.l E.val Y).obj K)).obj
  core : CompletedUnitPullback.Core P.coefficients.l E.val (j ≫ p)
  normal : RealizedTowerPurity.FiniteNormalization P.field P.coefficients E.val
    (j ≫ p) S (SpTowerGamma.factorization j p)
  lineTor : finiteTorConstructibleIntegral P.coefficients.l E.val X
    (PurUnitTrace.tateUnit P.field P.coefficients E.val d X)
  coefficients : PurAdicScalarTrace.CoefficientComparison P.coefficients.l
    (base P).val E.val (IntermediateField.inclusion bot_le) P.field P.coefficients.different
      (SpTowerGamma.factorization j p) d
  models : RingedModels P.coefficients.l E.val
  openComparison : RingedOpenComparisons P.coefficients.l E.val models
  lineFlat : (PurUnitTrace.lineComplex P.field P.coefficients E.val d X
    ).IsKFlatIndependentCoefficients
  unitFlat : (PurUnitTrace.unitComplex P.field P.coefficients E.val Y
    ).IsKFlatIndependentCoefficients
  unitIso : integralConstantCoefficientObject P.coefficients.l E.val Y ≅
    (calculus P.coefficients.l E.val Y).integralClosed.monoidal.tensorUnit
  unitNormalized : PurUnitTrace.IsUnitNormalized P.field P.coefficients E.val Y unitFlat unitIso
  tensorSource : PurUnitTrace.sourceRestricted P.field P.coefficients E.val (j ≫ p) d ≅
    PurUnitTrace.tensorFunctor P.field P.coefficients E.val (j ≫ p) d
  sourceNormalized : PurUnitTrace.IsJNormalized P.field P.coefficients E.val (j ≫ p) d
    models lineFlat tensorSource
  tensorTor : ∀ K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y,
    finiteTorConstructibleIntegral P.coefficients.l E.val X
      ((PurUnitTrace.tensorFunctor P.field P.coefficients E.val (j ≫ p) d).obj K)
  completionIso : ∀ K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y,
    IsIso (((models.tensor Y).chi P.coefficients.l E.val).app
      ((PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l E.val)
        (SpTowerGamma.factorization j p)).obj
          (PurUnitTrace.tateUnit P.field P.coefficients E.val d X), K.obj))
  projectionIso : ∀ K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y,
    IsIso (adicProjection P.coefficients.l E.val models openComparison
      (SpTowerGamma.factorization j p)
      (PurUnitTrace.tateUnit P.field P.coefficients E.val d X) K.obj (completionIso K))

variable (M : FieldShriekSystem.Models P) (E : FieldShriekSystem.Index P)
  (m : FieldExtensionTowers.IntegralModel P M E j p d) (A : Stage P j p d S M E m)

/-- Rlim of the actual whole-tower gamma, followed by the unique counit-preserving
comparison with the specified exceptional functor, in normalized source coordinates.
Source: displayed definition of gamma^T
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def tower (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :
    purAdicSource P.field P.coefficients E.val (j ≫ p) d K.obj ⟶
      ((S.operation (SpTowerGamma.factorization j p) (.integral { carrier := E.val })).G.obj
        K).obj :=
  m.sourceNormalization.exactSource.hom.app
      ((PurCompactSupport.finiteTorIntegralInclusion P.coefficients.l E.val Y).obj K) ≫
    AlgebraicGeometry.ProEtale.RealizedTowerPurity.component P.coefficients.l E.val
      (M.base E) (M.operations E) (M.coordinates E) j p d m.twists
      m.reductionX m.normalizationX m.reductionY m.normalizationY m.supportClosed m.exceptional
      m.adjunction m.levels m.realization
      A.rightClosed A.supportClosed
      (S.operation (SpTowerGamma.factorization j p) (.integral { carrier := E.val })).G
      (WeilConjectures.RealizedTowerPurity.specifiedAdjunction P.field P.coefficients E.val
        (j ≫ p) S (SpTowerGamma.factorization j p) A.supportClosed) K

/-- The tower orientation at the coefficient unit, with its canonical pulled-unit
source identification. Source: a^T = gamma^T_1
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def orientation : PurUnitTrace.tateUnit P.field P.coefficients E.val d X ⟶
    ((S.operation (SpTowerGamma.factorization j p) (.integral { carrier := E.val })).G.obj
      ⟨_, A.core.admissibleY.1⟩).obj :=
  (PurUnitTrace.sourceUnitIso P.field P.coefficients E.val (j ≫ p) d A.core).inv ≫
    tower P j p d S M E m A ⟨_, A.core.admissibleY.1⟩

/-- Compact support followed by the specified counit: epsilon P(g).
Source: the definitions of t_0 and of the tower unit trace
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def counitTrace (g : PurUnitTrace.tateUnit P.field P.coefficients E.val d X ⟶
    ((S.operation (SpTowerGamma.factorization j p) (.integral { carrier := E.val })).G.obj
      ⟨_, A.core.admissibleY.1⟩).obj) :
    (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l E.val)
      (SpTowerGamma.factorization j p)).obj
        (PurUnitTrace.tateUnit P.field P.coefficients E.val d X) ⟶
      integralConstantCoefficientObject P.coefficients.l E.val Y :=
  (S.left (SpTowerGamma.factorization j p) (.integral { carrier := E.val })).inv.app
      ⟨_, A.lineTor⟩ ≫
    ((S.operation (SpTowerGamma.factorization j p) (.integral { carrier := E.val })).F.map
      (ObjectProperty.homMk g)).hom ≫
    ((S.operation (SpTowerGamma.factorization j p) (.integral { carrier := E.val }
      )).adjunction.counit.app ⟨_, A.core.admissibleY.1⟩).hom

/-- Ordinary derived coefficient extension of t_0, with inverse compact-support
and twist comparisons and the normalized coefficient-unit multiplication.
Source: the displayed formula for t_E
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def extendedTrace
    (t0 : (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l (base P).val)
      (SpTowerGamma.factorization j p)).obj
        (PurUnitTrace.tateUnit P.field P.coefficients (base P).val d X) ⟶
      integralConstantCoefficientObject P.coefficients.l (base P).val Y) :=
  (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l E.val)
      (SpTowerGamma.factorization j p)).map
        (PurUnitTrace.twistedUnitIso P.field P.coefficients E.val d X).inv ≫
    PurAdicScalarTrace.trace P.coefficients.l (base P).val E.val
      (IntermediateField.inclusion bot_le) P.field P.coefficients.different
      (SpTowerGamma.factorization j p) d A.coefficients
      ((PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l (base P).val)
        (SpTowerGamma.factorization j p)).map
          (PurUnitTrace.twistedUnitIso P.field P.coefficients (base P).val d X).hom ≫ t0)

/-- Transpose inverse projection followed by t tensor identity. The normalized
source symmetry converts this to (identity tensor t) Pi in the node's convention.
Source: the definition of gamma^tr
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def tracePurity
    (t : (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l E.val)
      (SpTowerGamma.factorization j p)).obj
        (PurUnitTrace.tateUnit P.field P.coefficients E.val d X) ⟶
      integralConstantCoefficientObject P.coefficients.l E.val Y)
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :=
  A.tensorSource.hom.app K ≫
    adicTranspose P.field P.coefficients E.val (j ≫ p) S (SpTowerGamma.factorization j p)
      ⟨_, A.tensorTor K⟩ K
      (adicTraceMap P.coefficients.l E.val A.models A.openComparison
        (SpTowerGamma.factorization j p)
        (PurUnitTrace.tateUnit P.field P.coefficients E.val d X) K.obj
        (A.completionIso K) (A.projectionIso K) (t ≫ A.unitIso.hom))

/-- The base lift has exactly the prescribed finite unit purity reductions, using
the counit-normalized exceptional comparison at the chosen compactification.
Source: the hypothesis on g_0
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def PrescribedUnitReductions
    (g : PurUnitTrace.tateUnit P.field P.coefficients E.val d X ⟶
      ((S.operation (SpTowerGamma.factorization j p) (.integral { carrier := E.val })).G.obj
        ⟨_, A.core.admissibleY.1⟩).obj) : Prop :=
  ∀ n : ℕ,
    (scalarReductionDerivedExtension P.coefficients.l E.val X n).map
      ((PurUnitTrace.sourceUnitIso P.field P.coefficients E.val (j ≫ p) d A.core).hom ≫ g) ≫
        WeilConjectures.RealizedTowerPurity.finiteReduction P.field P.coefficients E.val
          (j ≫ p) S (SpTowerGamma.factorization j p) A.normal
          ⟨_, A.core.admissibleY.1⟩ n =
      purAdicSourceReduction P.field P.coefficients E.val (j ≫ p) d
          (integralConstantCoefficientObject P.coefficients.l E.val Y) A.core.admissibleY.1 n ≫
        (purAdicFiniteArrow P.field P.coefficients E.val (j ≫ p) d
          (integralConstantCoefficientObject P.coefficients.l E.val Y)
            A.core.admissibleY.1 n).hom

/-- The integral source, in the existing complete constructible full subcategory.
Its membership is the source clause of adic reconstruction.
Source: the common finite-Tor convention
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def sourceObject (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :
    sfIntegralConstructibleCategory P.coefficients.l E.val X :=
  ⟨purAdicSource P.field P.coefficients E.val (j ≫ p) d K.obj,
    (purAdicReconstruction P.field P.coefficients E.val (j ≫ p) d
      K.obj K.property).choose_spec.2.1.1⟩

/-- The specified exceptional target, included in the same integral category.
Source: the specified exceptional adjunction
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def targetObject (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :
    sfIntegralConstructibleCategory P.coefficients.l E.val X :=
  (PurCompactSupport.finiteTorIntegralInclusion P.coefficients.l E.val X).obj
    ((S.operation (SpTowerGamma.factorization j p) (.integral { carrier := E.val })).G.obj K)

/-- Literal scalar localization of the realized tower morphism.
Source: the displayed rational equality, Q_E(gamma^T)
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def rationalTower (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :=
  (sfRationalConstructibleLocalization P.coefficients.l E.val X).map
    (ObjectProperty.homMk (tower P j p d S M E m A K) :
      sourceObject P j p d E K ⟶ targetObject P j p S E K)

/-- The localized trace-transpose representative of the specified rational family.
The source and target identifications have already been inserted in the integral map.
Source: purity transport Steps 1--2, the integral-representative convention
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def rationalTrace
    (t : (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l E.val)
      (SpTowerGamma.factorization j p)).obj
        (PurUnitTrace.tateUnit P.field P.coefficients E.val d X) ⟶
      integralConstantCoefficientObject P.coefficients.l E.val Y)
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :=
  (sfRationalConstructibleLocalization P.coefficients.l E.val X).map
    (ObjectProperty.homMk (tracePurity P j p d S M E m A t K) :
      sourceObject P j p d E K ⟶ targetObject P j p S E K)

end QuasiCompactHelpers

/-- Change only the finite field in the existing coefficient setting.
Source: coefficient-field conventions, all finite subfields in the fixed closure
(blueprint: lem-pur-tower-trace-purity-comparison). -/
@[reducible] def atField (F : FieldShriekSystem.Index P) : PurityFiniteSetting.{u} :=
  { P with extension := F.val, finiteExtension := inferInstance }

/-- The canonical small coefficient model followed by the actual common-stage inclusion.
The transport is the recorded Shrink algebra equivalence, with no universe restriction.
Source: the final common-stage assertion
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def commonImage (F : FieldShriekSystem.Index P) (W : Scheme.{u}) :=
  AdicSmoothDualizing.modelScalar (atField P F) W ⋙
    AdicSmoothDualizing.commonInclusion (atField P F) W

attribute [local irreducible] sfRationalScalarExtension rationalDerivedPullback
  rationalDerivedTensor ScalarLocalization.category

section RationalComparisons
variable [QuasiCompact (j ≫ p)] [IsSeparated (j ≫ p)] [LocallyOfFiniteType (j ≫ p)]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := j ≫ p))
  (M : FieldShriekSystem.Models P) (E : FieldShriekSystem.Index P)
  (m : FieldExtensionTowers.IntegralModel P M E j p d)
  (A : Stage P j p d S.ring M E m)

/-- The actual rationalization of the finite-Tor input, in the specified field stage.
Source: rational purity transport Step 1, Q_E K
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def rationalInput (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :=
  (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
    (AdicSmoothDualizing.fieldStage (atField P E)) Y).obj K

/-- Localize the inverse K-flat-normalized tensor-source comparison. Its source is
exactly the integral representative used by the previously specified rational family.
Source: rational purity transport Step 1, canonical source identification
(blueprint: lem-pur-tower-trace-purity-comparison). -/
@[irreducible] def normalizedRationalSource
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :
    (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage (atField P E)) X).obj
        (RationalSmoothPurityCanonical.integralSource (atField P E) (j ≫ p) d
          (RationalSmoothPurityCanonical.representative (atField P E) (rationalInput P E K))) ⟶
      (sfRationalConstructibleLocalization P.coefficients.l E.val X).obj
        (sourceObject P j p d E K) :=
  (sfRationalConstructibleLocalization P.coefficients.l E.val X).map
    (ObjectProperty.homMk (A.tensorSource.inv.app K))

/-- The localized actual tower map with the specified rational family's source and
counit-preserving target comparisons, including the literal representative transport.
Source: rational purity transport Steps 1--2, the displayed rational equality
(blueprint: lem-pur-tower-trace-purity-comparison). -/
@[irreducible] def rationalTowerComponent
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :
    (RationalSmoothPurityCanonical.rationalSource P.coefficients.l E.val (j ≫ p) d).obj
        (rationalInput P E K) ⟶
      (S.ring.operation (SpTowerGamma.factorization j p)
        (.rational (AdicSmoothDualizing.fieldStage (atField P E)))).G.obj (rationalInput P E K) :=
  (RationalSmoothPurityCanonical.rationalSourceComparison (atField P E) (j ≫ p) d
      (rationalInput P E K)).hom ≫
    normalizedRationalSource P j p d S M E m A K ≫
    rationalTower P j p d S.ring M E m A K ≫
    (S.fields.rationalizationComparison (SpTowerGamma.factorization j p)
      (AdicSmoothDualizing.fieldStage (atField P E))).b.hom.app
        (RationalSmoothPurityCanonical.representative (atField P E) (rationalInput P E K)) ≫
    (S.ring.operation (SpTowerGamma.factorization j p)
      (.rational (AdicSmoothDualizing.fieldStage (atField P E)))).G.map
        (eqToHom (RationalSmoothPurityCanonical.representative_eq (atField P E)
          (rationalInput P E K)))

end RationalComparisons

/-- The comparison assertion on the standing finite-type schemes. Geometric instances
are derived here, so quasi-compactness of f is not an additional hypothesis.
Source: the setting and all four conclusions
(blueprint: lem-pur-tower-trace-purity-comparison). -/
def Comparison : Prop :=
  letI : CompactSpace X := FieldExtensionTowers.compactSpace P X
  letI : QuasiSeparatedSpace Y := FieldExtensionTowers.quasiSeparatedSpace P Y
  letI : QuasiCompact (j ≫ p) := inferInstance
  letI : IsSeparated (j ≫ p) := inferInstance
  letI : LocallyOfFiniteType (j ≫ p) := inferInstance
  letI : ∀ x : X, Invertible (P.coefficients.l : X.residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients X x).invertible
  letI : ∀ y : Y, Invertible (P.coefficients.l : Y.residueField y) :=
    fun y ↦ (purAdicResidueUnit P.field P.coefficients Y y).invertible
  ∀ S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := j ≫ p),
    ∃ (M : FieldShriekSystem.Models P)
      (R : FieldExtensionTowers.Result P M j p d)
      (A : ∀ E : FieldShriekSystem.Index P, Stage P j p d S.ring M E (R.model E)),
      (∀ E : FieldShriekSystem.Index P,
        PrescribedUnitReductions P j p d S.ring M E (R.model E) (A E)
          (orientation P j p d S.ring M E (R.model E) (A E)) ∧
        IsIso (orientation P j p d S.ring M E (R.model E) (A E))) ∧
      ∀ g0 : PurUnitTrace.tateUnit P.field P.coefficients (base P).val d X ≅
          ((S.ring.operation (SpTowerGamma.factorization j p)
            (.integral { carrier := (base P).val })).G.obj
              ⟨_, (A (base P)).core.admissibleY.1⟩).obj,
        PrescribedUnitReductions P j p d S.ring M (base P) (R.model (base P)) (A (base P))
          g0.hom →
        g0.hom = orientation P j p d S.ring M (base P) (R.model (base P)) (A (base P)) ∧
        (∀ E : FieldShriekSystem.Index P,
          extendedTrace P j p d S.ring M E (R.model E) (A E)
              (counitTrace P j p d S.ring M (base P) (R.model (base P)) (A (base P)) g0.hom) =
            counitTrace P j p d S.ring M E (R.model E) (A E)
              (orientation P j p d S.ring M E (R.model E) (A E))) ∧
        ∀ (E : FieldShriekSystem.Index P)
          (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y),
          tracePurity P j p d S.ring M E (R.model E) (A E)
              (extendedTrace P j p d S.ring M E (R.model E) (A E)
                (counitTrace P j p d S.ring M (base P) (R.model (base P)) (A (base P)) g0.hom)) K =
            tower P j p d S.ring M E (R.model E) (A E) K ∧
          (RationalSmoothPurityCanonical.rationalIso (atField P E) (j ≫ p)
            (SpTowerGamma.factorization j p) S d (rationalInput P E K)).hom =
              rationalTowerComponent P j p d S M E (R.model E) (A E) K ∧
          ∀ (F : FieldShriekSystem.Index P) (h : E ≤ F),
            (commonImage P F X).map
              ((RationalSmoothPurityCanonical.sourceScalar P.coefficients.l E.val F.val
                  (IntermediateField.inclusion h) (j ≫ p) d (rationalInput P E K)).hom ≫
                (RationalSmoothPurityCanonical.rationalIso (atField P F) (j ≫ p)
                  (SpTowerGamma.factorization j p) S d
                  ((ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
                    P.coefficients.Qbar (AdicSmoothDualizing.fieldStage (atField P E))
                    (AdicSmoothDualizing.fieldStage (atField P F))
                    (IntermediateField.inclusion h) Y).obj (rationalInput P E K))).hom) =
              (commonImage P F X).map
                ((ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
                  P.coefficients.Qbar (AdicSmoothDualizing.fieldStage (atField P E))
                  (AdicSmoothDualizing.fieldStage (atField P F))
                  (IntermediateField.inclusion h) X).map
                    (rationalTowerComponent P j p d S M E (R.model E) (A E) K) ≫
                  (S.fields.rationalComparison (SpTowerGamma.factorization j p)
                    (AdicSmoothDualizing.fieldStage (atField P E))
                    (AdicSmoothDualizing.fieldStage (atField P F))
                    (IntermediateField.inclusion h)).b.hom.app (rationalInput P E K))

```

## New

The identical block (above, including every definition body) is in
lean/Sheaf/Paper/TowerTracePurityComparisonData.lean. The sole textual differences
inside that block are the blueprint tags, from
lem-pur-tower-trace-purity-comparison to def-pur-tower-trace-comparison-data.
The original module publicly imports the data module:

```lean
public import Sheaf.Paper.TowerTracePurityComparisonData
```

The data module keeps all seven original public imports. It contains no sorry.
The original theorem signature remains verbatim:

```lean
theorem tower_trace_purity_comparison : Comparison P j p d
```

## Users

Read-only tools/downstream.py reports zero downstream modules. A declaration search
for Stage reports only the item's own module. No existing consumer requires adaptation.
All new consumers are in this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.TowerTracePurityComparison | P4 | Reexports definitions and proves assembly |
| Sheaf.Paper.TowerTraceNormalizedPresentations | P4, new | States the normalized presentation bridge |
| Sheaf.Paper.TowerTraceOrientationUniqueness | P4, new | States rank-one uniqueness in Stage coordinates |
| Sheaf.Paper.TowerTraceScalarCounit | P4, new | States scalar counit compatibility |
| Sheaf.Paper.TowerTraceCanonicalIntegral | P4, new | States ordinary/completed transpose comparison |

## Status

landed 20261026T070501-L-3596498 2026-10-26 (merge of deliver/P4/Sheaf.Paper.TowerTracePurityComparison)
