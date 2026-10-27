# WeilConjectures.PointTransformationDescent: canonical coefficient helpers

## Reason

The parent descent theorem uses the canonical small coefficient fields `Coefficient.{u} l Ω F = Shrink F.val`. Two stated dependencies used literal subfields instead, so the supplied family could not be passed to them. Align their indexed assertions with the prescribed small fields and conjugated inclusions. This is transport along the canonical algebra equivalences, with no new hypothesis.

The first complete assembly exceeded the 60-second compile limit. A profiler probe showed Lean unfolding duplicated integral/rational helpers through derived localizations and size transports while matching interfaces. Replace the duplicate helpers by abbreviations of their existing owners. The common-stage owner is `PointRationalFamilyCommonStageNaturality`; the integral owner is `PointTransformationRationalNormalization`. Every alias expands to the original construction. No natural transformation components, comparisons, or transport maps are chosen or replaced. This follows the one-definition-per-notion requirement.

## Old

```lean
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PointFdQbarCategory
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PointSectionsScalarExtension
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.PointFibreDerivedTensorBasic
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.IntegralScalarExtensionUniverses

def integralSections (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
    pointCompletedDerivedSections D.k l E

def integralPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  constructibleIntegralPullback l E g

def rationalPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  rationalDerivedPullback l E g

def commonPullback :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  commonStageDerivedPullback l Ω g

def pullbackObject (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  commonStagePullbackObject l Ω g A

def integralAlpha (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  integralPullbackScalarComparison l E L ι g K

def integralPhi (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  pointSectionsScalarExtensionIso l E L ι D hl K.obj
    ((pointIntegralConstructible_iff l E D hl K.obj).mpr K.property)

def rationalB (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  (pointRationalFibre D l hl L).mapIso
      ((rationalPullbackScalarComparison l E L ι g).app K).symm ≪≫
    (pointRationalFibreScalarIso D l hl E L ι).app
      ((rationalPullback D l hl g E).obj K)

def IntegralFamily :=
  ∀ F : Index l Ω,
    integralSections D l (Coefficient.{u} l Ω F) ⟶
      integralPullback D l hl g (Coefficient.{u} l Ω F) ⋙
        integralSections D l (Coefficient.{u} l Ω F)

def IntegralCompatible (η : IntegralFamily D l hl Ω g) : Prop :=
  ∀ (F G : Index l Ω) (h : F ≤ G)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (η G).app ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω F)
        (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F G h) (Spec (.of D.k))).obj K) ≫
      (integralSections D l (Coefficient.{u} l Ω G)).map
        (integralAlpha D l hl g _ _ (coefficientInclusion l Ω F G h) K).inv ≫
      (integralPhi D l hl _ _ (coefficientInclusion l Ω F G h)
        ((integralPullback D l hl g (Coefficient.{u} l Ω F)).obj K)).hom =
    (integralPhi D l hl _ _ (coefficientInclusion l Ω F G h) K).hom ≫
      (pointIntegralModuleDerivedTensor l _ _ (coefficientInclusion l Ω F G h)).map
        ((η F).app K)

def RationalFamily :=
  ∀ F : Index l Ω,
    pointRationalFibre D l hl (Coefficient.{u} l Ω F) ⟶
      rationalPullback D l hl g (Coefficient.{u} l Ω F) ⋙
        pointRationalFibre D l hl (Coefficient.{u} l Ω F)

def RationalNormalized (η : IntegralFamily D l hl Ω g)
    (t : RationalFamily D l hl Ω g) : Prop :=
  ∀ (F : Index l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    HEq
      ((pointRationalNormalization D l hl _ K).inv ≫
        (ModuleCat.uliftFunctor.{u + 1, u} (Coefficient.{u} l Ω F)).mapDerivedCategory.map
          ((t F).app K).hom ≫
        (pointRationalNormalization D l hl _
          ((rationalPullback D l hl g (Coefficient.{u} l Ω F)).obj K)).hom)
      ((pointModuleDerivedRationalization l (Coefficient.{u} l Ω F)).map ((η F).app K.obj))

def RationalCompatible (t : RationalFamily D l hl Ω g) : Prop :=
  ∀ (F G : Index l Ω) (h : F ≤ G)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (t G).app ((sfRationalScalarExtension l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h)).obj K) ≫
      (rationalB D l hl g _ _ (coefficientInclusion l Ω F G h) K).hom =
    (pointRationalFibreScalarIso D l hl _ _ (coefficientInclusion l Ω F G h)).hom.app K ≫
      (DerivedCategory.pointFdScalarExtension (coefficientInclusion l Ω F G h).toRingHom).map
        ((t F).app K)

def pullbackComparison
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  commonStagePullbackComparison l Ω g A N h

def stageB
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  (pointStageFibre D l hl Ω N).mapIso (pullbackComparison D l hl Ω g A N h).symm ≪≫
    (pointStageFibreScalarIso D l hl Ω A.stage N h).app
      (pullbackObject D l hl Ω g A).obj

def stageComponent (t : RationalFamily D l hl Ω g)
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  (DerivedCategory.pointFdScalarExtension
    (Shrink.algEquiv ℚ_[l] A.stage.val).toRingHom).map ((t A.stage).app A.obj)

def componentAt (t : RationalFamily D l hl Ω g)
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom).map
    (stageComponent D l hl Ω g t A)

def fibreArrow :=
  (pointStageFibreScalarIso D l hl Ω A.stage N hA).inv.app A.obj ≫
    (pointStageFibre D l hl Ω N).map f ≫
    (pointStageFibreScalarIso D l hl Ω B.stage N hB).hom.app B.obj

def pullbackArrow :=
  (stageB D l hl Ω g A N hA).inv ≫
    (pointStageFibre D l hl Ω N).map
      ((rationalPullback D l hl g (Coefficient.{u} l Ω N)).map f) ≫
    (stageB D l hl Ω g B N hB).hom

def pointClass (X Y : DerivedCategory.PointFdQbar l Ω)
    (M : Index l Ω) (hX : X.1 ≤ M) (hY : Y.1 ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) : X ⟶ Y :=
  (DerivedCategory.pointFdQbarStageComp l Ω hX).inv.app X.2 ≫
    (DerivedCategory.pointFdQbarStage l Ω M).map v ≫
    (DerivedCategory.pointFdQbarStageComp l Ω hY).hom.app Y.2

def fibreClass :=
  pointClass l Ω (pointQbarFibreObj D l hl Ω A) (pointQbarFibreObj D l hl Ω B)
    N hA hB (fibreArrow D l hl Ω A B N hA hB f)

def pullbackClass :=
  pointClass l Ω (pointQbarFibreObj D l hl Ω (pullbackObject D l hl Ω g A))
    (pointQbarFibreObj D l hl Ω (pullbackObject D l hl Ω g B))
    N hA hB (pullbackArrow D l hl Ω g A B N hA hB f)

def pointTransport (X Y : DerivedCategory.PointFdQbar l Ω)
    (N M : Index l Ω) (hX : X.1 ≤ N) (hY : Y.1 ≤ N) (h : N ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) :=
  (pointFibreFdTensorTower (IntermediateField.inclusion hX).toRingHom
      (IntermediateField.inclusion h).toRingHom).inv.app X.2 ≫
    (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom).map v ≫
    (pointFibreFdTensorTower (IntermediateField.inclusion hY).toRingHom
      (IntermediateField.inclusion h).toRingHom).hom.app Y.2

def CommonNormalized (t : RationalFamily D l hl Ω g)
    (τ : pointQbarFibre D l hl Ω ⟶ commonPullback D l hl Ω g ⋙ pointQbarFibre D l hl Ω) :
    Prop :=
  ∀ A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)),
    HEq (τ.app A)
      ((DerivedCategory.pointFdQbarStage l Ω A.stage).map (stageComponent D l hl Ω g t A))
```

## New

```lean
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PointFdQbarCategory
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PointSectionsScalarExtension
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.PointFibreDerivedTensorBasic
public import Sheaf.Paper.PointTransformationRationalNormalization
public import Sheaf.Paper.PointRationalFamilyCommonStageNaturality
import Sheaf.Paper.PointCompositeComparisonTower

abbrev integralSections (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  PointRationalNormalization.sections D l E

abbrev integralPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  PointRationalNormalization.pullback D l hl g E

abbrev rationalPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  PointRationalFamily.rationalPullback D l hl g E

abbrev commonPullback :=
  PointRationalFamily.commonPullback D l hl Ω g

abbrev pullbackObject (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  PointRationalFamily.pullbackObject D l hl Ω g A

abbrev integralAlpha (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  PointRationalNormalization.alpha D l hl g E L ι K

abbrev integralPhi (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  PointRationalNormalization.phi D l hl E L ι K

abbrev rationalB (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :=
  PointRationalFamily.rationalB D l hl g E L ι K

abbrev IntegralFamily :=
  PointRationalNormalization.IntegralFamily D l hl Ω g

abbrev IntegralCompatible (η : IntegralFamily D l hl Ω g) : Prop :=
  PointRationalNormalization.IntegralCompatible D l hl Ω g η

abbrev RationalFamily :=
  PointRationalFamily.RationalFamily D l hl Ω g

abbrev RationalNormalized (η : IntegralFamily D l hl Ω g)
    (t : RationalFamily D l hl Ω g) : Prop :=
  PointRationalNormalization.Components D l hl Ω g η t

abbrev RationalCompatible (t : RationalFamily D l hl Ω g) : Prop :=
  PointRationalFamily.RationalCompatible D l hl Ω g t

abbrev pullbackComparison
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  PointRationalFamily.pullbackComparison D l hl Ω g A N h

abbrev stageB
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  PointRationalFamily.stageB D l hl Ω g A N h

abbrev stageComponent (t : RationalFamily D l hl Ω g)
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  PointRationalFamily.stageComponent D l hl Ω g t A

abbrev componentAt (t : RationalFamily D l hl Ω g)
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  PointRationalFamily.componentAt D l hl Ω g t A N h

abbrev fibreArrow :=
  PointRationalFamily.fibreArrow D l hl Ω A B N hA hB f

abbrev pullbackArrow :=
  PointRationalFamily.pullbackArrow D l hl Ω g A B N hA hB f

abbrev pointClass (X Y : DerivedCategory.PointFdQbar l Ω)
    (M : Index l Ω) (hX : X.1 ≤ M) (hY : Y.1 ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) : X ⟶ Y :=
  PointRationalFamily.pointClass l Ω X Y M hX hY v

abbrev fibreClass :=
  PointRationalFamily.fibreClass D l hl Ω A B N hA hB f

abbrev pullbackClass :=
  PointRationalFamily.pullbackClass D l hl Ω g A B N hA hB f

abbrev pointTransport (X Y : DerivedCategory.PointFdQbar l Ω)
    (N M : Index l Ω) (hX : X.1 ≤ N) (hY : Y.1 ≤ N) (h : N ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) :=
  PointRationalFamily.pointTransport l Ω X Y N M hX hY h v

abbrev CommonNormalized (t : RationalFamily D l hl Ω g)
    (τ : pointQbarFibre D l hl Ω ⟶ commonPullback D l hl Ω g ⋙ pointQbarFibre D l hl Ω) :
    Prop :=
  PointRationalFamily.CommonNormalized D l hl Ω g t τ
```

The imported common-stage module supplies definitions only to the repaired
dependencies; its theorem is not used to assume comparison coherence or normalization.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PointTransformationCoefficientDescent | R4 | integralSections, integralPullback, rationalPullback, commonPullback, pullbackObject, integralAlpha, integralPhi, rationalB, IntegralFamily, IntegralCompatible, RationalFamily, RationalNormalized, RationalCompatible, pullbackComparison, stageB, stageComponent, componentAt, fibreArrow, pullbackArrow, pointClass, fibreClass, pullbackClass, pointTransport, CommonNormalized use canonical owners/models. |

The downstream script reports zero existing downstream modules for each of the three edited modules. Repository-wide namespace searches find no external uses of either repaired dependency. Existing unfinished DAG parents of the item stay valid: the aliases preserve their definitions exactly, and the theorem statement is unchanged. The two dependency nodes have only the parent descent node as a citer, audited in their statement_change records. No module held by another group is adapted. No target statement mentions a changed alias, and no target signature or mathematical meaning changes.

Identity inclusions, equal stages, zero transformations, empty sums and torsion objects retain the same formulas. No transition injectivity or component invertibility is assumed. No new theorem hole, arbitrary witness, or axiom is added.

## Status

landed 20261025T043315-L-1694914 2026-10-25 (merge of deliver/R4/Sheaf.Paper.PointTransformationCoefficientDescent)
