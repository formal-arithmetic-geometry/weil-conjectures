# WeilConjectures.PointCompositeComparison: canonical coefficient helpers

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
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.PointFibreDerivedTensorBasic
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale

def pullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  rationalDerivedPullback l E g

def sectionsPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  pullback D l hl g E ⋙ pointRationalFibre D l hl E

def commonPullback :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  commonStageDerivedPullback l Ω g

def pullbackPair (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  commonStagePullbackObject l Ω g A

def stageAlpha
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  commonStagePullbackComparison l Ω g A N h

def stageComparison
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  (pointStageFibre D l hl Ω N).mapIso (stageAlpha D l hl g Ω A N h).symm ≪≫
    (pointStageFibreScalarIso D l hl Ω A.stage N h).app
      (pullbackPair D l hl g Ω A).obj

def sectionsArrow :=
  (pointStageFibreScalarIso D l hl Ω A.stage N hA).inv.app A.obj ≫
    (pointStageFibre D l hl Ω N).map f ≫
    (pointStageFibreScalarIso D l hl Ω B.stage N hB).hom.app B.obj

def compositeArrow :=
  (stageComparison D l hl g Ω A N hA).inv ≫
    (pointStageFibre D l hl Ω N).map
      ((pullback D l hl g (Coefficient.{u} l Ω N)).map f) ≫
    (stageComparison D l hl g Ω B N hB).hom

def representativeClass (X Y : DerivedCategory.PointFdQbar l Ω)
    (M : Index l Ω) (hX : X.1 ≤ M) (hY : Y.1 ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) : X ⟶ Y :=
  (DerivedCategory.pointFdQbarStageComp l Ω hX).inv.app X.2 ≫
    (DerivedCategory.pointFdQbarStage l Ω M).map v ≫
    (DerivedCategory.pointFdQbarStageComp l Ω hY).hom.app Y.2

def sectionsClass :=
  representativeClass l Ω (pointQbarFibreObj D l hl Ω A) (pointQbarFibreObj D l hl Ω B)
    N hA hB (sectionsArrow D l hl Ω A B N hA hB f)

def compositeClass :=
  representativeClass l Ω (pointQbarFibreObj D l hl Ω (pullbackPair D l hl g Ω A))
    (pointQbarFibreObj D l hl Ω (pullbackPair D l hl g Ω B))
    N hA hB (compositeArrow D l hl g Ω A B N hA hB f)

def targetTransport (X Y : DerivedCategory.PointFdQbar l Ω)
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

def NaturalityAndUnit : Prop :=
  (∀ (F G : Index l Ω) (h : F ≤ G)
    (K J : sfRationalConstructibleCategory l F.val (Spec (.of D.k))) (v : K ⟶ J),
    (sectionsPullback D l hl g G.val).map
        ((sfRationalScalarExtension l F.val (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) G.val
          (IntermediateField.inclusion h)).map v) ≫
      (comparison D l hl g F.val G.val (IntermediateField.inclusion h)).hom.app J =
    (comparison D l hl g F.val G.val (IntermediateField.inclusion h)).hom.app K ≫
      (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom).map
        ((sectionsPullback D l hl g F.val).map v)) ∧
  (∀ (F : Index l Ω) (K : sfRationalConstructibleCategory l F.val (Spec (.of D.k))),
    ((comparison D l hl g F.val F.val (AlgHom.id ℚ_[l] F.val)).hom.app K).hom ≫
        (DerivedCategory.fieldScalarUnit F.val).hom.app
          ((sectionsPullback D l hl g F.val).obj K).obj =
      ((sectionsPullback D l hl g F.val).map
        ((sfRationalScalarUnit l F.val (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K)).hom)

def Tower : Prop :=
  ∀ (F G H : Index l Ω) (h : F ≤ G) (k : G ≤ H)
    (K : sfRationalConstructibleCategory l F.val (Spec (.of D.k))),
    (sectionsPullback D l hl g H.val).map
        ((sfRationalScalarComp l F.val G.val (IntermediateField.inclusion h)
          (Spec (.of D.k)) 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) H.val
          (IntermediateField.inclusion k)).hom.app K) ≫
      (comparison D l hl g F.val H.val
        ((IntermediateField.inclusion k).comp (IntermediateField.inclusion h))).hom.app K =
    (comparison D l hl g G.val H.val (IntermediateField.inclusion k)).hom.app
        ((sfRationalScalarExtension l F.val (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) G.val
          (IntermediateField.inclusion h)).obj K) ≫
      (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion k).toRingHom).map
        ((comparison D l hl g F.val G.val (IntermediateField.inclusion h)).hom.app K) ≫
      (pointFibreFdTensorTower (IntermediateField.inclusion h).toRingHom
        (IntermediateField.inclusion k).toRingHom).hom.app
          ((sectionsPullback D l hl g F.val).obj K)
```

## New

```lean
public import Sheaf.Paper.PointRationalFamilyCommonStageNaturality
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PointFdQbarCategory
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.PointFibreDerivedTensorBasic
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale

abbrev pullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  PointRationalFamily.rationalPullback D l hl g E

abbrev sectionsPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  pullback D l hl g E ⋙ pointRationalFibre D l hl E

abbrev commonPullback :=
  PointRationalFamily.commonPullback D l hl Ω g

abbrev pullbackPair (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  PointRationalFamily.pullbackObject D l hl Ω g A

abbrev stageAlpha
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  PointRationalFamily.pullbackComparison D l hl Ω g A N h

abbrev stageComparison
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  PointRationalFamily.stageB D l hl Ω g A N h

abbrev sectionsArrow :=
  PointRationalFamily.fibreArrow D l hl Ω A B N hA hB f

abbrev compositeArrow :=
  PointRationalFamily.pullbackArrow D l hl Ω g A B N hA hB f

abbrev representativeClass (X Y : DerivedCategory.PointFdQbar l Ω)
    (M : Index l Ω) (hX : X.1 ≤ M) (hY : Y.1 ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) : X ⟶ Y :=
  PointRationalFamily.pointClass l Ω X Y M hX hY v

abbrev sectionsClass :=
  PointRationalFamily.fibreClass D l hl Ω A B N hA hB f

abbrev compositeClass :=
  PointRationalFamily.pullbackClass D l hl Ω g A B N hA hB f

abbrev targetTransport (X Y : DerivedCategory.PointFdQbar l Ω)
    (N M : Index l Ω) (hX : X.1 ≤ N) (hY : Y.1 ≤ N) (h : N ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) :=
  PointRationalFamily.pointTransport l Ω X Y N M hX hY h v

def NaturalityAndUnit : Prop :=
  (∀ (F G : Index l Ω) (h : F ≤ G)
    (K J : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))) (v : K ⟶ J),
    (sectionsPullback D l hl g (Coefficient.{u} l Ω G)).map
        ((sfRationalScalarExtension l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)).map v) ≫
      (comparison D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω
        F G h)).hom.app J =
    (comparison D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F
      G h)).hom.app K ≫
      (DerivedCategory.pointFdScalarExtension (coefficientInclusion l Ω F G h).toRingHom).map
        ((sectionsPullback D l hl g (Coefficient.{u} l Ω F)).map v)) ∧
  (∀ (F : Index l Ω) (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of
    D.k))),
    ((comparison D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω F) (AlgHom.id ℚ_[l]
      (Coefficient.{u} l Ω F))).hom.app K).hom ≫
        (DerivedCategory.fieldScalarUnit (Coefficient.{u} l Ω F)).hom.app
          ((sectionsPullback D l hl g (Coefficient.{u} l Ω F)).obj K).obj =
      ((sectionsPullback D l hl g (Coefficient.{u} l Ω F)).map
        ((sfRationalScalarUnit l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K)).hom)

def Tower : Prop :=
  ∀ (F G H : Index l Ω) (h : F ≤ G) (k : G ≤ H)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (sectionsPullback D l hl g (Coefficient.{u} l Ω H)).map
        ((sfRationalScalarComp l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)
          (Spec (.of D.k)) 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω H)
          (coefficientInclusion l Ω G H k)).hom.app K) ≫
      (comparison D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω H)
        ((coefficientInclusion l Ω G H k).comp (coefficientInclusion l Ω F G h))).hom.app K =
    (comparison D l hl g (Coefficient.{u} l Ω G) (Coefficient.{u} l Ω H) (coefficientInclusion l Ω G
      H k)).hom.app
        ((sfRationalScalarExtension l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)).obj K) ≫
      (DerivedCategory.pointFdScalarExtension (coefficientInclusion l Ω G H k).toRingHom).map
        ((comparison D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion
          l Ω F G h)).hom.app K) ≫
      (pointFibreFdTensorTower (coefficientInclusion l Ω F G h).toRingHom
        (coefficientInclusion l Ω G H k).toRingHom).hom.app
          ((sectionsPullback D l hl g (Coefficient.{u} l Ω F)).obj K)
```

The imported common-stage module supplies definitions only to the repaired
dependencies; its theorem is not used to assume comparison coherence or normalization.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PointCompositeComparisonTower | unclaimed | pullback, NaturalityAndUnit, Tower use canonical owners/models. |
| Sheaf.Paper.PointTransformationCoefficientDescent | R4 | Uses the corrected interface in the proof and aliases. |

The downstream script reports zero existing downstream modules for each of the three edited modules. Repository-wide namespace searches find no external uses of either repaired dependency. Existing unfinished DAG parents of the item stay valid: the aliases preserve their definitions exactly, and the theorem statement is unchanged. The two dependency nodes have only the parent descent node as a citer, audited in their statement_change records. No module held by another group is adapted. No target statement mentions a changed alias, and no target signature or mathematical meaning changes.

Identity inclusions, equal stages, zero transformations, empty sums and torsion objects retain the same formulas. No transition injectivity or component invertibility is assumed. No new theorem hole, arbitrary witness, or axiom is added.

## Status

landed 20261025T043315-L-1694914 2026-10-25 (merge of deliver/R4/Sheaf.Paper.PointTransformationCoefficientDescent)
