# ConstructiblePointRationalComparison and ConstructiblePointCommonStageComparison

## Reason

The new point-fibre proof specializes generic comparison data to the standard derived
category of modules. In the two existing predicates, make that already intended target
category explicit in the `cohomology` projection. The original projection infers this
same category from the comparison record. This is an elaboration annotation only:
no binder, hypothesis, equation, coefficient model or underlying definition changes.
The two predicates are used textually only by this item, as checked by repository
search. The completed item compiles without errors or warnings (52.9 seconds).

The accompanying settings and helper instance are local proof-elaboration support;
there are no exported attribute or instance-priority changes. In particular no target
statement or definition's mathematical meaning changes.

## Old

```lean
def ConstructiblePointRationalComparison
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (x : Spec (.of D.k) ⟶ X) : Prop :=
  letI := constructiblePullbackResidueUnits D l hl X
  letI := constructiblePullbackResidueUnits D l hl (Spec (.of D.k))
  ∃ (d : ConstructibleRationalPullbackComparison D l hl E x)
    (f : ConstructiblePullbackComparison
      (sfRationalStandardTStructure l E (Spec (.of D.k)) D hl)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} E))
      (sfRationalHeartProperty l E (Spec (.of D.k)))
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)).heart
      (constructiblePointRationalRealization D l hl E)),
    (∀ j : ℤ, ∃ γ :
        constructibleTruncationCohomology (sfRationalStandardTStructure l E X D hl) j ⋙
          rationalDerivedPullback l E x ⋙ constructiblePointRationalRealization D l hl E ≅
        rationalDerivedPullback l E x ⋙ constructiblePointRationalRealization D l hl E ⋙
          constructibleTruncationCohomology
            (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)) j,
      ∀ K : sfRationalConstructibleCategory l E X,
        γ.app K = (constructiblePointRationalRealization D l hl E).mapIso
            ((d.cohomology j).app K) ≪≫
          (f.cohomology j).app ((rationalDerivedPullback l E x).obj K)) ∧
    ∀ (F : sfRationalHeart l E X) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} E) j).obj
        ((constructiblePointRationalRealization D l hl E).obj
          ((rationalDerivedPullback l E x).obj F.obj)))

def ConstructiblePointCommonStageComparison
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (x : Spec (.of D.k) ⟶ X) : Prop :=
  letI := constructiblePullbackResidueUnits D l hl X
  letI := constructiblePullbackResidueUnits D l hl (Spec (.of D.k))
  ∃ (d : ConstructibleCommonStagePullbackComparison D l hl Ω x)
    (f : ConstructiblePullbackComparison
      (sfCommonStageStandardTStructure l (Spec (.of D.k)) Ω D hl)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω))
      (sfCommonStageHeartProperty l (Spec (.of D.k)) Ω)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω)).heart
      (constructiblePointCommonStageRealization D l hl Ω)),
    (∀ j : ℤ, ∃ γ :
        constructibleTruncationCohomology (sfCommonStageStandardTStructure l X Ω D hl) j ⋙
          commonStageDerivedPullback l Ω x ⋙ constructiblePointCommonStageRealization D l hl Ω ≅
        commonStageDerivedPullback l Ω x ⋙ constructiblePointCommonStageRealization D l hl Ω ⋙
          constructibleTruncationCohomology
            (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω)) j,
      ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
        γ.app K = (constructiblePointCommonStageRealization D l hl Ω).mapIso
            ((d.cohomology j).app K) ≪≫
          (f.cohomology j).app ((commonStageDerivedPullback l Ω x).obj K)) ∧
    ∀ (F : sfCommonStageHeart l X Ω) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Ω) j).obj
        ((constructiblePointCommonStageRealization D l hl Ω).obj
          ((commonStageDerivedPullback l Ω x).obj F.obj)))
```

## New

```lean
def ConstructiblePointRationalComparison
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (x : Spec (.of D.k) ⟶ X) : Prop :=
  letI := constructiblePullbackResidueUnits D l hl X
  letI := constructiblePullbackResidueUnits D l hl (Spec (.of D.k))
  ∃ (d : ConstructibleRationalPullbackComparison D l hl E x)
    (f : ConstructiblePullbackComparison
      (sfRationalStandardTStructure l E (Spec (.of D.k)) D hl)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} E))
      (sfRationalHeartProperty l E (Spec (.of D.k)))
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)).heart
      (constructiblePointRationalRealization D l hl E)),
    (∀ j : ℤ, ∃ γ :
        constructibleTruncationCohomology (sfRationalStandardTStructure l E X D hl) j ⋙
          rationalDerivedPullback l E x ⋙ constructiblePointRationalRealization D l hl E ≅
        rationalDerivedPullback l E x ⋙ constructiblePointRationalRealization D l hl E ⋙
          constructibleTruncationCohomology
            (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)) j,
      ∀ K : sfRationalConstructibleCategory l E X,
        γ.app K = (constructiblePointRationalRealization D l hl E).mapIso
            ((d.cohomology j).app K) ≪≫
          (f.cohomology (B := DerivedCategory (ModuleCat.{u} E)) j).app
            ((rationalDerivedPullback l E x).obj K)) ∧
    ∀ (F : sfRationalHeart l E X) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} E) j).obj
        ((constructiblePointRationalRealization D l hl E).obj
          ((rationalDerivedPullback l E x).obj F.obj)))

def ConstructiblePointCommonStageComparison
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (x : Spec (.of D.k) ⟶ X) : Prop :=
  letI := constructiblePullbackResidueUnits D l hl X
  letI := constructiblePullbackResidueUnits D l hl (Spec (.of D.k))
  ∃ (d : ConstructibleCommonStagePullbackComparison D l hl Ω x)
    (f : ConstructiblePullbackComparison
      (sfCommonStageStandardTStructure l (Spec (.of D.k)) Ω D hl)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω))
      (sfCommonStageHeartProperty l (Spec (.of D.k)) Ω)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω)).heart
      (constructiblePointCommonStageRealization D l hl Ω)),
    (∀ j : ℤ, ∃ γ :
        constructibleTruncationCohomology (sfCommonStageStandardTStructure l X Ω D hl) j ⋙
          commonStageDerivedPullback l Ω x ⋙ constructiblePointCommonStageRealization D l hl Ω ≅
        commonStageDerivedPullback l Ω x ⋙ constructiblePointCommonStageRealization D l hl Ω ⋙
          constructibleTruncationCohomology
            (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω)) j,
      ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
        γ.app K = (constructiblePointCommonStageRealization D l hl Ω).mapIso
            ((d.cohomology j).app K) ≪≫
          (f.cohomology (B := DerivedCategory (ModuleCat.{u} Ω)) j).app
            ((commonStageDerivedPullback l Ω x).obj K)) ∧
    ∀ (F : sfCommonStageHeart l X Ω) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Ω) j).obj
        ((constructiblePointCommonStageRealization D l hl Ω).obj
          ((commonStageDerivedPullback l Ω x).obj F.obj)))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ConstructiblePullbackTExact | C8 | The two predicates retain their exact clauses; the point-fibre theorem now proves both by composing the comparison data. Compiled without warnings. |

No other module refers to either predicate by name. Importers use the unchanged
public interface of this module; no consumer adaptation is needed. The annotation
only specifies an existing implicit argument, and no statement meaning changes.

## Status

landed 20261021T100916-L-4170228 2026-10-21 (merge of deliver/C8/Sheaf.Paper.ConstructiblePullbackTExact)
