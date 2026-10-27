# CommonStageRestrictionTensor coordinate interface

## Reason

Expose the canonical pair constructors and use named Stage endpoints during elaboration.
The old interface causes expensive definitional equality checks against the nested
scalar-extension categories. Explicit endpoints and reducible canonical pair wrappers
allow the proof to use the same operations with less unfolding. The inferred type
of theta is the original type, and its chosen value is the same uniquely specified
rational tensor comparison. No mathematical data or target statement changes. The same local reducibility
setting for the cached stage-category instance as in DerivedPullbackTensorHom
is used to avoid reconstruction of the category structure during elaboration.
The unit source comparison is expanded into exactly the coordinate expression
of commonStagePullbackComparison and the scalar unit, fixing endpoint types at
construction time instead of converting them during the proof.
The source and target definitions use the canonical commonStage constructors
directly, avoiding a final conversion between those constructors and their literal
record expansions. The component proof respects transparency except at explicit
unfolding steps.
The residueUnits construction is kept locally irreducible after its definition;
its data are unchanged, and all instances refer to that same construction.
Named operation comparisons, the base coefficient field and its integer ring are
likewise kept locally irreducible during proofs to avoid reopening their large
constructions. These local settings do not change their exported attributes.

## Old

```lean
def r {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (E : Index l Ω) : Stage l Ω X E ⥤ Stage l Ω Y E :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  rationalDerivedPullback l (Coefficient.{u} l Ω E) f

def t (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (E : Index l Ω) :
    Stage l Ω W E × Stage l Ω W E ⥤ Stage l Ω W E :=
  letI := residueUnits D l hl W
  rationalDerivedTensor l (Coefficient.{u} l Ω E) W

def b {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (E L : Index l Ω) (h : E ≤ L) :
    r D l hl Ω f E ⋙ transition l Ω Y E L h ≅
      transition l Ω X E L h ⋙ r D l hl Ω f L :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f

def theta (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (E L : Index l Ω) (h : E ≤ L) :
    t D l hl Ω W E ⋙ transition l Ω W E L h ≅
      (transition l Ω W E L h).prod (transition l Ω W E L h) ⋙ t D l hl Ω W L :=
  letI := residueUnits D l hl W
  rationalTensorScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W

def source {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X) : Pair l Ω Y :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStagePullbackObject l Ω f (commonStageTensorObject l Ω X A B)

def target {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X) : Pair l Ω Y :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStageTensorObject l Ω Y
    (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B)

def sourceComparison {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X)
    (L : Index l Ω) (h : (source D l hl Ω f A B).stage ≤ L) :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStagePullbackComparison l Ω f (commonStageTensorObject l Ω X A B) L h ≪≫
    (r D l hl Ω f L).mapIso (commonStageTensorComparison l Ω X A B L h)

def targetComparison {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X)
    (L : Index l Ω) (h : (target D l hl Ω f A B).stage ≤ L) :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStageTensorComparison l Ω Y
      (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B) L h ≪≫
    (t D l hl Ω Y L).mapIso (Iso.prod
      (commonStagePullbackComparison l Ω f A L
        (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1.trans h))
      (commonStagePullbackComparison l Ω f B L
        (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2.trans h)))

def unitPair (W : Scheme.{u}) [W.Over (Spec (.of D.k))] : Pair l Ω W :=
  (inclusion (l := l) (Ω := Ω) (Y := W)
    (Padic.finiteCoefficientBase l Ω)).obj
      (unit D l hl Ω W (Padic.finiteCoefficientBase l Ω))

def unitTargetComparison (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (E : Index l Ω) :=
  (operationStageTransitionIso l Ω W (Padic.finiteCoefficientBase l Ω) E
    (baseInclusion l Ω E)).app _ ≪≫
      upsilon D l hl Ω W (Padic.finiteCoefficientBase l Ω) E (baseInclusion l Ω E)

def unitSource {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStagePullbackObject l Ω f (unitPair D l hl Ω X)

def unitSourceComparison {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (E : Index l Ω) :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStagePullbackComparison l Ω f (unitPair D l hl Ω X) E
      (baseInclusion l Ω E) ≪≫
    (r D l hl Ω f E).mapIso (unitTargetComparison D l hl Ω X E)
```

## New

```lean
@[reducible] def r {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (E : Index l Ω) :
    Stage l Ω X E ⥤ Stage l Ω Y E :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  rationalDerivedPullback l (Coefficient.{u} l Ω E) f

@[reducible] def t (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (E : Index l Ω) :
    Stage l Ω W E × Stage l Ω W E ⥤ Stage l Ω W E :=
  letI := residueUnits D l hl W
  rationalDerivedTensor l (Coefficient.{u} l Ω E) W

def b {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (E L : Index l Ω) (h : E ≤ L) :
    r D l hl Ω f E ⋙ transition l Ω Y E L h ≅
      transition l Ω X E L h ⋙ r D l hl Ω f L :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  show rationalDerivedPullback l (Coefficient.{u} l Ω E) f ⋙
      sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) ≅
    sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) ⋙ rationalDerivedPullback l (Coefficient.{u} l Ω L) f
  from rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f

def theta (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (E L : Index l Ω) (h : E ≤ L) :=
  letI := residueUnits D l hl W
  rationalTensorScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W

@[reducible] def source {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X) : Pair l Ω Y :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStagePullbackObject l Ω f (commonStageTensorObject l Ω X A B)

@[reducible] def target {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X) : Pair l Ω Y :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStageTensorObject l Ω Y
    (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B)

def sourceComparison {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X)
    (L : Index l Ω) (h : (source D l hl Ω f A B).stage ≤ L) :
    (source D l hl Ω f A B).toStage h ≅
      (r D l hl Ω f L).obj ((t D l hl Ω X L).obj
        (A.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
          A.stage B.stage).1.trans h),
         B.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
          A.stage B.stage).2.trans h))) :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStagePullbackComparison l Ω f (commonStageTensorObject l Ω X A B) L h ≪≫
    (r D l hl Ω f L).mapIso (commonStageTensorComparison l Ω X A B L h)

def targetComparison {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (A B : Pair l Ω X)
    (L : Index l Ω) (h : (target D l hl Ω f A B).stage ≤ L) :
    (target D l hl Ω f A B).toStage h ≅
      (t D l hl Ω Y L).obj
        ((r D l hl Ω f L).obj (A.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1.trans h)),
         (r D l hl Ω f L).obj (B.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2.trans h))) :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  commonStageTensorComparison l Ω Y
      (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B) L h ≪≫
    (t D l hl Ω Y L).mapIso (Iso.prod
      (commonStagePullbackComparison l Ω f A L
        (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1.trans h))
      (commonStagePullbackComparison l Ω f B L
        (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2.trans h)))

@[reducible] def unitPair (W : Scheme.{u}) [W.Over (Spec (.of D.k))] : Pair l Ω W :=
  ⟨Padic.finiteCoefficientBase l Ω,
    unit D l hl Ω W (Padic.finiteCoefficientBase l Ω)⟩

def unitTargetComparison (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (E : Index l Ω) :
    (unitPair D l hl Ω W).toStage (baseInclusion l Ω E) ≅ unit D l hl Ω W E :=
  (operationStageTransitionIso l Ω W (Padic.finiteCoefficientBase l Ω) E
    (baseInclusion l Ω E)).app _ ≪≫
      upsilon D l hl Ω W (Padic.finiteCoefficientBase l Ω) E (baseInclusion l Ω E)

@[reducible] def unitSource {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) : Pair l Ω Y :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  ⟨Padic.finiteCoefficientBase l Ω,
    (r D l hl Ω f (Padic.finiteCoefficientBase l Ω)).obj
      (unit D l hl Ω X (Padic.finiteCoefficientBase l Ω))⟩

def unitSourceComparison {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : Y ⟶ X) (E : Index l Ω) :
    (unitSource D l hl Ω f).toStage (baseInclusion l Ω E) ≅
      (r D l hl Ω f E).obj (unit D l hl Ω X E) :=
  letI := residueUnits D l hl X
  letI := residueUnits D l hl Y
  let E₀ := Padic.finiteCoefficientBase l Ω
  let U := unit D l hl Ω X E₀
  let R₀ := r D l hl Ω f E₀
  let R₁ := r D l hl Ω f E
  let x := operationStageTransitionIso l Ω X E₀ E (baseInclusion l Ω E)
  let y := operationStageTransitionIso l Ω Y E₀ E (baseInclusion l Ω E)
  (y.app (R₀.obj U) ≪≫ (b D l hl Ω f E₀ E (baseInclusion l Ω E)).app U ≪≫
    R₁.mapIso (x.app U).symm) ≪≫
    R₁.mapIso (unitTargetComparison D l hl Ω X E)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CommonStageRestrictionTensorDescent | U6 | Same operations and comparison values; explicit coordinate types for the proof. |

`tools/downstream.py Sheaf.Paper.CommonStageRestrictionTensorDescent --uses`
reports zero downstream modules. A full source scan likewise finds no Lean
importer. Unfinished parent DAG dependencies remain intact. No forced adaptation
is required. The public theorem descent is preserved verbatim. Any target using
these definitions keeps the same meaning; review of the definitional equality is
part of this definition-change packet. No source-library file is changed.

## Status

landed 20261025T164500-L-1024010 2026-10-25 (merge of deliver/U6/Sheaf.Paper.CommonStageRestrictionTensorDescent)
