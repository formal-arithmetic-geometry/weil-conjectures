# PulledReduction comparison data relocation

## Reason

The model-descent and restriction-of-limits lemmas use the same concrete functors and
normalizations. Move the existing declarations into one definition module, publicly
imported by the original module, so the proof lemmas can import them without a cycle.
The names, signatures, construction bodies and local-instance visibility stay the same.
Only their documentation node tags change. No target statement or mathematical
meaning changes; no new coefficient object, adjunction or derived functor is chosen.

## Old

In `Sheaf.Paper.PulledReductionStrictTowerComparison`:

```lean
/-- Constant scalar restriction, on the original small site.
Source: Stacks 099L (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
abbrev res (T : Scheme.{t}) := proEtaleRingRestrictScalars (exchangeScalar d T)

/-- Exact inverse image of constant-coefficient modules.
Source: Stacks 099N(5) (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
abbrev pull := proEtaleRingModulePullback g (exchangeConstantRing Y A)
  (exchangeConstantRing X A) (exchangeConstantIso g A)

/-- Ordinary constant-coefficient pullback after restriction; its exact derived functor
is N in the statement. Source: Stacks 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
abbrev ordinarySource := res d Y ⋙ pull (A := A) g

/-- N, on all ambient objects, without a completeness or boundedness hypothesis.
Source: Stacks 099N(5) (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def source := (ordinarySource d g).mapDerivedCategory

/-- The pulled-back completed-coefficient strict reduction tower H.
Source: Stacks 099N(5) (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def tower := completedReductionTower Y d ⋙ completedTowerPullback g d

/-- Ordinary restriction on strict towers, retaining all transitions.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
abbrev tres (T : Scheme.{t}) := exchangeTowerModuleRes d T


/-- The ordinary strict source diagram, before localization.
Source: Stacks 099N(5) (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
abbrev ordinaryReductionSource := ordinarySource d g ⋙ OrderedExchange.reductionModule d X

/-- The ordinary strict pulled quotient diagram, before localization.
Source: Stacks 099N(5) (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
abbrev ordinaryReductionTarget := completedReductionModuleTowerFunctor Y d ⋙
  completedTowerModulePullback g d ⋙ tres d X

/-- Zero maps for the entire ordinary strict comparison.
Source: Stacks 03EL
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
local instance ordinaryReductionTarget_preservesZeroMorphisms :
    (ordinaryReductionTarget d g).PreservesZeroMorphisms where
  map_zero M N := by
    have h := Functor.map_zero (completedReductionModuleTowerFunctor Y d) M N
    have h' := Functor.map_zero (completedTowerModulePullback g d)
      ((completedReductionModuleTowerFunctor Y d).obj M)
      ((completedReductionModuleTowerFunctor Y d).obj N)
    have h'' := Functor.map_zero (tres d X)
      ((completedTowerModulePullback g d).obj ((completedReductionModuleTowerFunctor Y d).obj M))
      ((completedTowerModulePullback g d).obj ((completedReductionModuleTowerFunctor Y d).obj N))
    exact (congrArg (tres d X).map
      ((congrArg (completedTowerModulePullback g d).map h).trans h')).trans h''

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar-insertion section for completed module pullback. Apply the actual
model-site pullback adjunction unit at the transported object, then insert 1.
The up/down module transports preserve section carriers definitionally, so this
is the unit of the constructed inverse image, with no choice of an adjunction.
Source: Stacks 03EK, 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def insertion (M : reductionModules Y (d.completedRing Y))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((completedModulePullback g d).obj M).val.obj ((proEtaleBaseChange g).op.obj U) := by
  letI : (proEtaleModelBaseChange g).IsContinuous
      (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
    proEtaleModelBaseChange_isContinuous g
  exact reductionTensorSection X (completedCoefficientMap g d)
    ((proEtaleModuleInverseImage g (d.completedRing Y)).obj M)
    ((proEtaleBaseChange g).op.obj U) 1
    (((SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
      (F := proEtaleModelBaseChange g)
      (J := proEtaleModelTopology Y) (K := proEtaleModelTopology X)
      (proEtaleModelRingUnit g (d.completedRing Y))).unit.app
        ((proEtaleModuleToModel (reductionModuleRing Y (d.completedRing Y))).obj M)).val.app
          (AsSmall.up.op.obj U) x)

/-- Scalar insertion determines the ordinary comparison, including its augmentation.
Source: Stacks 03EK, 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def IsOrdinaryNormalized
    (s : ordinarySource d g ⟶ completedModulePullback g d ⋙ res d X) : Prop :=
  ∀ (M : reductionModules Y (d.completedRing Y)) (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
    (s.app M).val.app ((proEtaleBaseChange g).op.obj U)
      (((proEtaleRingModuleAdjunction g (exchangeConstantRing Y A)
        (exchangeConstantRing X A) (exchangeConstantIso g A)).unit.app
          ((res d Y).obj M)).val.app U x) = insertion d g M U x

/-- Degreewise scalar insertion as a map of the actual pulled complexes.
The target is written as the successive two complex functors, retaining their
already fixed zero-map instances.
Source: Stacks 06YY
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def ordinaryComplexComparison
    (s : ordinarySource d g ⟶ completedModulePullback g d ⋙ res d X)
    (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
    ((ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((res d X).mapHomologicalComplex (.up ℤ)).obj
        (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) where
  f i := s.app (P.X i)
  comm' i j _ := (s.naturality (P.d i j)).symm

/-- A strict diagram comparison is normalized on inverse images of pure tensors.
Its natural-transformation type includes every quotient transition. The scalar on the
right is inserted only after the finite quotient is formed on Y.
Source: Stacks 03EL, 07A4, 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def IsStrictNormalized (e : ordinaryReductionSource d g ≅ ordinaryReductionTarget d g) : Prop :=
  ∀ (M : reductionModules Y (d.completedRing Y)) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (d.finiteRing Y n).obj.obj U) (x : M.val.obj U),
    ((e.hom.app M).app (op n)).val.app ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (OrderedExchange.quotient d X n)
        ((ordinarySource d g).obj M) ((proEtaleBaseChange g).op.obj U)
        ((proEtaleRingDirectImageMap g (d.finiteRing Y n) (d.finiteRing X n)
          (d.finiteRingIso g n)).hom.app U s)
        (((proEtaleRingModuleAdjunction g (exchangeConstantRing Y A)
          (exchangeConstantRing X A) (exchangeConstantIso g A)).unit.app
            ((res d Y).obj M)).val.app U x)) =
      insertion d g ((completedReductionLevel Y d n).obj M) U
        (reductionTensorSection Y (d.projection Y n) M U s x)

/-- The comparison from H on a K-flat completed model to its ordinary pulled quotient
complex. Its invertibility is asserted only on the specified resolving class below.
Source: Stacks 06YY, 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def targetCounit (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
    ((tower d g) ⋙ (tres d X).mapDerivedCategory).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ordinaryReductionTarget d g).mapHomologicalComplex (.up ℤ)).obj P) :=
  (tres d X).mapDerivedCategory.map
      ((completedTowerPullback g d).map (completedReductionTowerComplexCounit Y d P) ≫
        completedTowerPullbackComplexCounit g d
          ((completedReductionComplexTowerFunctor Y d).obj P)) ≫
    (tres d X).mapDerivedCategoryFactors.hom.app
      (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
        ((completedReductionComplexTowerFunctor Y d).obj P))

/-- Exact evaluation commutes with restriction of the entire strict diagram.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def evaluationRes (T : Scheme.{t}) (n : ℕ) :
    (tres d T).mapDerivedCategory ⋙
        reductionTowerDerivedEvaluation T (reductionModuleRing T (exchangeConstantRing T A)) n ≅
      reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n ⋙
        (res d T).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso
    (Iso.refl (tres d T ⋙ reductionTowerEvaluation T
      (reductionModuleRing T (exchangeConstantRing T A)) n))

/-- Exact restriction commutes with constant strict diagrams.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def diagonalRes (T : Scheme.{t}) :
    (res d T).mapDerivedCategory ⋙ OrderedExchange.diagonal (A := A) T ≅
      completedDerivedConstant d T ⋙ (tres d T).mapDerivedCategory :=
  (OrderedExchange.scalarDiagonal d T).symm

/-- The pulled strict quotient augmentation, before inverse limit.
Source: Stacks 099N(5) (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def pulledAugmentation (K : reductionDerivedCategory Y (d.completedRing Y)) :
    (completedDerivedConstant d X).obj ((completedOrdinaryPullback g d).obj K) ⟶
      (tower d g).obj K :=
  (completedPullbackConstantIso g d).hom.app K ≫
    (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K)

/-- Rho is Rlim(tau) inverse after the specified restriction/limit comparison. This
uses the normalized K-injective limit comparison already recorded in the library.
Source: Stacks 0940, 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def limitComparison
    (τ : source d g ⋙ OrderedExchange.reduction d X ≅
      tower d g ⋙ (tres d X).mapDerivedCategory)
    (K : reductionDerivedCategory Y (d.completedRing Y)) :
    (res d X).mapDerivedCategory.obj
        ((completedRlim X (d.completedRing X)).obj ((tower d g).obj K)) ≅
      (OrderedExchange.completion d X).obj ((source d g).obj K) :=
  (OrderedExchange.lambda d X).app ((tower d g).obj K) ≪≫
    (OrderedExchange.rlim (A := A) X).mapIso (τ.app K).symm
```

## New

In `Sheaf.Paper.PulledReductionComparisonData`, publicly imported by the original module:

```lean
/-- Constant scalar restriction, on the original small site.
Source: Stacks 099L (blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
abbrev res (T : Scheme.{t}) := proEtaleRingRestrictScalars (exchangeScalar d T)

/-- Exact inverse image of constant-coefficient modules.
Source: Stacks 099N(5) (blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
abbrev pull := proEtaleRingModulePullback g (exchangeConstantRing Y A)
  (exchangeConstantRing X A) (exchangeConstantIso g A)

/-- Ordinary constant-coefficient pullback after restriction; its exact derived functor
is N in the statement. Source: Stacks 099N(5)
(blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
abbrev ordinarySource := res d Y ⋙ pull (A := A) g

/-- N, on all ambient objects, without a completeness or boundedness hypothesis.
Source: Stacks 099N(5) (blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
def source := (ordinarySource d g).mapDerivedCategory

/-- The pulled-back completed-coefficient strict reduction tower H.
Source: Stacks 099N(5) (blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
def tower := completedReductionTower Y d ⋙ completedTowerPullback g d

/-- Ordinary restriction on strict towers, retaining all transitions.
Source: Stacks 03D7 (blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
abbrev tres (T : Scheme.{t}) := exchangeTowerModuleRes d T


/-- The ordinary strict source diagram, before localization.
Source: Stacks 099N(5) (blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
abbrev ordinaryReductionSource := ordinarySource d g ⋙ OrderedExchange.reductionModule d X

/-- The ordinary strict pulled quotient diagram, before localization.
Source: Stacks 099N(5) (blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
abbrev ordinaryReductionTarget := completedReductionModuleTowerFunctor Y d ⋙
  completedTowerModulePullback g d ⋙ tres d X

/-- Zero maps for the entire ordinary strict comparison.
Source: Stacks 03EL
(blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
local instance ordinaryReductionTarget_preservesZeroMorphisms :
    (ordinaryReductionTarget d g).PreservesZeroMorphisms where
  map_zero M N := by
    have h := Functor.map_zero (completedReductionModuleTowerFunctor Y d) M N
    have h' := Functor.map_zero (completedTowerModulePullback g d)
      ((completedReductionModuleTowerFunctor Y d).obj M)
      ((completedReductionModuleTowerFunctor Y d).obj N)
    have h'' := Functor.map_zero (tres d X)
      ((completedTowerModulePullback g d).obj ((completedReductionModuleTowerFunctor Y d).obj M))
      ((completedTowerModulePullback g d).obj ((completedReductionModuleTowerFunctor Y d).obj N))
    exact (congrArg (tres d X).map
      ((congrArg (completedTowerModulePullback g d).map h).trans h')).trans h''

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar-insertion section for completed module pullback. Apply the actual
model-site pullback adjunction unit at the transported object, then insert 1.
The up/down module transports preserve section carriers definitionally, so this
is the unit of the constructed inverse image, with no choice of an adjunction.
Source: Stacks 03EK, 099N(5)
(blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
def insertion (M : reductionModules Y (d.completedRing Y))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((completedModulePullback g d).obj M).val.obj ((proEtaleBaseChange g).op.obj U) := by
  letI : (proEtaleModelBaseChange g).IsContinuous
      (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
    proEtaleModelBaseChange_isContinuous g
  exact reductionTensorSection X (completedCoefficientMap g d)
    ((proEtaleModuleInverseImage g (d.completedRing Y)).obj M)
    ((proEtaleBaseChange g).op.obj U) 1
    (((SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
      (F := proEtaleModelBaseChange g)
      (J := proEtaleModelTopology Y) (K := proEtaleModelTopology X)
      (proEtaleModelRingUnit g (d.completedRing Y))).unit.app
        ((proEtaleModuleToModel (reductionModuleRing Y (d.completedRing Y))).obj M)).val.app
          (AsSmall.up.op.obj U) x)

/-- Scalar insertion determines the ordinary comparison, including its augmentation.
Source: Stacks 03EK, 099N(5)
(blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
def IsOrdinaryNormalized
    (s : ordinarySource d g ⟶ completedModulePullback g d ⋙ res d X) : Prop :=
  ∀ (M : reductionModules Y (d.completedRing Y)) (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
    (s.app M).val.app ((proEtaleBaseChange g).op.obj U)
      (((proEtaleRingModuleAdjunction g (exchangeConstantRing Y A)
        (exchangeConstantRing X A) (exchangeConstantIso g A)).unit.app
          ((res d Y).obj M)).val.app U x) = insertion d g M U x

/-- Degreewise scalar insertion as a map of the actual pulled complexes.
The target is written as the successive two complex functors, retaining their
already fixed zero-map instances.
Source: Stacks 06YY
(blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
def ordinaryComplexComparison
    (s : ordinarySource d g ⟶ completedModulePullback g d ⋙ res d X)
    (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
    ((ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((res d X).mapHomologicalComplex (.up ℤ)).obj
        (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) where
  f i := s.app (P.X i)
  comm' i j _ := (s.naturality (P.d i j)).symm

/-- A strict diagram comparison is normalized on inverse images of pure tensors.
Its natural-transformation type includes every quotient transition. The scalar on the
right is inserted only after the finite quotient is formed on Y.
Source: Stacks 03EL, 07A4, 099N(5)
(blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
def IsStrictNormalized (e : ordinaryReductionSource d g ≅ ordinaryReductionTarget d g) : Prop :=
  ∀ (M : reductionModules Y (d.completedRing Y)) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (d.finiteRing Y n).obj.obj U) (x : M.val.obj U),
    ((e.hom.app M).app (op n)).val.app ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (OrderedExchange.quotient d X n)
        ((ordinarySource d g).obj M) ((proEtaleBaseChange g).op.obj U)
        ((proEtaleRingDirectImageMap g (d.finiteRing Y n) (d.finiteRing X n)
          (d.finiteRingIso g n)).hom.app U s)
        (((proEtaleRingModuleAdjunction g (exchangeConstantRing Y A)
          (exchangeConstantRing X A) (exchangeConstantIso g A)).unit.app
            ((res d Y).obj M)).val.app U x)) =
      insertion d g ((completedReductionLevel Y d n).obj M) U
        (reductionTensorSection Y (d.projection Y n) M U s x)

/-- The comparison from H on a K-flat completed model to its ordinary pulled quotient
complex. Its invertibility is asserted only on the specified resolving class below.
Source: Stacks 06YY, 099N(5)
(blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
def targetCounit (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
    ((tower d g) ⋙ (tres d X).mapDerivedCategory).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ordinaryReductionTarget d g).mapHomologicalComplex (.up ℤ)).obj P) :=
  (tres d X).mapDerivedCategory.map
      ((completedTowerPullback g d).map (completedReductionTowerComplexCounit Y d P) ≫
        completedTowerPullbackComplexCounit g d
          ((completedReductionComplexTowerFunctor Y d).obj P)) ≫
    (tres d X).mapDerivedCategoryFactors.hom.app
      (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
        ((completedReductionComplexTowerFunctor Y d).obj P))

/-- Exact evaluation commutes with restriction of the entire strict diagram.
Source: Stacks 03D7 (blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
def evaluationRes (T : Scheme.{t}) (n : ℕ) :
    (tres d T).mapDerivedCategory ⋙
        reductionTowerDerivedEvaluation T (reductionModuleRing T (exchangeConstantRing T A)) n ≅
      reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n ⋙
        (res d T).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso
    (Iso.refl (tres d T ⋙ reductionTowerEvaluation T
      (reductionModuleRing T (exchangeConstantRing T A)) n))

/-- Exact restriction commutes with constant strict diagrams.
Source: Stacks 03D7 (blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
def diagonalRes (T : Scheme.{t}) :
    (res d T).mapDerivedCategory ⋙ OrderedExchange.diagonal (A := A) T ≅
      completedDerivedConstant d T ⋙ (tres d T).mapDerivedCategory :=
  (OrderedExchange.scalarDiagonal d T).symm

/-- The pulled strict quotient augmentation, before inverse limit.
Source: Stacks 099N(5) (blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
def pulledAugmentation (K : reductionDerivedCategory Y (d.completedRing Y)) :
    (completedDerivedConstant d X).obj ((completedOrdinaryPullback g d).obj K) ⟶
      (tower d g).obj K :=
  (completedPullbackConstantIso g d).hom.app K ≫
    (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K)

/-- Rho is Rlim(tau) inverse after the specified restriction/limit comparison. This
uses the normalized K-injective limit comparison already recorded in the library.
Source: Stacks 0940, 099N(5)
(blueprint: def-weil-pbc-pulled-reduction-comparison-data). -/
def limitComparison
    (τ : source d g ⋙ OrderedExchange.reduction d X ≅
      tower d g ⋙ (tres d X).mapDerivedCategory)
    (K : reductionDerivedCategory Y (d.completedRing Y)) :
    (res d X).mapDerivedCategory.obj
        ((completedRlim X (d.completedRing X)).obj ((tower d g).obj K)) ≅
      (OrderedExchange.completion d X).obj ((source d g).obj K) :=
  (OrderedExchange.lambda d X).app ((tower d g).obj K) ≪≫
    (OrderedExchange.rlim (A := A) X).mapIso (τ.app K).symm
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedTowerPullback | unclaimed | Existing proof holes filled; all public signatures, attributes, construction bodies and public imports preserved. No forced adaptation. |
| Sheaf.Paper.PulledReductionStrictTowerComparison | M1 | Publicly imports the same named definitions and enables its moved local zero-map instance locally. Its theorem statement is unchanged. |
| Sheaf.Paper.PulledReductionStrictModelDescent | M1, new | Imports the shared data and states only the strict-model part. |
| Sheaf.Paper.RestrictionLimitProjectionUnit | M1, new | Imports the shared data for the fixed evaluation and diagonal squares. |
| Sheaf.Paper.PulledReductionNormalizationComparison | E9 | Its public import still exposes the same source functor and scalar-insertion definitions, with identical bodies and signatures. No adaptation. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | Its public import still exposes res, pull, insertion and IsOrdinaryNormalized, with identical bodies and signatures. No adaptation. |

The current downstream script reports the two existing importers listed above.
Both retain all referenced declarations through the original module's public import.
The moved declaration bodies were mechanically compared with current sources and
are identical after removing docstrings. The theorem statement is byte-identical.
Its DAG parents are retained: the full original comparison remains available with the
same statement. There is no withdrawal or adaptation of another group's module.

The supporting proof-only changes to `Sheaf.Paper.CompletedTowerPullback` preserve
all public signatures, definition bodies, attributes and public imports. Its textual
proof users are `CompletedFiniteExchangeCoordinates`, `PbcCompletedPullbackActual`,
`AdicPullbackPresentationTransport`, `CompletedConstantCoefficientEquivalence`,
`CompletedQuotientUnitNormalization`, `PbcActualScalarPullback`, `SbcCompletedOperations`,
`CompletedPullbackReduction`, and the original comparison and Roos modules listed
above (all under `Sheaf.Paper`). Their types and data are identical; none is adapted.
This supporting module was unclaimed when the proof work began. These proof changes
require no statement review for a consumer or a target.

## Status

landed 20261022T002420-L-1927389 2026-10-22 (merge of deliver/M1/Sheaf.Paper.PulledReductionStrictTowerComparison)
