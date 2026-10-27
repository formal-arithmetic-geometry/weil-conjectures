# WeilConjectures.AdicNormalizedPurity canonical systems

## Reason

The normalization and exceptional-mate substeps must be stated in independent modules. Move the canonical definitions to an interface module to avoid a circular import. The item publicly reexports this module. Every existing declaration name, signature, attribute, and body is preserved; only its blueprint ownership tag changes. No endpoint or coefficient object is replaced. The theorem statement stays identical.

## Old

All definitions below were declared in `Sheaf.Paper.AdicNormalizedPurityLift`:

```lean
def sourceSequence (K : DerivedCategory (scalarReductionSource C.l E Y)) :=
  (pullbackTensorCalculus C.l E X).reduction.obj (purAdicSource D C E f d K)
```

```lean
def targetSequence (K : DerivedCategory (scalarReductionSource C.l E Y)) :=
  (integralExceptionalSystem C.l E D C.different f).obj K
```

```lean
def sourceTower (K : DerivedCategory (scalarReductionSource C.l E Y)) :=
  (coefficientSequenceDerivedRestriction C.l E X).obj (sourceSequence D C E f d K)
```

```lean
def targetTower (K : DerivedCategory (scalarReductionSource C.l E Y)) :=
  (coefficientSequenceDerivedRestriction C.l E X).obj (targetSequence D C E f K)
```

```lean
def sourceEvaluation
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) (n : ℕ) :
    (normalizedDVRTowerEvaluation C.l E X D C.different n).obj
        (sourceTower D C E f d K) ⟶
      (normalizedDVRResCompleted C.l E X D C.different n).obj
        (purAdicFiniteArrow D C E f d K hK n).left :=
  (coefficientRestrictedEvaluationIso C.l E X n).hom.app _ ≫
    (normalizedDVRResCompleted C.l E X D C.different n).map
      (((pullbackTensorCalculus C.l E X).reductionEvaluation n).hom.app _ ≫
        purAdicSourceReduction D C E f d K hK n)
```

```lean
def targetEvaluation
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) (n : ℕ) :
    (normalizedDVRTowerEvaluation C.l E X D C.different n).obj
        (targetTower D C E f K) ≅
      (normalizedDVRResCompleted C.l E X D C.different n).obj
        (purAdicFiniteArrow D C E f d K hK n).right :=
  (coefficientRestrictedEvaluationIso C.l E X n).app _ ≪≫
    (normalizedDVRResCompleted C.l E X D C.different n).mapIso
      (purAdicExceptionalEvaluation D C E f K n)
```

```lean
def exceptionalNormalization
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :
    ((purAdicFiniteSetting D C E m).finiteReduction (n + 1) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1) X).obj
        (purAdicFiniteArrow D C E f d K hK m).right ⟶
      (purAdicFiniteArrow D C E f d K hK n).right :=
  (purAdicFiniteSetting D C E m).finiteReductionExceptionalComparison (n + 1)
      (Nat.succ_pos n) (Nat.add_le_add_right h 1) f d
      ((scalarReductionDerivedExtension C.l E Y m).obj K)
      (purAdicReductionFiniteTor D C E Y K hK m) ≫
    ((purAdicFiniteSetting D C E n).compositionExceptional f).map
      (purAdicQuotientNormalization D C E Y h K)
```

```lean
def exceptionalTransition
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :
    (purAdicFiniteArrow D C E f d K hK m).right ⟶
      (normalizedDVRRes C.l E X h).obj (purAdicFiniteArrow D C E f d K hK n).right :=
  (purAdicExceptionalEvaluation D C E f K m).inv ≫
    (coefficientSequenceDerivedTransition C.l E X h).app (targetSequence D C E f K) ≫
    (normalizedDVRRes C.l E X h).map (purAdicExceptionalEvaluation D C E f K n).hom
```

```lean
def sourceRestrictedTransition
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :=
  (normalizedDVRResCompleted C.l E X D C.different m).map
      (purAdicFiniteSourceTransition D C E f d K hK h) ≫
    (normalizedDVRResCompletedComp C.l E X D C.different h).hom.app _
```

```lean
def targetRestrictedTransition
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :=
  (normalizedDVRResCompleted C.l E X D C.different m).map
      (exceptionalTransition D C E f d K hK h) ≫
    (normalizedDVRResCompletedComp C.l E X D C.different h).hom.app _
```

## New

The definitions above, with the same names and bodies, are declared in `Sheaf.Paper.AdicNormalizedPuritySystems`. The item has `public import Sheaf.Paper.AdicNormalizedPuritySystems`, retaining its public prerequisite imports transitively. The new interface owns blueprint tag `def-pur-adic-normalized-purity-systems`. The two new normalization lemmas publicly import that interface and are private proof imports of the item.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicNormalizedPurityLift | P3 | Same theorem statement; imports the interface and new proof components. |
| Sheaf.Paper.AdicActualSystemsNormalized | P3, new | States only normalization of the two actual systems. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | P3, new | States only the exceptional comparison mate identity. |

`python3 tools/downstream.py Sheaf.Paper.AdicNormalizedPurityLift` reports zero current downstream modules. A repository-wide declaration search finds only the item itself. This is not a withdrawal: the parent DAG dependency remains intact and the assigned theorem is retained with its exact signature. Target semantics do not change.

## Status

landed 20261025T095710-L-3469215 2026-10-25 (merge of deliver/P3/Sheaf.Paper.AdicNormalizedPurityLift)
