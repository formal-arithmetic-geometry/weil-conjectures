# WeilConjectures.AmbientPullbackTensor.TensorData

## Reason

The kernel spends about 30 seconds checking the specialized structure alone because its
field types unfold the selected ambient pullback and derived functor. Use the same two-field
structure parameterized by an abstract exact functor and specialize it by an abbreviation.
The fields and normalization have the same mathematical content. No source-library declaration
or target signature changes. Constructors and projections are supplied by the generic bundle;
current consumers eliminate the existence theorem and read its normalization.
The downstream search also lists unrelated short-name matches; these are identified below.
The targets using this definition require renewed statement review of this equivalent
representation. No consumer adaptation is needed. Both unchanged consumers compiled.
The new generic definitions record the same comparison data; the existing node
retains its mathematical statement and original statement dependencies.

## Old

```lean
structure TensorData {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ)
    (A : Tensor ell E Y s) (B : Tensor ell E X s)
    (TA : TensorModels ell E Y s A) (TB : TensorModels ell E X s B) where
  /-- Canonical derived tensor comparison. -/
  mu : A.tensor ⋙ derivedPull ell E f s ≅
    ((derivedPull ell E f s).prod (derivedPull ell E f s)) ⋙ B.tensor
  /-- Signed total map and its representative localization equation. -/
  model : TensorComparisonModel.{t + 1, t, u} (topology Y s) (topology X s)
    (coefficients ell E Y s) (coefficients ell E X s) (pull ell E f s) A B TA TB mu
```

## New

```lean
abbrev TensorData {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ)
    (A : Tensor ell E Y s) (B : Tensor ell E X s)
    (TA : TensorModels ell E Y s A) (TB : TensorModels ell E X s B) :=
  BundledTensorComparison.{t + 1, t, u} (topology Y s) (topology X s)
    (coefficients ell E Y s) (coefficients ell E X s) (pull ell E f s) A B TA TB
```

The generic `WeilConjectures.SemilinearSections.BundledTensorComparison` has exactly the
original `mu` and dependent `model` fields.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AmbientPullbackTensorCoherence | Y9 | Specializes the generic structure; proof uses its two fields. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | Search hit is SpTowerP1.TensorData, a different declaration; unaffected. |
| Sheaf.Paper.SmoothPurityTowerGamma | Q4 | Search hit is SpTowerP1.TensorData, a different declaration; unaffected. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | F9 | Defines its own SpTowerP1.TensorData; unaffected. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed | Search hit is SpTowerP1.TensorData, a different declaration; unaffected. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Search hit is SpTowerP1.TensorData, a different declaration; unaffected. |
| Sheaf.SixFunctors.CompositionProjectionData | unclaimed | Defines its own TensorData in a different namespace; unaffected. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Uses CompositionProjectionData.TensorData, a different declaration; unaffected. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | C2 | Uses CompositionProjectionData.TensorData, a different declaration; unaffected. |
| Sheaf.SixFunctors.SemilinearOpenExternalCoherence | unclaimed | Defines its own TensorData in a different namespace; unaffected. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed at inspection | Uses tensorData_existsUnique and its flat-representative consequence; no edit. |
| Sheaf.Paper.IntegralExpressionSystemComparison | unclaimed at inspection | Uses tensorData_existsUnique and its flat-representative consequence; no edit. |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed at renewed inspection | Uses SpTowerP1.TensorData, a different declaration; unaffected. |
| Sheaf.Paper.OrderedTowerOrientation | unclaimed at renewed inspection | Uses SpTowerP1.TensorData, a different declaration; unaffected. |
| Sheaf.Paper.SmoothPurityTowerGammaData | unclaimed at renewed inspection | Uses SpTowerP1.TensorData, a different declaration; unaffected. |
| Sheaf.Paper.SmoothPurityTowerP1Data | unclaimed at renewed inspection | Uses SpTowerP1.TensorData, a different declaration; unaffected. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | unclaimed at renewed inspection | Uses SpTowerP1.TensorData, a different declaration; unaffected. |
| Sheaf.Paper.TensorTransposeTowerNaturality | unclaimed at renewed inspection | Uses SpTowerP1.TensorData, a different declaration; unaffected. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed at renewed inspection | Uses SpTowerP1.TensorData, a different declaration; unaffected. |
| Sheaf.Paper.TowerTensorTransposeWords | unclaimed at renewed inspection | Uses SpTowerP1.TensorData, a different declaration; unaffected. |

## Status

landed 20261026T071609-L-3954447 2026-10-26 (merge of deliver/Y9/Sheaf.Paper.AmbientPullbackTensorCoherence)
