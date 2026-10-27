## What changed

Filled `WeilConjectures.SemilinearSections.semilinearGeometryEvaluation` by constructing
both comparisons as the canonical adjunction mates. Mathlib's mate unit and counit
identities give the two evaluation equations; `unit_mateEquiv_symm` and
`Adjunction.homEquiv_unit` give the coefficient transpose equation.

Added three proved supporting modules:

- `Sheaf.Paper.GeometricCoefficientPullback`: the actual scalar restriction mate is
  invertible. Its ordinary normalization comes from
  `exists_scalarInverseImageIndependent`; the two `ScalarData.transpose_model`
  equations identify its derived mate on flat-term K-flat representatives. Private
  helpers preserve the common resolving class; the exact-square and pointwise
  mate comparison helpers are reused from `ScalarEvaluationTransposeExistence`.
- `Sheaf.Paper.GeometricOrdinaryEvaluationMate`: the recorded ordinary push-evaluation
  isomorphism and `ordinary_unit_evaluation` identify the ordinary geometric mate.
  Mathlib's iterated-mates identity and reflection under conjugation then prove
  singleton mate invertibility for any ordinary singleton adjunctions.
- `Sheaf.Paper.GeometricEvaluationMate`: transport ordinary singleton extension through
  `strictSystemSequenceEquivalence`, derive it using
  `nonempty_normalizedLeftExtension`, and apply `derivedExtensionMate_isIso` on the
  common flat-term K-flat resolving class. A second iterated-mates identity gives
  invertibility of the canonical derived geometric evaluation mate.

The private singleton construction chooses a normalized universal derived pair;
its universal property determines it up to the comparison isomorphism used in the
proof. It does not choose arbitrary module data from a mere existence assertion.
All proof imports are private. Existing declaration signatures and public imports
are preserved, and no existing module other than the assigned item is changed.

## Proved and sorry left

Closed the item's one original hole:
`WeilConjectures.SemilinearSections.semilinearGeometryEvaluation`
(`lem-coef-semilinear-geometric-derived-evaluation`).

The three added public theorems are proved:
`WeilConjectures.SemilinearSections.geometricCoefficientPullbackMate_isIso`,
`WeilConjectures.SemilinearSections.geometricOrdinaryEvaluationMate_isIso`, and
`WeilConjectures.SemilinearSections.geometricEvaluationMate_isIso`.

Holes closed: 1. Holes added: 0. Sorries left in delivered modules: 0.

Validation: all four files compiled through `lcompile.py` in dependency order.
The final item compiled in 10.7 seconds; the slowest supporting file took 31.7 seconds.
There were no compiler warnings in the accepted runs.
The proof uses the existing declared K-flat, scalar, and normalized-extension theory
with its current proofs; it does not assert that every transitive dependency is
already axiom-free.

## No longer needed

The assigned module originally had no proof-dependency imports to remove.
Its original public import is retained. The following planned dependencies are
unused by this proof and removed from this node's direct proof dependencies:

- `lem-pur-system-singleton-geometric-pullback`
  (`Sheaf.CategoryTheory.SystemSingletonGeometricPullback`): ordinary push-evaluation
  and its unit normalization already make the ordinary singleton mate invertible.
  Its normalized derivation follows directly from the existing general extension
  comparison, so no construction and transport of an existential strict-system
  geometric realization is needed.
- `lem-pur-system-evaluation-scalar-restriction-normalization`
  (`Sheaf.CategoryTheory.SystemEvaluationScalarRestrictionNormalization`): the
  actual evaluation mate is used directly. Mathlib's unit and counit identities
  give the required normalization equations, and the scalar transpose is proved
  separately for the supplied `ScalarData` adjunctions.

The ordinary scalar inverse-image and ringed-topos K-flat pullback nodes remain
needed. Ordinary singleton extension, its sequence-site equivalence, and the
normalized left-extension theory remain needed. No module is withdrawn, and the
unit statement and its route are retained.

The complete difference of the old and revised dependency closures for this item
is the following 54 nodes. The module column records their Lean attachment;
no files are withdrawn in this delivery.

| Node removed from this item’s DAG closure | Lean module |
| --- | --- |
| `def-galois-exact-functor` | `Mathlib / no module attachment` |
| `def-galois-finite-limits-colimits` | `Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits` |
| `def-pur-system-evaluation-normalization-data` | `Sheaf.CategoryTheory.SystemEvaluationNormalizationData` |
| `def-trf-abelian-inverse-image-presentation` | `Sheaf.CategoryTheory.Sites.AbelianInverseImagePresentation` |
| `def-trf-geometric-morphism` | `Sheaf.CategoryTheory.Sites.GeometricMorphism` |
| `def-weil-pbc-ringed-topos-morphism` | `Sheaf.CategoryTheory.RingedToposMorphism` |
| `def-weil-pbc-topos` | `Sheaf.CategoryTheory.Sites.GrothendieckTopos` |
| `lem-grothendieck-derived-has-coproducts` | `Sheaf.CategoryTheory.GrothendieckDerivedCoproducts` |
| `lem-pur-adjunction-evaluation-composition` | `Sheaf.CategoryTheory.DerivedCategory.AdjunctionEvaluationComposition` |
| `lem-pur-adjunction-transition-coherence` | `Sheaf.CategoryTheory.DerivedCategory.AdjunctionTransitionCoherence` |
| `lem-pur-coefficient-comparisons-balanced-construction` | `Sheaf.SecSmoothPurity.CoefficientComparisonsBalancedConstruction` |
| `lem-pur-diagram-ring-restriction-pushforward` | `Sheaf.CategoryTheory.DiagramRingRestrictionPushforward` |
| `lem-pur-exact-derived-coproducts` | `Sheaf.CategoryTheory.DerivedCategory.ExactFunctorCoproducts` |
| `lem-pur-exact-derived-mate` | `Sheaf.CategoryTheory.DerivedExactMate` |
| `lem-pur-inverse-image-scalar-restriction-comparison` | `Sheaf.CategoryTheory.InverseImageScalarRestrictionComparison` |
| `lem-pur-ringed-site-grothendieck-coefficient-universe` | `Sheaf.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse` |
| `lem-pur-system-coproducts` | `Sheaf.CategoryTheory.SystemCoproducts` |
| `lem-pur-system-derived-subsequence` | `Sheaf.CategoryTheory.SystemDerivedSubsequence` |
| `lem-pur-system-derived-subsequence-evaluation-composition` | `Sheaf.CategoryTheory.SystemDerivedSubsequenceEvaluationComposition` |
| `lem-pur-system-derived-subsequence-transition` | `Sheaf.CategoryTheory.SystemDerivedSubsequenceTransition` |
| `lem-pur-system-derived-transition` | `Sheaf.CategoryTheory.SystemDerivedTransition` |
| `lem-pur-system-derived-transition-coherence` | `Sheaf.CategoryTheory.SystemDerivedTransitionCoherence` |
| `lem-pur-system-derived-transition-unit` | `Sheaf.CategoryTheory.SystemDerivedTransitionUnit` |
| `lem-pur-system-evaluation-scalar-restriction-normalization` | `Sheaf.CategoryTheory.SystemEvaluationScalarRestrictionNormalization` |
| `lem-pur-system-geometric-derived-lift` | `Sheaf.CategoryTheory.SystemGeometricDerivedLift` |
| `lem-pur-system-geometric-ordinary-comparison` | `Sheaf.CategoryTheory.SystemGeometricOrdinaryComparison` |
| `lem-pur-system-grothendieck` | `Sheaf.CategoryTheory.SystemGrothendieck` |
| `lem-pur-system-level-left-extension` | `Sheaf.CategoryTheory.SystemLevelLeftExtension` |
| `lem-pur-system-ordinary-selected-extension` | `Sheaf.CategoryTheory.SystemOrdinarySelectedExtension` |
| `lem-pur-system-restriction-mate-coherence` | `Sheaf.CategoryTheory.SystemRestrictionMateCoherence` |
| `lem-pur-system-scalar-derived-extension` | `Sheaf.CategoryTheory.SystemScalarDerivedExtension` |
| `lem-pur-system-selected-derived-composition` | `Sheaf.CategoryTheory.SystemSelectedDerivedComposition` |
| `lem-pur-system-selected-derived-composition-evaluation` | `Sheaf.CategoryTheory.SystemSelectedDerivedCompositionEvaluation` |
| `lem-pur-system-selected-derived-evaluation` | `Sheaf.CategoryTheory.SystemSelectedDerivedEvaluation` |
| `lem-pur-system-selected-derived-evaluation-index` | `Sheaf.CategoryTheory.SystemSelectedDerivedEvaluationIndex` |
| `lem-pur-system-selected-derived-extension` | `Sheaf.CategoryTheory.SystemSelectedDerivedExtension` |
| `lem-pur-system-selected-derived-transition` | `Sheaf.CategoryTheory.SystemSelectedDerivedTransition` |
| `lem-pur-system-single-derived-evaluation` | `Sheaf.CategoryTheory.SystemSingleDerivedEvaluation` |
| `lem-pur-system-singleton-evaluation-mate` | `Sheaf.CategoryTheory.SystemSingletonEvaluationMate` |
| `lem-pur-system-singleton-geometric-pullback` | `Sheaf.CategoryTheory.SystemSingletonGeometricPullback` |
| `lem-pur-system-singleton-scalar-extension` | `Sheaf.CategoryTheory.SystemSingletonScalarExtension` |
| `lem-pur-system-tensor-coherence` | `Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic` |
| `lem-trf-geometric-inverse-image-exact` | `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact` |
| `lem-weil-pbc-diagram-site-module-equivalence` | `Sheaf.CategoryTheory.DiagramSiteModuleEquivalence` |
| `lem-weil-pbc-diagram-site-realization` | `Sheaf.CategoryTheory.DiagramSiteRealization` |
| `lem-weil-pbc-diagram-site-sheaf-equivalence` | `Sheaf.CategoryTheory.DiagramSiteSheafEquivalence` |
| `lem-weil-pbc-diagram-site-topology` | `Sheaf.CategoryTheory.DiagramSiteTopology` |
| `lem-weil-pbc-geometric-ring-transport` | `Sheaf.CategoryTheory.GeometricRingTransport` |
| `lem-weil-pbc-kinjective-total-derived` | `Sheaf.CategoryTheory.KInjectiveTotalDerived` |
| `lem-weil-pbc-restriction-ringed-topos-module-direct-image` | `Sheaf.CategoryTheory.RestrictionRingedToposModuleDirectImage` |
| `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` | `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition` |
| `lem-weil-pbc-ringed-topoi-module-adjunction` | `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction` |
| `lem-weil-pbc-supplied-ringed-topos-kflat-pullback` | `Sheaf.CategoryTheory.RingedToposKFlatPullback` |
| `lem-weil-pbc-tower-derived-evaluation-normalization` | `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization` |

## Where the brief, the DAG or earlier work was wrong

The planned route overlooks information already present in `GeometryOrdinary`:
`ordinaryPushEvaluation` and `ordinary_unit_evaluation` determine an invertible
ordinary geometric mate. Taking mates a second time gives the singleton mate
without reconstructing an arbitrary strict-system realization or proving its
transition transport. This is a shorter route from the stated declarations.
No statement is disputed and no target or shared definition is changed.

## New nodes

`lem-coef-geometric-coefficient-pullback-mate` records the proved normalized scalar
mate and its common K-flat representative argument in
`Sheaf.Paper.GeometricCoefficientPullback`.

`lem-coef-geometric-ordinary-evaluation-mate` records the proved ordinary unit and
iterated-mates shortcut in `Sheaf.Paper.GeometricOrdinaryEvaluationMate`.

`lem-coef-geometric-evaluation-mate-invertible` records the proved normalized
singleton derivation and derived iterated-mates argument in
`Sheaf.Paper.GeometricEvaluationMate`.

All three nodes have source references, complete proofs in words, Lean attachments,
and LeanSearch, Loogle or LeanFinder, and Mathlib-source search records.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
