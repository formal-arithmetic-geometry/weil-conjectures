## What changed

Completed the five clauses of `Sheaf.Paper.CompletedExchangeCoherence`: ordinary and
completed identity comparisons, naturality, and horizontal and vertical pasting. The
proof uses unit reflection, the ordinary exchange equations, and the completion-unit
extension equation. The ordinary comparison declarations were relocated unchanged to
`CompletedOrdinaryComparisons` so the ordinary coherence statement can be imported
without a cycle. Two strictly smaller supporting results remain named statements in separate modules,
each with its own DAG node. A third new intermediate result, `completedExchange_unit`,
is proved in full from the published projection-unit equation by adjunction calculus.

The sandbox compiles all five Lean modules with `lcompile.py --all`, without warnings.
The required delivery dry run passed and produced review commit `a9eec94211` (before the exchange-unit proof was completed).
The original public API is reexported with the same signatures and definition bodies.
Unchanged consumer checks passed for `CompleteCompactSupportProetale`,
`CondensedERealization`, `ExchangeFunctoriality`, and `SystemPrimitiveComparisonShift`.
`ExtensionZeroPerfectModelTransport` timed out both against the sandbox and against
the unchanged published library (each at 60 seconds). It is not a forced adaptation
caused by these unchanged comparison signatures; no consumer file is delivered.
The relocation record is `coord/changes/CompletedOrdinaryComparisons.md`.

## Proved and sorry left

The item declarations proved are `integralRingIso_comp`,
`modulePushId_existsUnique`, `completedPullComp_existsUnique`, `completedPullId_existsUnique`,
`completedExchange_naturality`, `completedExchange_identity_horizontal`,
`completedExchange_identity_vertical`, `completedExchange_horizontal`, and
`completedExchange_vertical` (9 of the 9 original item sorries).

The two split-off declarations still contain their explicitly named `sorry`s:

- `AdicCoefficientDatum.completedPull_reflection`, node
  `lem-weil-pbc-completed-pullback-reflection`;
- `AdicCoefficientDatum.integralExchange_coherence`, node
  `lem-weil-pbc-ordinary-ringed-exchange-coherence`.

Closed 9 original holes and added 2 holes. The new theorem
`AdicCoefficientDatum.completedExchange_unit` has no hole. Its private generic mate
lemmas and `ordinaryToCompleted_reduction` are also fully proved.

This is a decomposition: each retained split statement is a proper intermediate result used by
the completed proof, and the item proof combining them is complete.

## No longer needed

No whole downstream module is claimed pruned. The direct proof-only imports removed
from the item are `Mathlib.CategoryTheory.Adjunction.Mates`,
`Mathlib.CategoryTheory.Adjunction.Limits`,
`Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`,
`Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism`,
`Sheaf.Paper.ConstantCompletionEquivalence`,
`Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`, `Sheaf.Paper.CompletedPullback`,
`Sheaf.Paper.CompletedDirectImageLimits`, `Sheaf.Paper.CompletedRlimFunctor`,
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
`Sheaf.Paper.CompletedPullbackAdjunction`, `Sheaf.Paper.ProEtaleConstantReductionTower`,
and `Sheaf.Paper.StrictTowerExchangeMateNormalization`.

The original node proof dependencies not used directly by the assembled proof are
`def-weil-pbc-adjunction-conjugate`, `def-weil-pbc-adjunction-mate`,
`lem-sp-completed-pullback-adjunction`, `lem-sp-completion-mate-comparison`,
`lem-weil-pbc-cartesian-square-pasting`, `lem-weil-pbc-constant-completion-equivalence`,
`lem-weil-pbc-mate-pasting`, `lem-weil-pbc-right-adjoint-preserves-kinjective`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`lem-weil-pbc-strict-tower-exchange-mate-normalization`, and
`prop-weil-pbc-rlim-functoriality`. Some remain dependencies of the retained lower
statements. The original node drops its obsolete two explicit tool approvals because
neither generic tool is applied directly in its Lean proof. The new proved unit lemma
uses `unit_conjugateEquiv` and the already stated projection-unit equation directly,
so it also drops `prop-weil-pbc-rlim-functoriality` as a direct proof dependency.

The item proof no longer imports `CompletedRlimFunctor`, `CompletedTowerPullback`,
`CompletedPullback`, `CompletedDirectImageLimits`, `CompletedTowerCorners`,
`ConstantCompletionEquivalence`, `CompletionMateComparison`,
`StrictTowerExchangeMateNormalization`, or `Triangulated.DerivedLimitLevelwiseIsomorphism`
directly; those declarations remain available through the retained dependency modules.
The old monolithic ordinary declarations are no longer needed in the item module and are
provided by `CompletedOrdinaryComparisons`.

## Where the brief, the DAG or earlier work was wrong

The original attempted compile expanded `ordinaryToCompleted` through the large derived
limit definitions and exceeded the server response window. The proof now uses an explicit
natural transformation with the same components and keeps the ordinary comparison definitions
irreducible during elaboration. The blueprint's ordinary coherence step was not exposed
as a Lean declaration, so it is split as a separate strictly smaller intermediate node.
The existing finite constant-coefficient pasting theorem does not state ambient ringed
pasting with these completed coefficient sheaves and comparisons.

The completion reflection split is also a genuine separate result: the published
strict-tower/intrinsic completion comparison assumes a complete input, while the
composition comparison here needs reflection for arbitrary ambient inputs. The general
constant-completion reflector has the small-site universe convention and requires a
unit-preserving transport to the actual pro-etale completed coefficient category.
The retained lemma states precisely that reflection property. Neither retained split
restates any completed exchange identity or pasting law.

## New nodes

`lem-weil-pbc-completed-ordinary-comparisons` records the proved relocated ordinary
coefficient cocycle and module identity uniqueness, together with their existing
comparison definitions. The change record is
`coord/changes/CompletedOrdinaryComparisons.md`.

`lem-weil-pbc-completed-pullback-reflection` records the completion reflector property
needed to reflect equalities through the completed pullback unit.

`lem-weil-pbc-completed-exchange-unit` records the equality extending ordinary exchange
along the completion units. This node is now proved, by transposing the existing
projection-unit equation, cancelling the strict H factors before taking derived limit,
and applying naturality.

`lem-weil-pbc-ordinary-ringed-exchange-coherence` records the four ordinary identity and
pasting equations used before adjoining completion.

The three intermediate statements were checked on zero input, zero coefficient ring, zero
ideal, unit ideal, empty schemes, and identity squares. The reflection statement then
reduces respectively to the trivial Hom bijection, identity reflection, or reflection
onto zero. The exchange-unit equation becomes ordinary naturality for zero ideal and
the zero equation for unit ideal. Ordinary pasting uses no completion condition and
retains its identity/composition isomorphisms in every case. These are mathematical
edge-case checks, not additional asserted Lean tests.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
