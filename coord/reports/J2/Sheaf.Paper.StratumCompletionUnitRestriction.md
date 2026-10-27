## What changed

Proved `AlgebraicGeometry.Scheme.stratumReduction_augmentation` in the assigned module.
The proof uses two new, fully proved supporting theorems:

- `derivedReduction_augmentationOfCounits` in
  `Sheaf.Paper.DerivedReductionAugmentationCompatibility` proves the generic
  augmented-square equation from exact localization factors, computing counits,
  normalized derived units and the ordinary augmented square.
- `completedReduction_augmentationOfComparison` in
  `Sheaf.Paper.ReductionAugmentationCompatibility` specializes this to the actual
  completed coefficient categories and the published quotient augmentations.

The generic proof checks equality on resolving complexes by cancelling the
invertible target counit. Both unit normalizations, the ordinary augmented square
and naturality then identify the paths. Fully faithful restriction extends the
equation to every derived object. The specialization uses K-flat resolutions with
flat terms and the existing computing-counit theorem. The item supplies its chosen
ordinary comparison, its derived normalization and its existing K-flat pullback proof.
Three additional private helpers prove the exact-square factor identity and convert
the published unit normalization to its complex-counit form.

All existing public signatures, definitions, imports and other proofs are retained.
The new item import is private. No consumer adaptation is required. Local
irreducibility protects the large coefficient and derived-functor constructions;
the coefficient-alias conversion and concrete specialization are checked in support
modules to keep each file within the compilation limit. No profiling or linter
suppression options are retained.

The launcher's leanfinder, loogle and grep searches and repository searches found
no existing augmented four-functor statement. The proof reuses the localization
factors and resolving-representative API. The related argument in
ReductionPullbackDerivedTower supplied the categorical route.
CompletedDirectImageLimits imports this item, so its comparison results would create
a cycle. The item's DAG records the actual route through the two proved new nodes.
No unit or chapter route changes.

Validation: `lcompile.py --all` compiles all three files without warnings.
The generic module takes 5.3 seconds, the specialization 31.2 seconds and the
item 25.3 seconds. Every file is below the 60-second limit.

## Proved and sorry left

Closed one of the five original holes:
`AlgebraicGeometry.Scheme.stratumReduction_augmentation`.
Added zero holes and split off zero unproved statements. Both new modules contain
zero `sorry` declarations.

Four original holes remain unchanged, all attached to
`lem-weil-pbc-stratum-completion-unit-restriction`:

- `AlgebraicGeometry.Scheme.stratumModuleReductionIso_exists`.
- `AlgebraicGeometry.Scheme.stratumReduction_normalization`.
- `AlgebraicGeometry.Scheme.stratumReduction_evaluation`.
- `AlgebraicGeometry.Scheme.stratumRlimComparison_isIso`.

The augmentation proof uses the existing ordinary comparison obligation as intended
by stage 3. It adds no replacement assumption or renamed obligation.

## No longer needed

None. No imports, nodes or modules are pruned. The remaining ordinary comparison,
finite normalization, evaluation and inverse-limit obligations still need the
recorded dependency routes. The new proof uses existing mathematical dependencies
through its two proved supporting theorems.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The DAG previously described strict
augmentation compatibility as an outstanding obligation; it is now proved from
the existing ordinary and derived normalizations. The coefficient ring and universal
counit each have two published definitionally equal aliases. Their concrete
conversion is expensive, so it is confined to the specialization support module.
No shared definition or statement is changed.

## New nodes

- `lem-weil-pbc-derived-reduction-augmentation-of-counits`: the fully proved generic
  compatibility theorem, with all resolving-class and normalization hypotheses
  explicit. Its source is the representative derived-base-change argument of
  Stacks Tag 06YY and the ordinary square of Tag 03EL.
- `lem-weil-pbc-completed-reduction-augmentation-of-comparison`: the fully proved
  specialization to the existing completed reduction functors and chosen units.
  Its proof uses the generic node, existing K-flat resolutions and computing counits.

Each new node has the verbatim Lean declaration signature, source, complete proof
steps, dependencies and three recorded Mathlib searches. Neither introduces an
unproved mathematical statement or changes the unit route.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
