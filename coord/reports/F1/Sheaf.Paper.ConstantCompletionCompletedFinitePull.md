## What changed

Replaced the sorry in `CategoryTheory.ConstantCompletion.completedFinitePull_existsUnique`
with a complete proof from a named ordinary finite-reduction assertion. A private categorical
helper applies finite extension to the representative comparison square, pastes naturality
of its computation counit, and cancels invertible computation maps. A second helper uses flat
scalar restriction, preservation of flat-term K-flat complexes by pullback, and resolving-class
descent to prove invertibility on every derived object. Compose the inverse of that reduced
comparison with the existing `finitePull`. Cancellation proves its inverse formula and uniqueness.
The original theorem signature is unchanged.

Added `Sheaf.Paper.ConstantCompletionOrdinaryReducedPull`, containing the remaining ordinary
assertion and its source-based proof plan. This is a normalization bridge to the existing
`CommonQuotientPullback.ordinary_insertion_reduction_isIso`: constructing its bundled geometric,
scalar-presentation and quotient data, and transporting to these specified functors, remains.
The derived argument is fully proved here. Updated step 4 of the aggregate node while retaining
all its other completion, tower and coherence clauses.

Compilation by lcompile.py passed: new module 5.6 s; item and full derived reduction 7.6 s.
Delivery repeats the compile and axiom checks. No shared definition, existing statement,
instance or public import is changed.

## Proved and sorry left

Closed: `CategoryTheory.ConstantCompletion.completedFinitePull_existsUnique` (1 of 1 original
holes). Added: `CategoryTheory.ConstantCompletion.ordinaryReducedPull_isIso` (1 hole), node
`lem-weil-pbc-constant-completion-ordinary-reduced-pull`.
The item has zero sorries; both private helpers are fully proved.
This is a decomposition: one upper hole closed, one ordinary lower hole added, net zero.
Pre-existing holes in imported flatness, resolution and comparison statements are not claimed
closed.

## No longer needed

Removed these direct private imports from the item; necessary transitive dependencies remain
available through the coefficient-completion modules:

- `Mathlib.CategoryTheory.Adjunction.Additive`
- `Mathlib.CategoryTheory.Adjunction.Whiskering`
- `Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`
- `Mathlib.RingTheory.Finiteness.Defs`
- `Mathlib.RingTheory.Ideal.Span`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.Paper.RingedTopoiTensorSections`
- `WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `WeilConjectures.CategoryTheory.NatTransFromResolvingClass`

No declaration, node or module is withdrawn. No aggregate proof dependency is pruned, since the
node describes other completion, tower, composition and identity clauses too. This finite
comparison itself needs no limit, quotient-unit or composition-coherence argument after the
ordinary reduced map is invertible. Public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The live server queue has a proof/route row, with no rework or
build-error entry for the item. The aggregate node's primary attachment remains on
`ConstantCompletionCore` for `equivalence`; its declarations list includes this theorem, whose
actual file is `ConstantCompletionCompletedFinitePull` as assigned.

The original sketch omitted the formal passage from the ordinary comparison to the specified
derived comparison, and the normalization bridge to the general common-quotient data. The former
is now proved. The latter is isolated as an ordinary statement with its exact argument in words.
It mentions no complexes, derived categories, resolving representatives, finitePull or uniqueness;
it is strictly one step of the original argument.

Edge cases: I=0 gives unchanged coefficients; I=A and the zero ring give the zero quotient-module
category; n=0 gives the first quotient. The argument uses sheafification and inverse-image
adjunction, and does not assume surjectivity on sections after inverse image, nonzero coefficients,
bounded complexes or enough points. The unit route is unchanged. Read the current blueprint's
completed-pullback finite-reduction proof, Stacks sites-modules.tex lemmas tensor-product-pullback
and completion-flat, and sites-cohomology.tex lemma-derived-base-change.

## New nodes

`lem-weil-pbc-constant-completion-ordinary-reduced-pull` records invertibility of the chosen
ordinary scalar insertion after finite scalar extension. The proof plan constructs compatible
common quotients, normalizes the chosen functors and applies/transports the existing ordinary
insertion theorem. The generic theorem uses different bundled data, so this is not a one-line
specialization in Lean. LeanSearch, LeanFinder, Loogle and Mathlib grep were run and logged; none
supplies this sheaf comparison. Blueprint searches for scalar insertion and common quotient
found no imported statement. The new module is its sole realization.
No change record is needed, since no existing definition or statement is repaired.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionCompletedFinitePull": "d26200a9c7bbd078709a28a768c28421c7de7f6a", "Sheaf.Paper.ConstantCompletionOrdinaryReducedPull": "cb2aca6c1cd8446be07b0558fb5b72e2af6d61d4"}, "results": {"Sheaf.Paper.ConstantCompletionEquivalence": {"hash": "d1c42681af0d8d17deb982fbdd20171738a2637f", "status": "OK"}}, "seconds": 297, "time": "2026-10-27T23:33:18+0800", "transitive": 0, "version": 1}
```

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
