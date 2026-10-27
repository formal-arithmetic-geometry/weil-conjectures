## What changed

Replaced the hole in `WeilConjectures.PurCompactSupport.compactSupportProjectionCoefficientChange`
by an explicit proper/open pasting proof. The proper coefficient mate is identified with the
geometric mate of `scalarPull.inv` using iterated mates and uniqueness of left adjoints.
The generic proved `tensor_mate_coherence` supplies the proper projection square, and the
component normalization equations identify the exact projection maps in the statement.
Naturality and `comparison_factorization` paste the two factor equations.

Added two statement modules: `Sheaf.Paper.ScalarPullTensorCoefficientCoherence` and
`Sheaf.Paper.OpenProjectionFactorCoefficientChange`. Their statements respectively concern
only the four left adjoints and only the open tensor factor including its compositor.
Neither is the assigned compact-support equation under another name. Both have complete
proofs in words, source places, and nodes. All added imports in the item are proof-only.
Explicit component source/target annotations avoid repeated normalization of curried
projection functors. Local irreducibility attributes keep derived constructions folded,
and the item now uses Lean's default transparency settings. No execution limit is raised.
The original theorem signature and existing docstring are unchanged. No source-library
module, target, definition, consumer, or unit record changes.

## Proved and sorry left

Decomposition: the original hole in
`WeilConjectures.PurCompactSupport.compactSupportProjectionCoefficientChange` is closed from
two strictly smaller statements. The proper mate identification and the complete
proper/open assembly contain no `sorry`.

Two holes added, one per new module:

- `WeilConjectures.PurCompactSupport.scalarPull_tensor_coefficient_coherence`
  (`lem-sf-scalar-pull-tensor-coefficient-coherence`): binary tensor coherence for scalar
  extension and geometric pullback; no projection or proper image.
- `WeilConjectures.PurCompactSupport.openProjectionFactor_coefficient_change`
  (`lem-sf-open-projection-factor-coefficient-change`): the open-unit tensor square and its
  pullback compositor; no proper direct image or proper projection.

There are no holes left in the assigned module. This is one hole reduced to two, hence
net minus one hole rather than a completed proof of the whole argument. The imported
library's existing holes are unchanged.

## No longer needed

The direct dependency on `lem-fix-operation-reduction` is removed: no arithmetic
coefficient system, constructibility, completion, field extension, or bounded-domain
reduction theorem is used. `Sheaf.Paper.BasicOperationsCoefficientReduction` is not imported.

The direct dependency on `lem-sp-intrinsic-open-projection-invertible` moves into the new
open-factor node, where the open inverse is used. It remains needed there and is not
claimed as globally pruned. The ringed exchange module remains needed for its proved
generic categorical tensor/mate identity. The new tensor node retains the representative
ringed-square calculation and resolving-class descent dependencies.

The exploratory imports of `Sheaf.Paper.ProjectionScalarSquare` and
`Sheaf.Paper.CompactSupportStrictScalarMate` are absent from the final file. The former's
formal pasting calculation is written directly to avoid its DAG cycle through the broad
completed coefficient theorem. The latter's generic mate identification is replaced by
a short proof from Mathlib's iterated-mate theorem. No unrelated arithmetic lemmas enter
the proof. No module is withdrawn, and no claim of globally unreachable modules is made.

## Where the brief, the DAG or earlier work was wrong

The planned proper/open argument is valid, but the broad arithmetic operation-reduction
signature does not directly supply this arbitrary ring-sheaf binary tensor square.
The missing normalization calculations are now explicit statements with the exact maps.

The existing generic `projection_scalar_square` is proved, but its DAG record depends on
`lem-pur-compact-support-integral-coefficient-comparison`, whose proof route returns to this
item through `lem-pur-compact-support-scalar-projection-identification`. Reusing that DAG
edge would create a cycle. The delivery instead writes the formal pasting calculation in
the item, and uses only the defining coefficient data plus the two smaller identities.
No other group's node is changed. An overlay dependency traversal confirms that each new
proof dependency is acyclic relative to the assigned node.

Edge-case review: the two statements use arbitrary unbounded inputs and derived scalar
extension. Zero inputs and empty opens give the same zero maps, identity coefficient
changes obey the unit formulas, and nonflat coefficient quotients introduce no flatness
assumption. The proof never cancels a proper projection or a coefficient comparison.
Arbitrary representative-normalized tensor models remain in every statement.

## New nodes

`lem-sf-scalar-pull-tensor-coefficient-coherence` records the tensor equation before
transposition. Its proof normalizes the coefficient pullback comparison on flat K-flat
representatives, checks the balanced pure tensors, then descends. It is strictly a
left-adjoint calculation and cannot imply the compact-support square without the mate
and open-factor arguments.

`lem-sf-open-projection-factor-coefficient-change` records the separate open factor and
geometric compositor. Its proof uses the open unit normalization, the preceding tensor
coherence, invertibility of the open projection, and uniqueness of composite adjoints.
It has no proper image functor or proper counit projection. Blueprint and Mathlib searches
found only constant-coefficient or restricted-domain specializations, not these generic
statements. No change record is needed: all existing interfaces are unchanged.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
