## What changed

Proved the uniqueness part of both normalized finite comparisons in
AlgebraicGeometry.Scheme.cbcFiniteComparisons_existsUnique. Finite model maps are
invertible on K-flat representatives by the existing scalar-extension counit theorem.
Cancel those maps in the normalization equations. For an arbitrary complex, take a
K-flat resolution and use naturality to cancel its invertible derived image.
Existence of the two comparisons is isolated as the strictly smaller theorem
AlgebraicGeometry.Scheme.cbcNormalizedFiniteComparison_exists, with its own module
and node. This is a decomposition, not a net hole reduction.

Moved the five unchanged representative-model definitions and normalization predicates
to Sheaf.Paper.CompletedFiniteComparisonModels, publicly imported from the original
module, to avoid an import cycle. Signatures, attributes and bodies remain verbatim.
The change record is coord/changes/W4-finite-comparison-models.md.

Validation: all three packet modules compile through lcompile.py on the published
server build (13.7 s, 3.9 s and 14.9 s respectively). Both unchanged downstream
consumer modules also compile against the packet (14.0 s and 20.0 s).

## Proved and sorry left

Original holes: 2. Closed in the item:
AlgebraicGeometry.Scheme.cbcFiniteComparisons_existsUnique, reduced to existence
with a complete uniqueness proof. Added: 1 hole,
AlgebraicGeometry.Scheme.cbcNormalizedFiniteComparison_exists
(lem-cbc-normalized-finite-comparison-existence).
Remaining original hole: AlgebraicGeometry.Scheme.completedRingStrictFiniteExchange
(lem-cbc-completed-ring-strict-finite-exchange), untouched.
Total packet holes: 2; net reduction: 0. No hollow definitions or private holes.

## No longer needed

No mathematical dependency or module is pruned. The unfinished original exchange proof
still needs its recorded dependencies. The new uniqueness argument needs only the
normalized existence theorem, finite model definitions, scalar-extension counit
invertibility, K-flat resolutions and localization naturality. Two redundant public imports were removed from the new existence module because
the model module already exports them. No existing consumer import is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original proof plan omits the separate uniqueness
argument required by the Lean existence-and-uniqueness declarations. That argument is
now fully written in Lean. The remaining existence proof still requires transport of
the stated finite-evaluation and strict-reduction comparisons to these precise models.
Edge cases of the uniqueness proof: zero complex and empty open require no extra
hypotheses; the argument is unbounded and uses only K-flat resolution and cancellation.
The new existence statement has the original quantifiers and normalizations with only
uniqueness removed, and is true in those same edge cases.

## New nodes

`def-cbc-finite-comparison-models` records the five original model definitions and
normalization predicates moved unchanged into their common dependency module.
`lem-cbc-normalized-finite-comparison-existence` isolates existence of the two normalized
comparison isomorphisms from uniqueness; its proof follows Step 7 of the original
geometric argument. The item node retains the main geometric plan and records the
new existence dependency and the proved cancellation-and-resolution uniqueness step.
Change record: coord/changes/W4-finite-comparison-models.md.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
