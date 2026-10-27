## What changed

Extracted the explicit tuple and coset-chain constructions, byte for byte, into
`Sheaf.AlgebraicTopology.OrderedJoinCosetChains`, with a public reexport from the
assigned module. Every original public import and declaration signature stays.
This breaks the import cycle needed to state the two genuine remaining steps in
separate modules.

The assigned theorem combines the recursive chain-map and coordinate-formula properties and the
erasure-boundary lemma with direct proofs of equivariance of the recursive comparison in every arity, erasure equivariance, both
augmentations, all three corresponding properties of the composite, and top
support. The support proof establishes the stronger fact that erasing *any*
top-degree colored chain lands in the stated span, independently of the
comparison construction. It shows the color set is all of Fin(n+1), chooses
coset witnesses for the already specified vertices, and identifies the erased
list with the corresponding ofFn generator. No object is chosen from an
unproved existence theorem.

The direct equivariance proof also establishes naturality of tuple deletion for
arbitrary maps of sets. These proved private helpers add no public interface.

The item has no current Lean importers; the parent DAG attachments are retained.
Interface extraction is documented in
`coord/changes/ordered-join-coset-chains-extraction.md`.

Validation: all four delivered modules compiled individually through `lcompile.py --all`;
the assigned module took 5.5 seconds, with no errors or warnings. The delivery
preflight checks the final files again, including declaration axioms.

## Proved and sorry left

Original hole closed:
`AlgebraicTopology.OrderedJoin.CosetComparison.orderedJoinCosetComparison`
(`lem-sfb-ordered-join-coset-comparison`). Its unchanged statement now has a complete
Lean proof from two smaller statements. This is a decomposition, not a complete
proof of all its dependencies: one original hole closed, two holes added, net
minus one hole closed. There is no sorry left in the assigned module and none
in the extracted definitions.

New holes:

- `AlgebraicTopology.OrderedJoin.CosetComparison.cosetComparisonRecursion`
  (`lem-sfb-ordered-join-coset-recursion`), in
  `Sheaf.AlgebraicTopology.OrderedJoinCosetRecursion`: recursive comparison
  chain-map identities and the fixed finite coordinate expansion. This contains no
  erasure, composite map or top-support conclusion.
- `AlgebraicTopology.OrderedJoin.CosetComparison.cosetErasureBoundary`
  (`lem-sfb-ordered-join-coset-erasure-boundary`), in
  `Sheaf.AlgebraicTopology.OrderedJoinCosetErasureBoundary`: the single identity
  that erasure commutes with boundary, independent of the comparison recursion.

Both have their own source, complete proof in words and DAG node. They are strict
parts of the original argument, not aliases or repackaged hypotheses. The
combining proof performs the actual composition and augmented-index reasoning.

## No longer needed

None. The original partial-contraction and subgroup public imports are retained.
Removed the unused private PartialContraction import from the new recursive
statement module: its statement uses only the explicit data; its future proof
dependency remains recorded in its node.
The free-module and partial-contraction nodes remain needed through the explicit
constructions and the recursive comparison lemma. No module is withdrawn and no
parent route is bypassed. The new data module imports only the ordered-join
construction module, since its definitions use no contraction theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The stated dependencies provide the contraction
identities and formal expansion but do not themselves state the recursion or
the erasure positional-deletion calculation. These two steps are separated so
other workers can prove them independently.

Checked edge cases in the new statements: the empty face has empty boundary,
singletons erase to singleton lists whose augmentation is the empty tuple,
and degrees below -1 have no symbols. For n=1 the recursive comparison sends
[h0,h1] to -[(0,h1*a0),(1,h0*a1)]+[(0,h0*a0),(1,h0*a1)]; its boundary is
[(0,h1*a0)]-[(0,h0*a0)]. Repeated h values, coincident cosets, the trivial
subgroup, and arbitrary ambient group characteristic impose no extra condition.
The node and docs retain the fact that this arithmetic expansion is agent
written; the cited blueprint paragraph itself does not assert these formulas.

## New nodes

`def-sfb-ordered-join-coset-chains` records the verbatim extracted constructions.
`lem-sfb-ordered-join-coset-recursion` records the recursive comparison step.
`lem-sfb-ordered-join-coset-erasure-boundary` records the positional-deletion
compatibility of erasure. All inherit the item's chapter and unit. The original
node now records the actual assembly and direct top-support proof.

Change record: `coord/changes/ordered-join-coset-chains-extraction.md`.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
