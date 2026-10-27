## What changed

Filled `AlgebraicGeometry.algebraicSpace_coproduct` with the existing DAG argument.
The public statement and definitions are unchanged. Added private proof imports for
`FppfCoproductEqualityLocus`, `CoproductSchemePullback`, and Mathlib coproduct,
subcanonical-slice and sheaf-colimit infrastructure. All helpers are private and proved.

For the diagonal, partition the two test sections, pull back each summand diagonal
on the same-label intersection, take their scheme coproduct, and apply
`Scheme.fppfSheaf_coproduct_equality_locus`. For the atlas, Mathlib's
`GrothendieckTopology.isColimitCofanMkYoneda` constructs the map out of the scheme
coproduct. Component atlas pullbacks are assembled by
`Scheme.fppfSheaf_coproduct_scheme_pullback`. Étaleness follows on the coproduct
open cover, and surjectivity follows pointwise from the partition covering and
component surjectivity. Separate representability witnesses for étaleness and
surjectivity are identified through their pullback universal properties and
Yoneda's full faithfulness. All lifted-Yoneda conversions use explicit isomorphisms.

The empty-index and empty-summand cases require no nonemptiness assumptions:
covering by the partition supplies a label only after a point is given, and the
sheaf coproduct construction checks the empty-cover condition explicitly.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.algebraicSpace_coproduct`
(`lem-trf-algebraic-space-coproduct`). Proved 1 of 1 sorries in the item;
0 holes added, 0 split off, and 0 sorries left in the delivered module.
The existing dependencies `Scheme.fppfSheaf_coproduct_partition`,
`Scheme.fppfSheaf_coproduct_equality_locus`, and
`Scheme.fppfSheaf_coproduct_scheme_pullback` remain proof dependencies; this
is a proof from their existing statements, not a claim that their proofs are closed.

## No longer needed

Removed redundant direct proof imports of
`Mathlib.AlgebraicGeometry.Sites.BigZariski` and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal`; their APIs are already
available through the retained public import closure. No DAG dependencies or
modules are pruned. Both existing comparison lemmas are
used, and the unit route is unchanged. No upstream declarations are modified.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The two DAG comparison lemmas were
available but not imported in the original item. Their lifted representables
require explicit transport to the ordinary representables in `IsAlgebraicSpace`.
The prescribed source was read at Stacks `spaces.tex`,
`lemma-coproduct-algebraic-spaces` (Tag 02WQ).

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
