## What changed

Proved `AlgebraicGeometry.Scheme.fppfSheaf_coproduct_partition` from the three declared
proof dependencies: small sheaf coproduct labels, labelled fppf cover descent, and
recognition of disjoint sheaf partition pullbacks. Private proved helpers establish
slice covering axioms, descent of local representatives, and coproduct existence in
the original coefficient universe. Every existing public signature and definition is
unchanged. Updated the proof node to describe the coefficient-universe argument and
the empty-index proof actually used.

The generic coproduct theorem first constructs a coproduct with larger section sets.
A section determines clopen partition data with original G_i-sections; uniqueness of
gluing makes this encoding injective. Hence its section sets are small in the original
universe. Objectwise shrinking and full faithfulness of coefficient lifting give the
required coproduct. This uses no arbitrary witness of an unproved existence theorem
to define public data: all choices occur inside theorem proofs.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.fppfSheaf_coproduct_partition`
(node `lem-trf-fppf-sheaf-coproduct-partition`). Zero holes remain in the delivered
module, and zero holes are added or split off. All private helpers are proved.

The proof uses the already stated, independently assigned theorems
`CategoryTheory.small_sheaf_coproduct_labels`,
`AlgebraicGeometry.Scheme.fppf_labelled_cover_descent`, and
`AlgebraicGeometry.Scheme.FppfPartition.disjoint_sheaf_partition_pullbacks`.
Validation: the complete module compiles through `lcompile.py` without errors or
warnings in 18.9 seconds. Empty labels and empty schemes are handled explicitly;
the value universe includes the original v=0 case without added assumptions.

Their existing holes remain outside this delivery; this is a proof from the stated
DAG dependencies, not a claim that the whole transitive axiom closure is finished.

## No longer needed

Removed unused private imports `Mathlib.CategoryTheory.Sites.LeftExact`,
`Mathlib.AlgebraicGeometry.Gluing`, `Mathlib.AlgebraicGeometry.PullbackCarrier`, and
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`. Their machinery
is encapsulated in the three declared supporting lemmas. No declared proof dependency is pruned: all three supporting lemmas and the two
site-definition nodes are used. No modules are withdrawn. The empty-index clause
uses partition existence and the empty-cover sheaf condition directly, instead of
the generic coproduct theorem's separate empty-index clause.

## Where the brief, the DAG or earlier work was wrong

The DAG's instruction to apply the generic small-site coproduct theorem directly
on the big fppf site misses a universe distinction: Scheme.{u} has object universe
u+1 whereas the theorem here permits coefficient universe max u v, including v=0.
Lifting coefficients first, proving the section sets small by clopen partitions,
and shrinking resolves this without changing any statement or assuming a global
sheafification instance. The updated node records this extra glue. The source
Stacks arguments and the unit route are preserved.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
