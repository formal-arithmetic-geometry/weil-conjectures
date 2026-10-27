## What changed

Replaced the remaining proof of
`WeilConjectures.PurStrictScalar.ordinaryBalancing_existsUnique` by a complete
assembly of one-level scalar-balancing isomorphisms. Two new proof-only imports
state the separate level construction and source-generator criterion. Private
proof imports expose the existing completed tensor scalar-multiplication lemma
and its reduction wrapper. No existing
statement, public definition or public import changes. The previously proved
`reductionBalancing_existsUnique` and its two universal-counit imports are retained.

The new private helpers prove tensor-section naturality from the normalized scalar
adjunction, reduction-unit naturality from the adjunction unit and limMap_π,
and horizontal unit compatibility from limit.w. Generator extensionality then
proves horizontal commutativity and naturality in M. Two applications of
NatIso.ofComponents assemble the level isomorphisms into a natural tower
isomorphism. Generator extensionality also proves its uniqueness. Witnesses from
the single-level existence theorem are used only inside a theorem proof; no
public data is selected from an undetermined existence statement.

## Proved and sorry left

Original holes: 1. Closed in the item:
`WeilConjectures.PurStrictScalar.ordinaryBalancing_existsUnique`.
The item has zero remaining sorry bodies. This is a decomposition, not a net
proof: two strictly simpler holes are added.

- `WeilConjectures.PurStrictScalar.ordinaryScalarBalancingLevel_exists`, in
  `Sheaf.Paper.OrdinaryScalarBalancingLevel`, node
  `lem-pur-ordinary-scalar-balancing-level`. This only asserts a single object/level
  isomorphism with its tensor formula, without horizontal or module naturality
  and without uniqueness.
- `WeilConjectures.PurStrictScalar.ordinaryScalarReduction_hom_ext`, in
  `Sheaf.Paper.OrdinaryScalarReductionGenerators`, node
  `lem-pur-ordinary-scalar-reduction-generators`. This is an independent generator
  criterion into an arbitrary module, with no ramification or F-reduction comparison.

No other holes are added, and the already proved derived-balancing theorem is preserved.
The two new statements are tested mathematically at n=0 (positive exponent 1),
e=1, the zero module and empty site object. They assert local generation, not
surjectivity of the quotient-unit map on global sections.

## No longer needed

None. No original import, dependency node or module is pruned. The source and
target derived counit universality nodes and the generic right Kan uniqueness
node are still used by the retained derived proof. The new lemmas import only
the existing native-support model, avoiding an import cycle through the item.

## Where the brief, the DAG or earlier work was wrong

The prior node recorded the ordinary theorem as a retained original hole rather
than decomposing its argument. The new node proof records the single-level
algebra and generator criterion separately, and the actual Lean assembly of
transitions, naturality and uniqueness. The unit route is unchanged.

A read-only traversal also found an existing, unrelated DAG cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`. No files in that branch are
changed. A separate reachability check confirms that none of the four prerequisite
nodes used by the new lemmas has a path back to this item, so the added edges do
not introduce a cycle.

## New nodes

`lem-pur-ordinary-scalar-balancing-level` records the quotient/tensor reassociation
at one module and one retained quotient, normalized by the specified adjunction
unit. Its source is the original ordinary balancing docstring, Stacks 03EK/0940
and the finite-free completed coefficient comparison. Its own module contains
one named public theorem with a complete proof in words and one sorry body.

`lem-pur-ordinary-scalar-reduction-generators` records the independent local
source-generator criterion at one level, into any B-module. Its source is the
local pure-tensor generation step of the same docstring and the sheafified tensor
adjunction in Stacks 03EK. Its own module contains one named public theorem with
a complete proof in words and one sorry body. No change record is required:
existing statements and definitions are unchanged.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
