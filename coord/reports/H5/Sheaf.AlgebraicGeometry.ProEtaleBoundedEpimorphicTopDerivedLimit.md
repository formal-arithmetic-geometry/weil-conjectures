## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.bounded_epimorphic_top_derivedLimit` with its
existing signature. Exact pro-etale products and the existing general
`CategoryTheory.derivedCategory_countableProducts_core` give preservation of the supplied
countable derived product by homology. The canonical product comparison commutes with
`1 - s`, as checked after each projection. Naturality of `homologyFunctorFactors`
transports the top-transition epimorphisms to derived homology. Applying
`AlgebraicGeometry.ProEtale.milnor_epimorphic` makes the top Roos map epic.
The long exact sequence kills the other degrees by adjacent product vanishing, and
kills degree `b + 1` by cancellation of that epic map.

Only proof imports, the proof-plan docstring, and the item's proof/DAG route change. No definitions, public imports,
or theorem signatures change. The general countable-products theorem is used as a
categorical tool from `sk-thm-properbasechange`; the item's unit has no realized proof
steps to bypass. Its new direct inputs are existing proved declarations. No new node
or new theorem is introduced. The sheafification instance exclusion is scoped to this
single theorem, following the existing Milnor proof's resolution of universe ambiguity.
The required elaboration-scope record is
`coord/changes/H5-bounded-derived-limit-instance-scope.md`; the downstream scan finds
zero current Lean consumers. The DAG parent remains attached and its statement is
unaffected.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.ProEt.bounded_epimorphic_top_derivedLimit`
(node `lem-sf-bounded-epimorphic-top-derived-limit`). Added zero holes; zero holes remain
in the delivered Lean module. This is a proof, with no split-off statements.

Validation: `lcompile.py` compiled the complete module cleanly in 5.9 seconds. Both
new direct imports pass `tools/import_direction.py may`. The original theorem signature
was compared verbatim with the sandbox signature and is unchanged; all Lean lines are
at most 100 characters.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived` and replaced
its direct dependency `det-pe-products-derived` by `det-pe-products-exact` and
`lem-weil-derived-limit-products-core`. Their existing general product-preservation
API avoids reconstructing and comparing termwise product models in this theorem.
Removed the obsolete `det-pe-products-derived` entry from the node's `tool_uses`;
the existing Milnor approval remains in its original order.
The redundant private import `Mathlib.CategoryTheory.Limits.Shapes.Products` was also
removed; the existing public imports already supply these definitions.

No module is withdrawn, and no global pruning of `ProEtaleProductsDerived` is claimed:
other consumers can still need it. All other original dependency nodes remain used.
The existing public `ProEtaleSurjectiveTowerDerivedLimit` import remains, including
its large-universe sheafification instances; its commutative-coefficient tower theorem
is not needed by this proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement or source was found. The first planned step
can be shortened using the already proved general exact-countable-products theorem.
The proof works directly with the supplied product, so no cone uniqueness or canonical
choice of a derived-limit object is required. The original commutativity and `a ≤ b`
hypotheses are retained verbatim, although this argument does not need them.
The zero tower, empty scheme, `a = b`, and a tower with arbitrary lower-degree
transitions are covered by the same argument; only the top transitions enter the
Milnor epimorphism. No arbitrary object is chosen from an unproved existence theorem.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
