## What changed

Proved `CategoryTheory.siteRepresentableAlgebraicPullback` in
`Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback`, with its signature unchanged.
The arrow-map definition is unchanged. The proof uses the existing source-library
`Adjunction.uliftYonedaCompIso` and its Yoneda-evaluation lemma to identify the
adjunct. Naturality is the existing natural transformation's field. Finite-limit
compatibility follows by composing with projections and applying that naturality.
`Functor.mapGrpNatIso` supplies the group-object comparison; its two underlying
component equations are reflexive.

Replaced the broad public site-convention and inverse-image-tensor imports by
`Mathlib.CategoryTheory.Sites.Limits` and
`Mathlib.CategoryTheory.Limits.Types.Limits`, which supply the instances needed
in the unchanged statement. Updated the item's DAG proof to the implemented route.
The public-import change is recorded in
`coord/changes/site-representable-algebraic-pullback-imports.md`.
No definitions, statements, universes, or target declarations were changed.
`tools/downstream.py` and a library text search found no current Lean importers
or external users of this module. Its mathematical parent dependencies are retained;
this is a proof delivery, not withdrawal.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.siteRepresentableAlgebraicPullback`
(node `lem-pur-site-representable-algebraic-pullback`).
Holes added: zero. Holes left in this module: zero. No split-off statements.
The full theorem compiles on the project server with no warnings. `#print axioms`
for both the arrow-map definition and theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

Removed imports `Sheaf.CategoryTheory.SiteCoveringAxioms`,
`Sheaf.CategoryTheory.SiteInverseImageTensor`,
`Mathlib.CategoryTheory.Sites.CoverPreserving`, and the redundant private import
`Mathlib.CategoryTheory.Yoneda`. The existing source comparison already carries
out the adjunction/Yoneda construction, and Mathlib supplies the needed sheaf-limit
instances directly. Cover preservation is not separately used after continuity
has been supplied in the theorem's hypothesis.

Removed `lem-weil-pbc-left-exact-site-inverse-image-tensor` from this node's
`proof_deps`, proof-step uses, and obsolete `tool_uses`: the adjunction and
finite-limit-preservation hypotheses are already parameters of the unchanged
statement, so its proof does not construct an inverse-image functor. The node's
statement dependencies remain unchanged. The site-convention dependency remains
in the DAG for the sheaf definitions, but its custom covering-axiom module is not
needed by this proof. No module is withdrawn and no global pruning of these
shared dependencies is claimed. The fixed unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing DAG plan is mathematically valid, but its initial search missed the
proved source-library comparison and Mathlib's `Functor.mapGrpNatIso`. Reusing
these results avoids reproving the Yoneda isomorphism and the group-operation
calculations. The stage-2 report observed that removing the Sheaf imports lost
limit instances; the two explicit Mathlib imports above provide them without
importing the entire inverse-image tensor development.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
