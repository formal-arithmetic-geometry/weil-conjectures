## What changed

Proved `TopCat.Sheaf.subsingleton_H'_top_of_profinite` without changing its signature.
The private helper `surjective_app_top_of_profinite` constructs local section lifts, refines
by a finite disjoint clopen cover, and glues the restricted lifts. This includes the empty
space: the finite subcover may be empty, and the sheaf axiom supplies its unique gluing.
Empty parts cause no problem because sections on the empty open form a zero group.

The private `sectionsEquiv` and its naturality lemma identify maps from the sheafification
of the free abelian representable of the top open with global sections. The private
`projective_freeSheaf_top_of_profinite` then proves this sheaf is projective by lifting
against any epimorphism. Mathlib's `Abelian.Ext.subsingleton_of_projective` closes the
original positive cohomology hole directly, in the existing `H'` Ext model.

Added proof imports of `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`,
`Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives`, and
`Mathlib.CategoryTheory.Adjunction.Whiskering`. Updated the existing proof docstring
and the node's proof, proof dependencies, and proof origin to match this shorter route.
The source read was Stacks `cohomology.tex`, `lemma-vanishing-for-profinite` (Tag 0A3F),
and `topology.tex`, `lemma-profinite-refine-open-covering` (Tag 08ZZ). The unit record
`sk-prop-sf-comparison` has no realized steps affected by this change.

The item compiled without errors or warnings through `lcompile.py`. The delivery preflight
checks all declarations for axioms and direct holes. All helpers are proved; the only
private definition is the explicit composite of three existing equivalences.

## Proved and sorry left

Closed 1 of 1 original holes:
`TopCat.Sheaf.subsingleton_H'_top_of_profinite`
(node `lem-cbc-profinite-topological-cohomology-vanishing`).
Added 0 holes. Left 0 holes. No decomposition or split-off theorem.

## No longer needed

Removed these proof imports:

- `Sheaf.Topology.PresheafModuleStalkFunctor`
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`
- `Mathlib.CategoryTheory.Abelian.Basic`
- `Mathlib.Algebra.Homology.ExactSequence`
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`

The proof no longer uses node `def-weil-pbc-module-stalk`: local surjectivity is already
available directly. It no longer uses `def-weil-pbc-exact-sequence`, `def-sp-abelian`,
or `lem-weil-pbc-right-derived-universal-delta-functor` as separate proof dependencies:
projectivity and Ext vanishing replace the short exact sequence and dimension-shifting
steps. The abelian category instance is still used through the statement's existing imports.
The retired Sheaf module shims are unnecessary as well as their source implementations.
`def-weil-pbc-sites-and-cohomology` remains a conceptual dependency for sheaf gluing, but
its attached `SiteCoveringAxioms` module declares a general precoverage interface that this
proof does not use: the open-set site and gluing API are already supplied by Mathlib.
All existing public imports are retained because they provide the statement's interface.
These removals assert only that this proof does not need these modules; other users may remain.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The existing six-step plan is mathematically
valid, but its final dimension shifting is unnecessary: `H'` is definitionally Ext from
the free abelian representing sheaf, whose projectivity is precisely the lifting property
established by the first three steps. The current blueprint's `def-pc-ext` includes positive
Ext vanishing for a projective first argument; Mathlib supplies that result without needing
enough projectives for the whole sheaf category. Enough injectives is retained to construct
`HasExt` with exactly the universe and instance used by the original signature.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
