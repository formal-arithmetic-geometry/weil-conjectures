## What changed

Proved `AlgebraicGeometry.ProEtale.component_lift_base_change` in
`Sheaf.Paper.ComponentLiftBaseChange`, retaining all public signatures and definitions.
Private proved helpers construct the comparison and its inverse from the relative-site
mapping property, prove naturality and identity/composition coherence, and verify the
labelled finite-open and arbitrary presentation normalizations. Added the proof-only
import `Sheaf.Paper.RelativeComponentLiftPullbackSpace`. Updated the node proof and
dependencies to the actual argument. No other Lean module changes. Scoped proof elaboration commands are documented in
`coord/changes/component-lift-base-change-proof-scope.md`; preflight conservatively
flags these commands as an interface change. The downstream check found no importing
modules, and no adaptation is required.

The final single-file lcompile.py check passes in 43.7 seconds without warnings.
The public theorem statement and all existing definition bodies were compared verbatim
against the repository, and the file has zero sorry and no line over 100 characters.
The delivery preflight performs the independent compile and axiom probe.
The construction handles empty schemes, empty indexing types, non-surjective component
base change, and repeated finite labels without any extra hypothesis. Finite-stage
normalization is proved even without using the stated surjectivity hypothesis.

Searches: msearch leanfinder for relative component lift base change found generic
profinite pullback/lifting lemmas, no comparison theorem; msearch loogle found no
`Over.pullback` result in its index; msearch grep and direct rg found the slice pullback
API and no duplicate comparison in either project root. Read all dependency signatures,
Bhatt–Scholze Lemma 2.2.8 and HRS pp. 8–9. The finite labelled-cover construction
adapts the already proved private `component_finite_comparison` argument in
ComponentRelativeProfiniteSite; that helper is private and does not expose the labels.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.ProEtale.component_lift_base_change`
(node `lem-zl-component-lift-base-change`). Added 0 holes. No sorry remains in the
item or is added elsewhere. All private helpers are proved. The existing geometric
description theorem remains a proof dependency; its existing hole is not changed.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.StalkIsomorphismLifting` and
`Mathlib.CategoryTheory.Extensive`. The direct dependency
`new-lem-zl-stalk-isomorphism-lifting` is unnecessary because the relative-site
universal property already gives exactly the unique lifts needed. The finite-coproduct
base-change node `lem-sc-etale-fibre-product-base-change-coproduct` is unnecessary:
the image formula supplies disjoint open immersions covering the Y-lift, and Mathlib's
disjoint-open-cover coproduct criterion finishes directly. Removed its obsolete
`tool_uses` entry. Neither dependency is withdrawn from the shared library.
The geometric description, relative-site theorem, fibre-product property and open
fibre-product range formula remain needed. The existing scheme coproduct-family
node records the disjoint-open-cover criterion used by the finite normalization.

## Where the brief, the DAG or earlier work was wrong

The plan is valid, but its direct stalk-lifting and finite-coproduct base-change routes
are longer than the available unique mapping property and labelled-cover arguments.
The presentation clause follows immediately from slice pullback preservation of limits
and transport along the constructed natural isomorphism, avoiding another finite-stage
presentation argument. The corrected label intersection in the original statement is
retained, and the proof explicitly covers repeated labels. No statement or definition
repair, target change, new node, or forced adaptation is required. The first preflight
required a change record for added scoped proof commands; the record above supplies it.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
