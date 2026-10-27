## What changed

Proved `AlgebraicGeometry.ProEtale.relative_component_lift_pullback_space` without changing its
signature. The relative construction already exposes the universal property for arbitrary schemes
over the base. Applied the existing `component_mapping_property` to the affine component-site
model, then used uniqueness to obtain inverse,
coordinate-preserving comparison maps and naturality. Transported the pullback homeomorphism,
stalk isomorphisms and component homeomorphism. Verified the actual structure-map adjunct is an
isomorphism using `exists_inverseImage_stalk_iso_commRing` on germs and Mathlib's stalk criterion.

Removed the duplicate private `pullback_model_mapping_property` identified in the return.
The existing `component_mapping_property` was private in
`Sheaf.Paper.ComponentRelativeProfiniteSite`; exposed that proved helper in place, with its
statement and proof unchanged, and called it from the item. That module is unclaimed.
Two fully proved private helpers remain in the item module. No new theorem is stated.
The visibility change and all 74 downstream importers are recorded in
`coord/changes/E1-component-mapping-property-public.md`; no consumer adaptation is needed.
Updated the item's DAG proof to this shorter argument. The finite-stage characterization and limit
properties remain in the relative construction, whose theorem is still used. No unit realization
is bypassed. Read Bhatt--Scholze Lemma 2.2.8 and its more precise statement on printed p. 10,
the current unit text, and the declarations of all planned dependencies.

Compiled the complete module using `lcompile.py`. The final delivery also performs its compile
and axiom checks. Empty spaces require no exceptional choices: maps are characterized for all
schemes, and the quotient homeomorphism is proved on representatives without nonemptiness.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.relative_component_lift_pullback_space`
(node `lem-sfb-relative-component-lift-pullback-space`).

Holes closed: 1. Holes added: 0. Sorries left in the item module: none.
No split-off statements or new modules.

## No longer needed

Removed proof imports `Mathlib.Topology.Category.Profinite.Basic` and
`Sheaf.AlgebraicGeometry.StalkIsomorphismLifting`. Removed the duplicate private helper
`AlgebraicGeometry.ProEtale.pullback_model_mapping_property`; its existing counterpart
`AlgebraicGeometry.ProEtale.component_mapping_property` is now reused.
The item no longer directly uses `lem-sfb-profinite-topological-limits`: the stated universal
property of `component_relative_profinite_site` supplies the comparison directly. Removed this
node from the item's `proof_deps`. Also removed the direct dependency on
`new-lem-zl-stalk-isomorphism-lifting` and its obsolete `tool_uses` entry: the existing mapping
property already encapsulates that lifting argument. Both construction statements and the
inverse-image stalk theorem remain used.
No Lean module or public declaration is withdrawn. The profinite-limit fact may remain needed
by the proof of the relative construction itself; this delivery prunes only the redundant local
argument and dependency edge.

## Where the brief, the DAG or earlier work was wrong

The DAG's finite-stage and limit comparison is valid but redundant given the current public
mapping-property clause of `component_relative_profinite_site`. The shorter proof uses exactly
that clause, for arbitrary schemes over the base, rather than reopening its construction.
The returned duplicate was mathematically identical to `component_mapping_property`, whose
private visibility prevented direct reuse. Exposing the existing theorem repairs that API
limitation without changing its statement or proof. No mathematical statement or definition
repair was required.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
