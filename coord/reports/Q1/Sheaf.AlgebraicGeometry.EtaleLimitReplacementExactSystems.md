## What changed

Reduced `AlgebraicGeometry.Etale.etale_limit_replacement_exact_systems` to the
strictly smaller stage construction
`AlgebraicGeometry.Etale.etale_replacement_stage_diagram`, in the new module
`Sheaf.AlgebraicGeometry.EtaleReplacementStageDiagram`.

The new theorem gives compatible injective/cokernel systems and their short exact
functor-category diagram, with stage comparison morphisms. It has no colimit
cocones, colimit arrows, or colimit exact sequence; it works over an arbitrary
cone and omits the limit, compactness, quasi-separatedness and affine-transition
hypotheses. The existing theorem's entire signature stays unchanged.

The original module now proves the rest: it constructs canonical colimit cocones,
uses the universe-restricted AB5 instance for abelian groups and Mathlib exactness
of sheaf filtered colimits, transports the resulting short exact complex to the
specified cocone L, and constructs the stage-to-colimit short-complex morphisms.
Their two squares and both prescribed component formulas are proved in Lean.

The proof-only import of the new stage-diagram module replaces the direct
injective-system and site-exactness proof imports. Public imports of the original
module stay unchanged. The new module publicly imports short-exact complexes and
the abelian functor-category interface needed by its statement, and privately
imports enough-injectives, right-adjoint preservation and site exactness. Both modules compile without warnings
through lcompile.py --all. The original theorem uses a declaration-local
unused-variable linter setting because its unchanged existential signature has
proof witnesses that do not occur in later binders. No statement or definition
was changed, and no other existing module was adapted.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.etale_limit_replacement_exact_systems`
(node `lem-weil-pbc-etale-limit-replacement-exact-systems`).

Added exactly one named hole:
`AlgebraicGeometry.Etale.etale_replacement_stage_diagram`
(node `lem-weil-pbc-etale-replacement-stage-diagram`).

This is a decomposition, not a sorry-free proof of the complete replacement
construction: one upper hole closed, one strictly smaller construction hole
added, net zero holes. The filtered-colimit and canonical-coprojection argument
is fully proved, including transport to the user-specified colimit cocone.
There are no other sorries in the delivered modules, no new definitions, and no
axioms. The helper has a source and a complete natural-language construction in
its declaration docstring.

## No longer needed

Removed direct proof imports from the original module:

- `Sheaf.Paper.ColimitSitesInjectiveSystem`: its strict site-diagram interface is
  not used. The new construction node cites enough injectives, products of
  injectives and preservation of injectives by exact-inverse-image right adjoints
  directly. Its module and node `lem-weil-pbc-colimit-of-sites-injective-system`
  are no longer needed by this proof; no removal from other target branches is
  claimed.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`: exact inverse-image work moves
  to the stage-diagram item, which retains this proof dependency.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: its interface already
  comes from the original public TopologicalInvariance import.

The original node no longer directly uses
`lem-weil-pbc-colimit-of-sites-injective-system`,
`lem-weil-pbc-inverse-image-composition`, or
`lem-weil-pbc-site-pullback-abelian-exact`; the latter two remain dependencies of
the new stage-diagram node. No whole-project removal is claimed from the
transitive target closure. The filtered-colimit Mathlib dependency remains.
The unit's own statement and realized proof steps are untouched.

## Where the brief, the DAG or earlier work was wrong

The existing compatible-injective-system theorem has strict site diagrams and
pushforward-transposed transitions, while this theorem uses inverse-image
transitions for scheme small étale sites with canonical comparison isomorphisms.
That translation, the cokernel system, and its short exact functor-category
packaging are not supplied by the stated Lean interfaces. The new stage-diagram
item isolates these tasks; no dependency was rejected merely because it uses
sorry.

LeanSearch returned Internal Server Error and was recorded as unavailable.
LeanFinder returned Mayer–Vietoris and affine-transition section results, with no
matching stage replacement construction; Loogle had no exact match. Source grep
found ShortExact.map_of_exact, which is used for the colimit portion.

The stage-diagram statement was checked on a singleton index (ordinary injective
embedding and cokernel with inverse-image transport), a zero coefficient system,
and an arbitrary cone which is not a limit. The construction only needs exact
inverse images and enough injectives, so it does not need the original geometric
limit hypotheses. The nonempty directed index assumptions are retained; no
empty-index case is silently added. No arbitrary object is defined using a
witness from the new sorry: the main proof eliminates its existential conclusion
within a theorem proof and constructs the colimit cocones using Mathlib.

Disk exhaustion temporarily interrupted an import cleanup and damaged a generated
sandbox artifact; only this item's generated build directory was cleared. Its
source helper was restored and both files recompiled cleanly.

## New nodes

`lem-weil-pbc-etale-replacement-stage-diagram` states the compatible injective and
cokernel stage systems and their pulled-back short exact diagram, before colimits.
Its source is the product/direct-image construction of Stacks 0EXZ with exact
inverse image from 04JC. It is strictly smaller than the original node because
none of the filtered-colimit sequence or its coprojection morphisms is assumed.
The new node records all actual Mathlib searches and the existing construction
and inverse-image dependencies. The blueprint search for “injective system” found
no matching imported blueprint node; its ancestor and route come from the
existing item's blueprint record. There are no change records or forced
adaptations.

The new construction node uses `lem-sp-right-adjoint-preserves-injectives` from
the Picard-framework unit as a categorical tool: exact inverse image has a right
adjoint preserving injectives. Its existing proved Lean interface is imported;
this does not replace any step of the proper-base-change unit. No tool_uses
maintainer field was written.

## Second reading by Q1

1. **Visibility and unchanged statements.** Compared both delivered modules with the
repository versions. The existing theorem signature is byte-for-byte unchanged; the
new declaration is confined to the new helper module and no existing declaration was
adapted. Verdict: pass.

2. **Proof and trust basis.** Compiled both modules with `lcompile.py --all`; they
compile without errors or warnings. The parent theorem has no `sorry`, `axiom`,
`unsafe`, `opaque`, `extern`, or `implemented_by`. The helper's single named `sorry`
is the split-off theorem listed above, with its source, construction proof, and DAG
node. The parent proof uses only the stated helper and standard categorical lemmas;
its remaining axioms are therefore within the project allowance apart from the
explicit open helper. Verdict: pass subject to the helper's documented split.

3. **Split statement review.** Checked the helper on a singleton directed index, a
zero coefficient system, and an arbitrary (non-limit) cone. Its conclusion supplies
only the stage systems, objectwise short exactness, pulled-back short exact diagram,
and component comparison maps; it makes no colimit or limit assertion. The statement
is strictly smaller than the parent target and is needed by the proof. Searches of
Lean/mathlib and the library found no duplicate declaration. Verdict: pass.

4. **Route and pruning.** The parent proof follows the unit route through compatible
stage systems, then constructs canonical filtered-colimit cocones and transports
short exactness with `ShortExact.map_of_exact`. The removed imports and proof
 dependencies are recorded in `## No longer needed`; exact inverse-image and
injective-system dependencies remain on the helper node. Verdict: pass.

5. **DAG agreement.** The parent node records the helper as its actual proof
 dependency and the helper node records its exact Lean statement, source, proof plan,
searches, unit, and split status. The unit's realized statement and route are
unchanged. Verdict: pass.

Changes made during this second reading: added this review record only; no Lean
statements or proofs were changed.
