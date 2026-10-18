## What changed

Proved `CategoryTheory.NatTrans.isoLocus_localizing` in
`Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus`, without changing its
signature, docstring, definitions or public imports.

The existing instances in
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators` supply the
triangulated and retract assertions. Their proofs realize the node's zero,
shift, triangle and retract steps; the triangulated instance uses the stated
`lem-sf-triangle-two-out-of-three` declaration
`CategoryTheory.NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃`.

For every indexing type and every colimit presentation in the isomorphism
locus, `NatIso.isIso_of_isIso_app` turns the component assumptions into an
isomorphism of diagrams. Mathlib's
`CategoryTheory.Limits.isIso_app_coconePt_of_preservesColimit` then proves
invertibility at its vertex. This is exactly the universal-property argument
in step 4, already implemented in Mathlib, and includes arbitrary cocones
and the empty family. Finally `sInf_le` applied to the locus itself proves
the minimality assertion. No new mathematical route or dependency is needed,
so the existing six-step node proof and its dependency list stay unchanged.

Read the current blueprint statement and proof at
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-lem-sf-determination/det-sf-determination-localizing{,.proof}.md`,
the item's node, the dependency nodes and the implementing Lean sources.
The unit record has no realized-node route that this proof bypasses.

Validation: the complete module compiles through `lcompile.py` with no
warnings or errors. No new assumptions or category restrictions were added.

## Proved and sorry left

Closed 1 of 1 holes:
`CategoryTheory.NatTrans.isoLocus_localizing`
(node `det-sf-determination-localizing`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered
module. All invoked library and Mathlib results are already proved.

## No longer needed

None. No imports, dependency nodes or modules were removed. The original
imports provide the isomorphism-locus API, colimit-closure notion,
colimit-preservation hypotheses and colimit infrastructure used here.
All four declared node dependencies remain used, directly or through the
already proved triangulated-locus instance. No generating-class lemma or
constructible-complex specialization is introduced as a dependency.

## Where the brief, the DAG or earlier work was wrong

No mathematical corrections were needed. The blueprint's proof is already
largely implemented by the upstream isomorphism-locus instances and the
generic Mathlib preserved-colimit lemma; those implementations avoid
repeating their inverse constructions in this module.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
