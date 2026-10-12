## What changed

Proved `CategoryTheory.colimit_site_stage_image_refinement` in
`Sheaf.CategoryTheory.ColimitSiteStageImageRefinement`, preserving its signature
and existing docstrings. Added the proof-only import
`Mathlib.CategoryTheory.Limits.Types.Filtered`. Four private helpers are proved.
The arrow lift uses joint surjectivity of the given arrow colimit and eventual
object equality. The sheaf comparison transposes the later unit, uses adjunction
injectivity, and applies naturality to restrict the resulting section.
The item's node proof and dependencies describe this route.

Repaired both duplicate statements identified in the return:

1. Removed `sheaf_unit_unique`; the single call now uses Mathlib's
   adjunction `homEquiv` injectivity, natural-transformation extensionality,
   and `Arrow.mk_inj` directly. The existing helper in
   `ColimitSiteSetSectionCoherence` is private, so cannot be imported by name.
2. Generalized the private `arrow_mk_heq_apply` in place: its two arrows may
   now have different source types as well as different target types, and
   it accepts heterogeneously equal input elements. Its proof uses
   `Arrow.mk_eq_mk_iff` and equality elimination; the call supplies `HEq.rfl`.
   The helper in `ColimitSiteSetSectionRepresentatives` is private and its
   module imports this item, preventing reverse import. The generalized
   statement is strictly stronger, and is no longer the duplicate flagged
   by the landing check. Equal source types and repeated inputs recover the
   earlier use; equality elimination also handles empty types without any
   inhabitedness assumption.

No other module, public signature, visibility, or definition changes.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.colimit_site_stage_image_refinement`
(node `lem-weil-pbc-colimit-site-stage-image-refinement`). No holes added or left.
All four private helpers are proved. This is a proof, not a decomposition.
The repaired module compiles cleanly through `lcompile.py`.

## No longer needed

The planned dependency `lem-weil-pbc-filtered-colimit-categories`, module
`Sheaf.CategoryTheory.FilteredColimitCategories`, is not used by this proof.
Its category construction, general finite-diagram descent, and isomorphism
clauses are unnecessary: arrow surjectivity and eventual object equality suffice.
This is local pruning of this item's proof route, not a claim that other targets
cease to need that module.

No original imports were removed. Both original public imports supply the
existing interface. No Sheaf proof imports were added. The duplicate private
`sheaf_unit_unique` declaration is removed; `arrow_mk_heq_apply` is generalized.
The blueprint unit's realized declarations and route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original delivery duplicated two private library helpers. The repair removes
one and generalizes the other, as permitted by the return, without importing
private declarations or introducing an import cycle.

The planned category-colimit theorem constructs a chosen category on
`colimit (F ⋙ Cat.objects)`; it does not directly supply arrow lifting for the
arbitrary cocone V. The direct set-colimit argument avoids that interface gap.

The earlier second reading predates this repair and must be renewed by the
second reader; it is not reproduced as validation of the changed proof.

## Second reading by U3

1. Compared the delivered module with the repository version. The public theorem signature and all existing declarations are unchanged; only the proof body, private helpers, and a proof-only Mathlib import differ. Verdict: pass.
2. Compiled the module and all sandbox modules with `lcompile.py`; there are no errors, warnings, `sorry`, forbidden declarations, or hollow definitions. A scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Read the proof and checked the helper statements. The arrow lifting helper uses joint surjectivity and filtered-colimit equality twice; the triangle helper is a strict intermediate uniqueness construction; the heterogeneous arrow application helper is stronger than its use and true by `Arrow.mk_eq_mk_iff`; the restriction helper is direct equality elimination. No duplicate public or private statement remains. Verdict: pass.
4. Checked the proof route against the node and unit. The target is proved directly from the stated cocone, object and arrow colimit hypotheses, and the sheaf adjunction; the removed filtered-colimit-categories dependency is genuinely unused. The unit `sk-thm-p1` and its realized route are unchanged. Verdict: pass.
5. Checked DAG agreement and pruning. The node proof, dependencies, and origin describe the actual three proof stages, and the omitted category-colimit theorem is listed under pruning. No new node or split-off sorry was added. Verdict: pass.

Changed after second reading: no Lean declarations or node statements; added this review record only.
