## What changed

Replaced the whole-proof hole in
`Sheaf.CategoryTheory.ColimitSiteAbelianStageImageSheaf` with a complete Lean proof
from `CategoryTheory.colimit_site_abelian_stage_matching_lift` in the new module
`Sheaf.CategoryTheory.ColimitSiteAbelianStageMatchingLift`. The new import is proof-only.
Every existing signature, visibility, definition, and public import is preserved.
The copied DAG node now records the actual three-step proof.

The argument includes the generated presheaf in the ambient inverse-image sheaf,
glues there, lifts the original matching family to a stage cover, and glues in the
stage inverse-image sheaf. Naturality and separatedness of continuous restriction
identify the stage amalgamation with the ambient amalgamation. Restriction along
the inverse presentation equality proves that the ambient amalgamation is a
generator. Subtype extensionality supplies the amalgamation and uniqueness in
the generated presheaf. No data construction uses an unproved existence theorem.

The new residual statement asks only for a compatible family on a stage cover,
with specified local comparison formulas. It asserts neither an amalgamation nor
uniqueness, and supplies the stage cover used by the actual stage gluing in the
main proof. Its natural-language proof uses finite source-unit zero detection to
stabilize the finitely many overlap differences. This avoids rebuilding the whole
presentation presheaf inside that residual statement.

Both modules compile with lcompile.py, individually and in dependency order.
The main proof also compiled after removing its redundant proof-only Whiskering
import. The new matching-lift dependency branch does not return to the assigned node.
A raw traversal of all existing statement/proof dependencies encountered an existing
horseshoe-delta/derived-long-exact cycle; this delivery does not change either node.

## Proved and sorry left

Closed: `CategoryTheory.colimit_site_abelian_stage_image_isSheaf`
(node `lem-weil-pbc-colimit-site-abelian-stage-image-sheaf`). No direct hole remains
in the assigned module.

Added and left: `CategoryTheory.colimit_site_abelian_stage_matching_lift`
(node `lem-weil-pbc-colimit-site-abelian-stage-matching-lift`), whose entire proof
is `:= by sorry` in its own new module, with source and proof in its docstring.

This is a decomposition: one upper hole closed, one strictly intermediate hole
added, net zero holes. The upper theorem depends on the residual theorem; it is
not yet a theorem with only the three permitted axioms.

## No longer needed

No original import is removed: all three public imports supply declarations used
by the unchanged signature. The proof-only Mathlib.CategoryTheory.Whiskering
import tried during development was redundant and removed.

The assigned node no longer directly depends on
`lem-weil-pbc-filtered-colimits-commute-finite-limits`,
`lem-weil-pbc-filtered-colimit-sets-elementwise`, or the continuous adjunction node:
its proof uses the matching-lift statement and existing sheaf conditions instead.
The matching-lift node uses object/arrow representatives, adjunctions, and the
existing `lem-weil-pbc-colimit-site-finite-unit-zero-detection` statement. The latter
still has a finite-limit/filtered-colimit proof dependency. Therefore no globally
unreachable module or net module pruning is claimed. The raw presentation
presheaf and its adjunction identification are not constructed by this delivery.
All unit-realizing nodes and unit steps remain in place.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. A full raw DAG traversal exposed the pre-existing
cycle `lem-weil-pbc-horseshoe-delta-functor` to
`lem-weil-pbc-derived-functor-long-exact` and back, reached via the broad
`def-weil-pbc-sites-and-cohomology` record. These existing nodes are outside this
delivery; no existing edge in that cycle was added or changed here. The existing stage-image refinement theorem only
handles sections over a forward image of an object from the original stage i.
A cover of an arbitrary limit object need not have this form. Applying that
statement directly to every member of an arbitrary cover would be invalid.
The new matching-lift statement explicitly presents the target at a stage above
i and allows arbitrary objects of that stage.

Compatibility of ambient images does not imply compatibility of arbitrary chosen
stage representatives: alpha need not be injective at one stage. The residual
proof uses source-unit zero detection on overlap differences, then a common
refinement, rather than making that inference. The source was checked at
[Stacks Tag 0A35](https://stacks.math.columbia.edu/tag/0A35) and
[Tag 03CO](https://stacks.math.columbia.edu/tag/03CO).

Edge cases checked in the argument: an empty stage cover has an empty matching
family and the stage and restricted ambient sheaves supply their empty-cover
conditions; the separatedness comparison still holds. A zero sheaf yields the
zero matching family. An empty category of limit objects has no Y to consider;
filteredness and the supplied i exclude an empty indexing category. Target-object
presentation equality is retained explicitly, with inverse transports cancelled
by presheaf functoriality. No cover or stage map is assumed injective.

## New nodes

`lem-weil-pbc-colimit-site-abelian-stage-matching-lift`, at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-colimit-site-abelian-stage-matching-lift.json`,
states existence of a compatible stage-cover lift of a matching family of
generated sections. It has a new module of its own and a two-step source-based
proof: finite cover and local representative lifting; stabilization of the finite
overlap equations using existing source-unit zero detection. The proposition is
not a renamed sheaf condition. Stage amalgamation, the separatedness comparison,
subgroup membership of the resulting global section, and uniqueness are proved
in the assigned module.

LeanSearch was unavailable with Internal Server Error. LeanFinder returned generic
compatible-family and subfunctor lemmas, but no stage-cover lift. The Mathlib grep
query had no hits. Searches of both project roots and the DAG found the existing
refinement, source-unit zero-detection and set/etale matching statements; none has
the general abelian matching-lift signature here. Blueprint search for matching
families returned no unit match, and the recorded nearest ancestor is null,
matching the assigned node's ancestry. No interface changes or change records.

## Second reading by J3

1. **Statements and accidental changes.** Compared the delivered image-sheaf module with the repository version. The target theorem signature, all existing declarations, definitions, visibility, and public imports are byte-for-byte unchanged; only its proof and one proof-only import were added. The new matching-lift declaration is a separately named intermediate statement with a matching DAG node.

2. **Proof checks.** Compiled both delivered modules with `lcompile.py --all`. The image-sheaf target has no remaining `sorry`; the only residual `sorry` is the named matching-lift theorem, documented and represented by its split node. No forbidden declarations or hollow definitions occur. The target proof uses only the permitted existing sheaf and category constructions; the residual theorem is explicitly marked as the open proof obligation.

3. **Truth and strength of the new statement.** Checked the matching-lift statement against its use: it asserts only existence of a stage cover and compatible stage family with the required local comparison equations, and does not assert amalgamation or uniqueness. Its hypotheses and conclusion are strictly weaker than the target and sufficient for the subsequent stage gluing. The empty-cover and zero-section cases are covered by the stated sheaf conditions.

4. **Pruning and dependency agreement.** Compared the revised node proof and `proof_deps` with the Lean proof. The target now depends on the matching-lift node and the existing image, sites, and underlying-sheaf declarations; removed old dependencies are no longer referenced by the proof. The proof-only matching-lift import is non-public. No unit-realized node or unit step was bypassed.

5. **Source and search review.** Read the matching-lift docstring and DAG source/proof, checked the cited Stacks paragraphs, and searched the local Lean and Mathlib trees for an existing declaration. No duplicate theorem was found. The source-unit zero-detection route in the new node is the documented stabilization argument, while stage amalgamation and uniqueness remain in the target proof.

Changed during second reading: added this review section only; no Lean declarations, statements, definitions, imports, or DAG records were altered.
