## What changed

Replaced the proof of `CategoryTheory.colimit_site_raw_finite_matching_refinement`
without changing its signature or public imports. Added proof imports of
`Sheaf.CategoryTheory.ColimitSiteRawFiniteEqualityStabilization`, Mathlib pullback
preservation. The new module isolates finite equality detection
for raw stage representatives, without covers, pullbacks, compatibility, or gluing.

The main proof obtains raw overlap equalities by naturality, applies finite equality
detection at the pairwise pullbacks, and transports the original sections through
`θ`. Naturality of `θ` and the limit property of each preserved pullback establish
compatibility on arbitrary common test objects. A proved private helper
`CategoryTheory.raw_arrow_transport`, cocone naturality, coprojection naturality,
and `colimit.w` establish the required raw-image formula. No data definitions or
existing statements changed. Both modules compile cleanly with lcompile.py.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.colimit_site_raw_finite_matching_refinement`
(node `lem-weil-pbc-colimit-site-raw-finite-matching-refinement`). This is a
**decomposition**, not a proof independent of sorry: one upper hole is closed and
one strictly lower hole is added, so the net number of holes is unchanged.

The only sorry added or left by this delivery is
`CategoryTheory.colimit_site_raw_finite_equality_stabilization`
(node `lem-weil-pbc-colimit-site-raw-finite-equality-stabilization`). Its entire proof
is `by sorry`; its docstring states the source and the finite Kan-relation lifting
argument. There is no sorry left in the item's module, and no sorry in a definition
or private helper.

The new statement was checked on an empty finite index set (identity refinement),
on a single equation, on repeated objects/equations, and on a constant one-stage
diagram (the Kan extension along the identity reflects equality). The main proof
works for empty covers and repeated covering arrows without requiring nonemptiness
or injectivity of the indexing family. Its remaining assertion is finite equality
of two *given* sections at each object, strictly before any cover compatibility.

## No longer needed

Removed the redundant proof import `Mathlib.CategoryTheory.Whiskering` added by
the first worker; whiskering is already available through the retained imports.
No original imports were removed, and no modules are claimed pruned from the
transitive target closure. The original direct proof dependencies on
`lem-weil-pbc-filtered-colimit-categories` and
`lem-weil-pbc-filtered-colimit-sets-elementwise` move below the new finite equality
node; they remain necessary there. The old direct proof dependencies `def-weil-pbc-arrows-functor`,
`def-weil-pbc-category-colimit`, and `def-weil-pbc-sites-and-cohomology` are retained
in statement dependencies and below the equality node. All five original direct
proof dependencies are therefore no longer direct dependencies of the main proof. The main node's sole direct proof dependency is the new
finite equality node. `hcover` is unnecessary for this particular conclusion, but
is retained unchanged in the public signature and explicitly cleared in the proof.
The unused-variable linter is disabled only for this theorem to retain that binder.

The searched `ColimitSiteRawStageRestriction` is not imported: its arbitrary
comparison isomorphism does not specify the images of these representatives.
`ColimitSiteRawSectionRelations` and `ColimitSiteRawSectionCompatibility` only
handle objects transported from the initial stage, with a supplied section diagram;
they cannot directly handle the arbitrary pairwise pullback objects here.
`ColimitSiteSetSectionEventualEquality` additionally requires finite-pretopology and
limit-preservation hypotheses unavailable in this statement, and reaches the raw
sheaf theorem that depends on this matching refinement. None of these is a direct
proof dependency of this delivery.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan includes a substantial raw Kan equality-detection
argument not exposed by its fixed-set/category colimit declarations. That step is
now isolated; the overlap and transport calculations are proved in Lean.

The recorded source and unit markdown files are absent in this read-only checkout.
Read the unit's complete statement, steps, and realized list in `dag/units/sk-thm-p1.json`;
no realized unit node is bypassed. Read the source online at
https://stacks.math.columbia.edu/tag/0A35 (lemma-compute-pullback-to-limit), especially
the omitted independence verification and the first finite-cover H^0 equality.
WANTED: literature/stacks-project/sites.tex, Tag 0A35, for the new equality node.
LeanSearch returned Internal Server Error, recorded as unavailable rather than no match.

`tools/blueprint_refs.py ancestor` returns None for this item: the inherited
ancestry ends at `lem-weil-pbc-colimit-of-sites-reduced`, whose own from.node is null.
The new node accordingly records null ancestry with the precise source step and
the item path; the existing node's blueprint metadata is unchanged as required.
A whole-blueprint search for finite equality stage raw Kan returned no match.

## New nodes

`lem-weil-pbc-colimit-site-raw-finite-equality-stabilization` in
`dag/nodes/sec-proper-base-change/` is stated by
`Sheaf.CategoryTheory.ColimitSiteRawFiniteEqualityStabilization`. It detects finitely
many raw equalities after one theta transition. The main proof uses it only for
the two restrictions at each old pairwise pullback, then proves new-stage matching
and the raw-image formula itself. Three actual search kinds are recorded (LeanSearch
unavailable, LeanFinder supporting results, grep zero hits), together with direct
reads of the relevant Mathlib and project signatures. No change records are needed.

## Second reading by T1

1. **Interfaces unchanged — pass.** Compared each delivered module against the
   repository with diff. The existing matching-refinement theorem's signature is
   byte for byte unchanged; no definition or original public import changed.
   The equality module is new, with one public theorem and no data definitions.
   No change record is required.
2. **Kernel proof and holes — pass as a decomposition.** Compiled both modules
   in import order with lcompile.py. A scratch copy with `#print axioms` reports
   only propext, Classical.choice, Quot.sound, and sorryAx for the main theorem
   and the new open equality theorem. The private raw_arrow_transport helper
   uses only propext and Quot.sound. The sole textual sorry is the new named
   theorem. No forbidden declarations or hollow definitions occur. The new
   sections are explicitly theta images, and the equality witness is cocone
   naturality; no arbitrary data is chosen from an unproved existence theorem.
3. **Split statement — pass.** The equality theorem removes all covering,
   pullback, and matching data and asks only for equalities of given sections
   after one transition. It is a strict intermediate step, not a renamed matching
   theorem. Rechecked empty K (identity transition), singleton K, repeated objects
   and equations, a constant identity diagram, and parallel transition maps
   (filtered equalization). The pointwise Kan zigzag lifting argument applies to
   arbitrary stage objects and uses no missing topology assumption. Expanded its
   docstring and matching node proof to specify the intermediate outer equality,
   the Kan triples and relations, endpoint identity arrows, and common transition.
   Independent LeanFinder, Loogle, msearch grep, and rg searches found only fixed
   set-diagram equality criteria, notably isColimit_eq_iff' and
   ιColimitType_eq_iff_of_isFiltered'. Read RawSectionRelations and the more general
   ColimitStageKanCocone: the former only evaluates objects from the initial stage;
   the latter additionally requires a constructed section diagram and its cocone.
   Neither directly closes this varying-object equality statement in a few minutes.
4. **Top-down reduction and pruning — pass.** Read the proof from its conclusion
   backward: naturality and colimit.w give the precise raw-image transport;
   preserved pullbacks give compatibility on arbitrary common test objects;
   the new equality theorem is used only on the I × I old overlap equations.
   Removed the redundant Whiskering proof import and recompiled successfully.
   All five old proof dependencies are accounted for above. The unit record
   sk-thm-p1.json is unchanged; none of its realized nodes is bypassed. The raw
   argument stays below the unit route.
5. **Lean and DAG agreement — pass.** The existing node's three proof steps follow
   the overlap, pullback, and raw-image calculations in Lean, and its sole direct
   proof dependency is the new equality node. The new node records its full Lean
   signature verbatim, source, proof, dependencies, origin, three search kinds,
   creation data, blueprint ancestry, chapter and unit. Verified the cited Stacks
   Tag 0A35 online: the new argument expands its omitted presentation independence
   verification and the finite-cover equalizer calculation.

Second reading changed the redundant proof import, the new module's author credit,
and the completeness of the new theorem's docstring and node proof. Updated the
report's dependency accounting. No theorem signature or proof term changed. One
original hole is closed and one lower hole is added: net zero, no module pruned.
