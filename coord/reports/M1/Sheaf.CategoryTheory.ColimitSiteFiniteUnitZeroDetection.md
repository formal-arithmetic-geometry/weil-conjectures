## What changed

Replaced the proof of `CategoryTheory.colimit_site_finite_unit_zero_detection` without changing
its signature. The second reading changes the existing `Comma.Over.Basic` import
to proof-only visibility, because only the proof uses `Under`. Added proof-only imports of
`Sheaf.CategoryTheory.ColimitSiteFiniteSectionColimitPresentation`,
`Mathlib.CategoryTheory.Filtered.Final`, and
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered`.

The proof obtains a section-colimit presentation, uses the identity object of `Under j`,
and turns the assumed unit vanishing into equality of two coprojections by injectivity of the
limit section-group isomorphism. Mathlib's `IsColimit.eq_iff'` supplies a single refinement.
Naturality of the source-unit transformation and additivity then prove vanishing of the
later-stage unit. The Lean proof performs this extraction completely.

The new structural theorem groups the original plan's presentation construction, finite-cover
sheaf argument, adjunction identification, and finality of carried-forward presentations.
It asserts a colimit cocone of stage section groups and two equations of additive maps for
all source sections; it has neither a vanishing hypothesis nor an eventual-vanishing conclusion.
Its docstring and node give the construction and proof in words. No object or definition is
chosen from its existential assertion: its witnesses are eliminated only inside the proof.

The structural module also imports its stated construction dependency
`ColimitSiteAbelianSectionDiagram` and the Mathlib mates, filteredness and finite-limit
commutation modules as proof-only dependencies, matching its documented proof plan.

Both modules were recompiled in import order with lcompile.py on this repair, with exit code 0
and no compiler warnings. The prescribed deliver3.py dry run passes preflight and compilation;
nothing was pushed. Repaired reviewer X-1e6db point 2 by replacing the change record's Users
prose with the requested direct-importer table. The importer independently publicly imports
`Mathlib.CategoryTheory.Comma.Over.Basic` and requires no adaptation.
The unit record `sk-thm-p1` is unchanged: this item and its new structural dependency lie below
the unit's realized statements and steps.

## Proved and sorry left

Closed the original hole in `CategoryTheory.colimit_site_finite_unit_zero_detection`
(node `lem-weil-pbc-colimit-site-finite-unit-zero-detection`). No sorry remains in the item's
module.

Added one hole: `CategoryTheory.colimit_site_finite_section_colimit_presentation`
(node `lem-weil-pbc-colimit-site-finite-section-colimit-presentation`), in the new module
`Sheaf.CategoryTheory.ColimitSiteFiniteSectionColimitPresentation`.

This is a decomposition: one hole closed and one structural hole added, not a net reduction
in the number of holes and not an axiom-free completion of the import closure.

Edge cases checked against the construction: for a one-object identity diagram the group
colimit and both section-group isomorphisms are the identity presentation; a zero source sheaf
has zero stage section groups; an empty source category admits no X; an empty covering family
uses the zero group through the empty finite matching-family limit. `Under j` is inhabited by
its identity object even though no choice of another stage was assumed.

## No longer needed

None of the original imports or dependency modules is pruned from the transitive proof route.
The old direct proof dependencies no longer directly used by the parent are:
`def-weil-pbc-arrows-functor`, `def-weil-pbc-category-colimit`,
`def-weil-pbc-finite-precoverage`, `def-weil-pbc-sites-and-cohomology`,
`lem-weil-pbc-conjugate-iso-unit-equation`, and
`lem-weil-pbc-filtered-colimits-commute-finite-limits`. They remain statement or structural
proof dependencies; none is removed from the transitive route. The parent directly uses
only the structural node and the Mathlib filteredness and equality criteria. The new node also records the existing proved abelian section-diagram
construction as a dependency for its canonical diagram step.

Discarded the uncommitted earlier `ColimitSiteFiniteUnitZeroDetectionData` module and its
node copy. They were never part of the library and are not counted as pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier source-root discovery blocker is resolved: the prescribed dry run now passes.
The returned change record omitted the direct importer from its Users table; reviewer
X-1e6db point 2 is repaired with the exact requested row for
`Sheaf.CategoryTheory.ColimitSiteAbelianSectionEventualEquality` (unclaimed).
The saved second-reading sections are retained unchanged.

The previous sandbox did not match its report: its helper theorem restated the entire
zero-detection assertion with an extra `True`, and the main proof merely projected that
conjunction. Its node described different data, had a circular dependency on the item,
and lacked the required searches and matching signature. That reduction was removed.

The existing `ColimitSiteAbelianSectionUniversality` has a compatible section-colimit
conclusion, but import_direction.py reports that it already reaches this item. Importing it
here would close a cycle through eventual section equality and source-unit zero detection.
`ColimitSiteAbelianSectionDiagram` has no such cycle and proves diagram coherence, but does
not assert that its cocone is colimiting. `ColimitSiteStageSectionDiagram` is set-valued and
has no colimit conclusion. `ColimitSiteStageImageSheaf` requires an additional finite-limit
preservation instance for set inverse images. These interfaces therefore do not independently
supply the needed finite-site section formula.

The Stacks text was read at https://stacks.math.columbia.edu/tag/0A35 and
https://stacks.math.columbia.edu/tag/03CO because the named local literature files are absent
on this machine. The new lemma retains the parent's finite-precoverage hypotheses and follows
the section-formula argument, stopping before equality detection. LeanSearch returned an
Internal Server Error; LeanFinder, Loogle, and local Mathlib/library searches were also made
and their results are recorded in the new node.

## New nodes

`lem-weil-pbc-colimit-site-finite-section-colimit-presentation`:
`lean/Sheaf/CategoryTheory/ColimitSiteFiniteSectionColimitPresentation.lean`, declaration
`CategoryTheory.colimit_site_finite_section_colimit_presentation`. Its conclusion is the
unit-compatible section colimit and stage group identifications, before the final
filtered-colimit equality extraction. It inherits the parent chapter, unit, and blueprint
ancestry. Its dependencies do not include the parent or any of its downstream users.
No statement, definition, or target changes. The public import demotion in the parent is
documented in `coord/changes/demote-comma-over-basic-import.md`; no forced adaptation is needed.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered parent module with the repository version. The theorem signature is unchanged byte for byte; only proof and import visibility changed. The added structural module and node are new and are documented. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; both compile without warnings. The parent has no `sorry`; the structural theorem has exactly its named `sorry`. No prohibited declarations or hollow definitions occur. Verdict: pass.
3. Checked the parent theorem and structural theorem against the stated DAG nodes and the Stacks sources. The structural statement is strictly weaker than the detection target and supplies the section-colimit construction required by the proof; edge cases (identity diagram, zero sheaf, empty covers) are covered in the report. Verdict: pass.
4. Read the proof from the target downward. It uses the structural presentation, filteredness of `Under j`, and Mathlib's concrete filtered-colimit equality criterion. The unit route `sk-thm-p1` remains intact; no reachable import was pruned. Verdict: pass.
5. Compared node statements and dependencies with the Lean declarations. The new node records its source, proof steps, searches, origin, metadata, chapter and unit; dependencies match the proof. Verdict: pass.

Changed during second reading: added this required review section and retained the proof-only import demotion and structural split documented above.

## Earlier second reading (a previous round; superseded)

1. Compared each delivered module with the repository. The only existing module changes
   are its proof and imports; its theorem signature and docstrings are byte for byte
   unchanged. The other module and node are new. No definition, target, statement,
   or other claimed module changes. Verdict: pass.
2. Compiled both modules locally in import order. The parent contains no sorry; the
   helper has exactly its one named theorem ending in `by sorry`. No prohibited
   declaration or hollow definition occurs. Explicit scratch `#print axioms` checks
   give only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the helper is
   still open. Its existential witnesses are eliminated inside a Prop proof and
   supply no definition or arbitrary chosen data. Verdict: pass as decomposition.
3. Read the full new signature and its construction proof against Stacks
   [0A35](https://stacks.math.columbia.edu/tag/0A35) and
   [03CO](https://stacks.math.columbia.edu/tag/03CO). Checked the identity diagram,
   zero sheaf, empty source and empty cover cases. This is the section formula
   before equality extraction: it has no vanishing hypothesis or eventual-vanishing
   conclusion, and simultaneously compares additive maps on every source section.
   It is a structural part of the original argument, not a renamed detection lemma.
   Independent LeanFinder, Loogle and grep searches, using different queries, found
   no applicable independent replacement; the existing universality theorem reaches
   this item through eventual equality. Verdict: pass; the construction remains open
   and cannot be closed by a short local proof.
4. Read the proof from its conclusion back to its assumptions. Mathlib's concrete
   filtered-colimit criterion handles all equality extraction; naturality and the
   two unit equations supply exactly the required later-stage unit. The public
   group-limit, colimit and filtered-colimit imports supply the instances needed
   to elaborate the canonical sheaf adjunctions, so they belong to the signatures.
   Demoted the parent's `Comma.Over.Basic` import, used only by the proof. Added
   proof-only imports for the helper's documented dependencies. Listed all six old
   direct dependencies transferred to the structural node. No module is pruned from
   the transitive route. Checked `sk-thm-p1.realized`; none of its statement or step
   nodes is bypassed. Verdict: pass after import/report repairs.
5. Compared both node `lean.statement` fields with the actual signatures; they
   match verbatim. Each `proof_deps` is exactly the union of the steps' `uses`.
   The new node has source, complete proof steps, searches, origin, split status,
   created metadata, blueprint ancestry, chapter, unit and Lean record. Clarified
   the parent plan's actual Mathlib instance and equality criterion. Verdict: pass.

Changed only import visibility/dependency imports, dependency reporting, search records,
and the parent proof-plan explanation. The reviewed Lean proof itself needed no repair.
This delivery closes one original hole and adds one structural hole: net zero, with no
claim that the target import closure is axiom-free.

## Second reading by M1

1. Compared the full parent diff with the repository and programmatically compared
   its signature byte for byte. Only its proof and documented import visibility
   change; the second module is new. The existing node changes only proof,
   proof_deps and proof_origin. Verdict: pass; no target or definition changed.
2. Independently compiled both modules with lcompile.py --all. Fresh scratch copies
   with #print axioms report exactly propext, Classical.choice, Quot.sound and
   sorryAx for both declarations. The sole direct sorry is the named structural
   theorem, with its source, proof docstring and node. There are no prohibited
   declarations or definitions choosing arbitrary existential witnesses. Also
   compiled the unchanged direct importer ColimitSiteAbelianSectionEventualEquality
   against the reviewed modules; the public import demotion requires no adaptation.
   Verdict: pass as a decomposition, not an axiom-free proof of the import closure.
3. Read the structural statement and all its unit equations against Stacks
   [0A35](https://stacks.math.columbia.edu/tag/0A35) and
   [03CO](https://stacks.math.columbia.edu/tag/03CO). Checked the identity diagram,
   zero sheaf, empty source and empty cover cases: identity inverse image is
   canonically isomorphic to the source, and an empty cover forces zero sections.
   The missing result constructs the section-colimit presentation independently
   of vanishing; the parent genuinely performs equality extraction and naturality.
   Fresh LeanFinder, Loogle and grep searches with different wording found no
   independent replacement. SectionUniversality imports EventualEquality, which
   imports this item; other set/scalar formulas require extra hypotheses.
   The construction is a proper structural part of the original argument and
   cannot be closed in a few minutes from the available interfaces. Verdict: pass.
4. Read the target proof backward: the stage unit equation reduces the conclusion
   to naturality of e, Mathlib eq_iff' supplies the refinement, and the limit unit
   equation plus injectivity of beta supplies coprojection equality. Checked all
   imports against signature instances and the documented structural dependencies.
   Checked sk-thm-p1.realized: this change bypasses no realized unit statement or
   step. All six old direct dependencies transferred to the helper are listed;
   none of the transitive modules is pruned. Verdict: pass.
5. Compared both node lean.statement fields with the actual signatures, and checked
   that proof_deps is the union of proof-step uses. Read the sources, searches,
   origin, split status, created record, blueprint ancestry, chapter and unit of
   the new node. The parent plan matches the proof's Mathlib filteredness and
   equality criterion. Verdict: pass.

Changed in this reading: appended this independent review and fresh search records.
No Lean proof repair was necessary. One original hole is closed and one structural
hole is added, for net zero; no modules are pruned.
