## What changed

Completed `CategoryTheory.colimit_site_set_section_eventual_equality` without changing its
signature or visibility. Added three proof-only imports, each with a new statement module:
`ColimitSiteRawSectionDiagram`, `ColimitSiteRawSectionEvaluation`, and
`ColimitSiteRawSectionSheaf`. Added the filtered Under-category instance, connected constant-colimit API, and the
Mathlib filtered-set equality criterion as proof imports. The two private helpers
`raw_comparison_iso` and `raw_colimit_comparison_iso` are fully proved: they establish
the stage adjunction comparison and its colimit comparison after sheafification. Updated the item's DAG proof to match.

The proof constructs an actual raw presheaf colimit, proves its comparison with the limit
inverse image is an isomorphism by sheafification-unit naturality, then transfers the
supplied equality to a genuine set-colimit cocone and applies the same-stage equality
criterion. The three remaining statements separate formal Kan/adjunction construction,
raw presheaf evaluation, and the finite-cover sheaf condition. The full adjunction and
sheafification-isomorphism argument is written in Lean in the item itself. None restates eventual
equality in the limit inverse-image sheaf.

All four modules compile locally without warnings. No existing definitions or interfaces
were changed, and no adaptations or change records are needed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.colimit_site_set_section_eventual_equality`
(node `lem-weil-pbc-colimit-site-set-section-eventual-equality`). Its proof has no `sorry`.

Added three holes, all whole proofs of named public theorems in separate modules:

- `CategoryTheory.colimit_site_raw_section_diagram`
  (`lem-weil-pbc-colimit-site-raw-section-diagram`). Constructs the raw Kan diagram and
  its compatible maps only; it assumes neither
  category-colimit hypotheses nor finite-cover hypotheses.
- `CategoryTheory.colimit_site_raw_section_evaluation`
  (`lem-weil-pbc-colimit-site-raw-section-evaluation`). Computes raw presheaf evaluation
  as a section-set colimit, for an arbitrary comparison presheaf T; it assumes no
  sheafness or section-equality criterion in a limit inverse image.
- `CategoryTheory.colimit_site_raw_section_isSheaf`
  (`lem-weil-pbc-colimit-site-raw-section-sheaf`). Proves the finite-cover sheaf condition
  for the actual raw colimit; it has no alpha, K, e, D, or section-equality conclusion.

This is a decomposition: one hole closed, three added, net minus two holes. The theorem
still transitively depends on those three sorries; this is not a fully axiom-free proof.
The Kan objects and maps are determined up to compatible isomorphism by their universal
units and factorization equations. The evaluated cocone is a colimit, but its chosen
isomorphism q is only constrained after composition with the arbitrary comparison map;
that equation need not determine q. All existence witnesses are destructured inside a
theorem proof. No definition chooses data from a mere-existence theorem.

## No longer needed

No original imports were removed from the item: its public imports support its unchanged
statement. No existing node or module is claimed globally pruned. The following old
proof dependencies are no longer direct dependencies of the item's proof:

- `def-weil-pbc-category-colimit` (retained as a statement dependency and beneath all
  three new statements; Mathlib's colimit construction is still used directly).
- `def-weil-pbc-finite-precoverage` (retained as a statement dependency and beneath the
  raw sheaf-condition statement).
- `lem-weil-pbc-filtered-colimit-categories` (needed beneath raw evaluation and sheafness).
- `lem-weil-pbc-filtered-colimits-commute-finite-limits` (needed beneath raw sheafness).
- `lem-weil-pbc-initial-functor-cofiltered-criterion` (needed beneath raw evaluation
  and sheafness; its Mathlib module also supplies the filtered Under instance used here).

Second reading removed the unused `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
import from `ColimitSiteRawSectionDiagram`. Its statement needs no presheaf colimit
instance. The evaluation and sheaf-condition modules retain this public import because
`colimit B` and its instance occur in their public signatures.

Deleted the earlier sandbox-only `AColimitSiteSetSectionCoconeIsColimit.lean`: its proposed
whole section-cocone universal property carried the substance of the original goal and
had no node or complete docstring. The replacement is the three-part reduction above.
The new formal diagram and evaluation modules omit the finite-precoverage import, which
their statements do not need. The formal diagram uses Mathlib Cat directly, not the
project's arrow-colimit functor.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt treated the absence of a proved section-cocone construction as a
reason to abandon. The supplied dependency statements do not themselves construct that
presheaf, but stage 3 permits the missing construction steps as named intermediate
statements. These steps are now stated in Lean and combined by a complete compiled proof.

The raw Kan colimit is an explicit categorical construction: `colimit B`. The proof
separates its sheaf condition from its raw evaluation and from the formal comparison
after sheafification. This keeps finite-cover descent out of the raw evaluation lemma.
The unit's realized statements and route are unchanged.

Checked edge cases in the new statements: an empty source stage supplies no U, so the
evaluation assertion has no instance there; the raw diagram still exists for sheaves on
an empty stage by Kan extension. The filtered Under category is nonempty (the identity
arrow) and connected. Empty covers are included in the sheaf lemma and force the
terminal-set condition. For a constant one-stage diagram, raw Kan extension along the
identity returns the original sheaf and all three steps reduce to their identity cases.
The evaluation lemma allows arbitrary T, including non-sheaves, since it only uses
naturality and Kan universality.

Read the Stacks source online at https://stacks.math.columbia.edu/tag/0A35: the presentation,
finite-cover, and adjunction paragraphs. The local `literature/stacks-project/sites.tex`
is unavailable on this machine. The new nodes mark the explicit Kan realization as an
agent-written elaboration of those paragraphs. Search: LeanFinder and Loogle gave only
supporting APIs, and source search found the Kan pointwise formula and filtered-set
criterion. LeanSearch returned Internal Server Error, recorded as unavailable, not as
absence. Blueprint search found no exact existing statement for this raw decomposition.

## New nodes

`lem-weil-pbc-colimit-site-raw-section-diagram`, module
`Sheaf.CategoryTheory.ColimitSiteRawSectionDiagram`: formal Kan-extension diagram with
universal units and compatible comparisons. It isolates the
presheaf diagram-construction part of Tag 0A35 and carries the complete construction proof in its docstring.

`lem-weil-pbc-colimit-site-raw-section-evaluation`, module
`Sheaf.CategoryTheory.ColimitSiteRawSectionEvaluation`: raw pointwise Kan-colimit section
formula, including its compatibility with any presheaf comparison. It isolates lifting
of arrows and relations and does not use finite covers.

`lem-weil-pbc-colimit-site-raw-section-sheaf`, module
`Sheaf.CategoryTheory.ColimitSiteRawSectionSheaf`: finite-cover sheaf condition for the raw
presheaf colimit. Its proof includes empty covers and generated-topology passage.

Every new node has the item's chapter and unit, a source, a full natural-language proof,
three actually executed kinds of search (including the failed LeanSearch), and a Lean
record. No change record is required.


## Second reading by F2

Independent second reader, 2026-10-13. Read all four delivered modules, all four node
files, the original item and its eight proof dependencies, and `sk-thm-p1`'s `realized`
record. Read Stacks [0A35](https://stacks.math.columbia.edu/tag/0A35)
(`lemma-compute-pullback-to-limit`), its presentation, finite-cover and adjunction
paragraphs, together with the setup [0A34](https://stacks.math.columbia.edu/tag/0A34)
and category/cover construction [09YL](https://stacks.math.columbia.edu/tag/09YL).

1. **Visible declarations: pass.** Compared the item with the repository by `diff` and
   extracted its entire theorem signature: byte-identical, including universes,
   typeclass hypotheses, hα/hθ as Arrow-object equalities, hι/hm, and the single-arrow
   eventual-equality conclusion. Only proof imports, private proof helpers, and the
   original theorem body changed. The other three modules are new. There are no changed
   definitions, public signatures, forced adaptations, or change records.

2. **Lean proof and axioms: pass as a decomposition.** Compiled all four files through
   `lcompile.py --all`, without errors or warnings. The item contains zero sorries;
   each new module has exactly one, as the whole proof of its reported public theorem.
   Scanned for forbidden declarations and implementation attributes: none. A scratch
   copy with `#print axioms` for the main theorem, all three new theorems, and both
   private helpers compiled. Both helpers have exactly propext, Classical.choice and
   Quot.sound; the four public theorems additionally have sorryAx. The main proof
   correctly identifies κ with the composite-adjunction comparison, proves the
   sheafified γ maps invertible using Kan uniqueness and the sheafification counit,
   passes this to the colimit using connectedness, and cancels the two sheafification
   units. Its final cancellation of q and φ followed by
   `Types.FilteredColimit.isColimit_eq_iff'` produces one common refinement arrow.
   The scratch copy was removed. No data is chosen in a definition from an open theorem.

3. **Split statements: pass.** The diagram lemma isolates Kan units, extension maps
   and γ naturality, without object/arrow-colimit or finite-cover assumptions. hθ
   identifies transition maps by adjunction uniqueness, and hα ensures γ compatibility;
   Kan universality then proves functor laws and naturality. The evaluation lemma
   uses the object and arrow colimits to lift representatives and their finite Kan
   relations; hβmap and hm identify the lifted transition maps. Its arbitrary T does
   not need sheafness. The sheaf lemma uses hQ to lift a cover, hfinite for its finite
   matching diagram, hcover to keep it covering at later stages, and hpullback and
   hVpullback to compare the matching pullbacks; finite-limit commutation supplies
   descent, including the empty cover. These are separate proper parts of 0A35's
   construction, not a renaming of the original eventual-equality assertion.
   All three docstrings give the argument and blueprint id, and all have matching
   new nodes. Tested the constant one-stage/identity case, empty stage categories
   (no U there; Kan construction remains meaningful), empty covering families
   (terminal section sets), and a non-sheaf or terminal T in evaluation. In the
   terminal T case q is not determined by its displayed composite equation; that is
   harmless because witnesses are eliminated only inside a proof, and the report
   now states this accurately.

   Independently searched LeanFinder for "left Kan extension presheaf filtered
   diagram continuous functors colimit site", Loogle for
   `CategoryTheory.Functor.IsLeftKanExtension`, and msearch grep for
   `isSheaf.*colimit|colimit.*isSheaf|leftKanExtension.*obj|pointwiseLeftKanExtension`.
   These found supporting Kan APIs, not any of the three new statements. Also
   searched repository `lean/Sheaf` and upstream `WeilConjectures/CategoryTheory`
   with Kan/presheaf/presentation and colimit/site terminology. Read
   `SiteFilteredColimitSections`, upstream `Pro/PresheafColimit`, and upstream
   `GrothendieckAbelian/HasLeftKanExtension`: the first concerns already-sheaf
   diagrams on one fixed site, the second needs a fully faithful fixed functor and
   compactness, and the third concerns small scheme sites and abelian coefficients.
   None computes this varying-site raw diagram or proves its sheafness. The existing
   section-presentation and inverse-image modules depend on this item, so applying
   them would be circular. No split-off hole closes by a short application of those APIs.

4. **Top-down route and pruning: pass after report/import repair.** The main proof
   opens the original hole and combines three genuinely different construction
   tasks with two fully proved comparisons and the existing Mathlib equality
   criterion. The old conjugate-isomorphism node is realized by the recorded
   `Adjunction.leftAdjointUniq` specialization, and the filtered-set node by its
   recorded same-stage criterion. Removed the diagram module's unused functor-category
   colimit import; remaining new imports support statements or the proved argument,
   and proof-only imports in the item are plain `import`. Expanded `No longer needed`
   to enumerate all five old nodes absent from the new direct proof_deps, explaining
   their retained roles below the new statements. No globally pruned module is claimed.
   No node in `sk-thm-p1.realized` is replaced or bypassed; the changes are below the
   unit level and follow the same presentation, descent, adjunction route of 0A35.

5. **DAG versus Lean: pass.** Checked the new natural-language statements against
   every parameter and conclusion in their Lean signatures, including universal
   Kan units, Arrow transports, arbitrary T, and the empty-cover case. The main
   node's three proof steps are respectively the diagram plus compiled adjunction
   comparisons, raw sheafness plus unit cancellation, and raw evaluation plus the
   filtered-set equality criterion. In each node proof_deps is exactly the union
   of step uses; source and proof_origin identify the agent's Kan elaboration of
   0A35 rather than claiming it is a literal source statement. New nodes have the
   required source, searches, creation, blueprint, chapter/unit and Lean fields.
   Original statement and statement dependencies are unchanged. The three new
   nodes retain the original lifting, finite-limit and finality tools in their
   planned proofs. Existing node fields outside the permitted stage-3 fields were
   not edited by this reader.

Changed only the unused import in the new diagram module and this report: completed
pruning enumeration, corrected the assertion about q's determination, and added the
independent second reading. The accounting remains one original hole closed, three
strictly smaller holes added, net minus two; no claim of an axiom-free completed module.
