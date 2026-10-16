## What changed

The fresh second reading also removed two private theorems duplicated between
the delivered files: `filtered_map_of_degreewise` and
`total_secondFiltration_map`. The main module now reuses the helper module
through proof-only `import all`. This removes 77 lines without changing any
existing signature, definition or public import.

Repair of the landing rejection at head `27d55f991`: removed the four duplicate
private theorems from `SecondFiltrationTwoColumnImage` and imported their existing
modules with proof-only `import all`. All call sites now use the existing
`CategoryTheory.Functor` declarations:

- `gradedPiece_isZero_of_complexStep_eq_bot` from `SecondFiltrationRowCohomology`;
- `pullback_kernelSubobject`, `kernelSubobject_of_cokernel`, and
  `iso_of_kernelSubobject_eq` from `SecondFiltrationRowCycleComparison`.

Their binders and conclusions match exactly. No replacement theorem, axiom, or
hole was added. Updated the helper node's proof, dependency union, and origin
note to record these actual imports. The earlier second-reading section below
is preserved as history; this repair needs a fresh independent reading.

Proved `CategoryTheory.cartanEilenberg_comparison_independence` with its existing signature
unchanged. The proof constructs the second filtration and comparison maps, uses Mathlib's
injective-resolution comparison homotopy and the existing CE double-complex homotopy
statement, transports homotopies through additive functors and extension by zero, and
applies filtered homotopy invariance. Identity and composition comparisons are explicit.

Added and proved `Sheaf.CategoryTheory.SecondFiltrationTwoColumnImage`. It computes the
concrete first page from horizontal cycles, removes the totalization sign, identifies
its homology with iterated cohomology, and combines normalized successor-page and
quotient-image comparisons. Every naturality square is proved using actual cycle
representatives and epi/mono cancellation, including the supplied target quotient map.

The main module combines that calculation with the supplied `FilteredPageTwoModel`.
It proves the horizontal cohomology comparison and naturality, constructs the explicit
injective resolution of horizontal cohomology, and applies `isoRightDerivedObj` and its
naturality. For the abutment it uses total cohomology with its finite image filtration
and degreewise stable quotient comparisons; independence, functoriality and filtration
preservation are proved explicitly.

Updated the main node's proof route and added a node for the two-column theorem. New
imports in the original module are proof-only. No existing definition, signature,
visibility or target changed. No forced adaptations or change records are needed.

## Proved and sorry left

Closed the original hole:

- `CategoryTheory.cartanEilenberg_comparison_independence`
  (`lem-sp-cartan-eilenberg-comparison-independence`).

The new theorem is also proved:

- `CategoryTheory.secondFiltration_two_column_image`
  (`lem-sp-second-filtration-two-column-image`).

No `sorry` remains in either delivered module; no new hole was added.
The current shared `TargetsCheck` source import closure does not reach this
item, so this local hole closure does not change the active targets' closure
ledger. No active-target hole reduction is claimed. The proof uses
existing stated stage-3 dependencies, so this does not claim that their full transitive
axiom closure has already been discharged. All new definitions are constructions or
choices determined by explicit normalization equations. The original theorem signature
is byte-for-byte unchanged, and all delivered Lean lines have at most 100 characters.

Both repaired modules compile without warnings via `lcompile.py --all`
(21.9 s for the helper and 31.3 s for the main module). The delivery dry run also checks
declaration axioms and node/report metadata. The required LeanSearch request returned an internal server
error; this is recorded without a mathematical verdict. Loogle, LeanFinder and
Mathlib-source searches were available and found no matching comparison.

## No longer needed

The main module no longer needs local copies of `filtered_map_of_degreewise`
and `total_secondFiltration_map`; both constructions are reused from the new
helper module. No extra module is pruned by this deduplication.

Removed these original direct imports and their uses from this item's proof route:

- `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`, node
  `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`: use Mathlib
  `InjectiveResolution.descHomotopy` directly.
- `Sheaf.CategoryTheory.CartanEilenbergComparisonHomotopy`, node
  `lem-sp-cartan-eilenberg-comparison-homotopy`: subtract the comparison maps and use
  `lem-sp-cartan-eilenberg-double-complex-homotopy` directly; restore the homotopy using
  `Homotopy.equivSubZero`.
- `Sheaf.CategoryTheory.CartanEilenbergFunctorial`, node
  `lem-weil-pbc-cartesian-eilenberg-functorial`: comparisons are supplied in the statement;
  the proof constructs identity/composite comparisons and filtered total maps directly.
- `Sheaf.CategoryTheory.ExactCoupleConvergence`, node `def-sp-convergence`: use the
  degreewise stable quotient theorem and the fixed quotient-image model instead.
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`, node
  `thm-sp-double-complex-spectral-sequences`: no arbitrary spectral-sequence existence
  theorem is needed. The fixed functor `M.S` gives the functor laws; the new two-column
  calculation gives its specified second page.

Removed duplicate direct imports `Sheaf.CategoryTheory.CartanEilenbergExists`,
`Sheaf.CategoryTheory.DoubleComplexTotal`, `Sheaf.CategoryTheory.Filtration`, and
`WeilConjectures.CategoryTheory.Abelian.Filtration`. Their necessary definitions remain
available through the unchanged public statement imports and proof dependencies.
`lem-sp-cartan-eilenberg-exists` is not used to choose any new resolution; its presentation
data remain part of the statement. These duplicate removals do not assert that those
modules disappear from the targets' global import closure.

The removed direct filtration imports are redundant, not pruned definitions:
`def-sp-filtration` remains a proof dependency for the explicit filtered maps.
`def-sp-left-exact-additive` also remains a proof dependency: its Mathlib match
includes `rightDerived` and `InjectiveResolution.isoRightDerivedObj`, used here.
The second reader restored both citations, and the filtration citation in the
new helper node, so the DAG records these actual uses.

Also removed the redundant direct import
`WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso`; its required API remains
available transitively, and the main module still compiles (25.8 s in that check).

A fresh source import-graph audit finds these nine modules absent from this item's import
closure after the change (other target parents may still need them):

- `Sheaf.CategoryTheory.CartanEilenbergAugmentedComparison`: `lem-weil-pbc-ce-augmented-comparison`.
- `Sheaf.CategoryTheory.CartanEilenbergComparisonColumnStep`: `lem-weil-pbc-ce-comparison-column-step`.
- `Sheaf.CategoryTheory.CartanEilenbergComparisonHomotopy`: `lem-sp-cartan-eilenberg-comparison-homotopy`.
- `Sheaf.CategoryTheory.CartanEilenbergComparisonObjectStage`: `lem-weil-pbc-ce-comparison-object-stage`.
- `Sheaf.CategoryTheory.CartanEilenbergComparisonObjectStage.Rows`: `lem-weil-pbc-ce-comparison-augmented-rows`.
- `Sheaf.CategoryTheory.CartanEilenbergFunctorial`: `lem-weil-pbc-cartesian-eilenberg-functorial`.
- `Sheaf.CategoryTheory.DoubleComplexBoundedBelowTotal`: `lem-weil-pbc-total-bounded-below`.
- `Sheaf.CategoryTheory.DoubleComplexFirstFiltrationDifferential`: `lem-weil-pbc-total-first-filtration-differential`.
- `Sheaf.CategoryTheory.DoubleComplexFirstFiltrationMap`: `lem-weil-pbc-total-first-filtration-map`.

A separate audit of the current shared `TargetsCheck` import graph finds that
this item is outside its closure; therefore no module is globally pruned from
the active targets by this delivery. The nine-module list is item-local only.

The inherited audit also listed `HorseshoeMorphismLiftExactSource` and
`CartanEilenbergComparisonCycleStage`; both remain reachable in the current shared
source graph, so they are not counted as pruned here.

The new two-column proof reuses generic internal graded-term and kernel/cokernel
lemmas from the existing row modules. The four duplicate private helper proofs
listed under `## What changed` are removed. Their modules,
`SecondFiltrationRowCohomology` and `SecondFiltrationRowCycleComparison`, are now
required proof imports, alongside `SecondFiltrationRowGradedCycles`; the earlier
claim that the first two could be avoided was wrong. Their transitive dependencies
are retained. The nine absent modules listed above remain absent after this repair,
as confirmed by a fresh source-graph audit. No additional module is pruned by the
repair itself. Removed unused draft helpers `column_graded_homology` and
`column_page_one_homology` remain absent.
`CartanEilenbergPageRealization` and `CartanEilenbergFilteredTruncationComparison` are not
imported: they depend on this item. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned version copied four generic theorems already present in the row
modules. The landing checker correctly rejected these duplicates. Reusing the
existing declarations requires `import all` because they are private. This
repair follows that route and makes the dependency metadata and pruning claims
agree with it. None of the four theorems depends on the specialized row-page
statements, so their use does not add a new proof hole.

The inherited sandbox left the derived second-page identification as a private `sorry`
without a node. Both that derived calculation and the underlying natural two-column
image calculation are now implemented. Nothing is left as an unnamed or private hole.

The original existence statement attached to `thm-sp-double-complex-spectral-sequences`
does not supply the normalized natural identification for an arbitrary supplied
`FilteredPageTwoModel`. The implementation explicitly uses that model's quotient-image
normalization. Existing row-page statements concern the flipped filtration; their
internal generic graded-column lemmas are reusable, but the actual second-page
identification and sign calculation are proved here for the required filtration.

The inherited unit field is `sk-prop-av-pqf-finite`, whose record concerns proper
quasi-finite morphisms and records no realized CE step. No unit or unit route changed.
The cited local Stacks `.tex` files are absent; the relevant arguments are available
at Tags 0130, 012K, 015K and 015N on the Stacks Project website.

The sandbox contained completed proofs from earlier dispatcher sessions. This session
preserved and checked those proofs, recompiled both modules, verified the original
signature and node dependency unions, and refreshed the import-closure pruning audit.
No additional agent was started.

## New nodes

`lem-sp-second-filtration-two-column-image`, module
`Sheaf.CategoryTheory.SecondFiltrationTwoColumnImage`, declaration
`CategoryTheory.secondFiltration_two_column_image`: the natural two-column cohomology-image
calculation from Stacks 0130 and 012K, now proved. Its statement has no resolutions,
derived functors, comparison homotopies, spectral-sequence model or convergence.
The proof handles vertical degree zero using the zero incoming extended column and
horizontal degree zero using the missing negative horizontal term. The normalization
also covers zero objects and maps, and uniquely identifies the supplied quotient map.

No change record is needed: no existing interface or statement changed.


## Earlier second reading (a previous round; superseded)

1. **Unchanged interface: PASS.** Compared both delivered modules with the shared
   repository. The original theorem signature is byte-for-byte identical, as are
   all four original public imports. The second module is new. No existing
   definition, visibility, target or other group's module changed; no change
   record or forced adaptation is needed.

2. **Proof and data: PASS.** Read both files in full and compiled the pair in import
   order through `lcompile.py --all`: 16.3 s for the helper and 25.8 s for the main
   module, with no errors or warnings. Neither file contains `sorry` or a forbidden
   declaration. A scratch `#print axioms` check gives only `propext`,
   `Classical.choice`, `Quot.sound` for `secondFiltration_two_column_image`; the
   main theorem additionally has inherited `sorryAx` from existing open
   dependencies, including the CE and filtered spectral-sequence homotopy
   obligations. The new resolution has the supplied cohomology complex and
   augmentation as its data. Chosen filtration lifts, cycle lifts and comparisons
   are fixed by monic inclusion or epic projection equations. The successor
   homology isomorphism and page differential have explicit uniqueness statements;
   there is no arbitrary object selected from an unproved existence claim.

3. **New statement and small cases: PASS.** No statement is split off with `sorry`.
   The fully proved helper is strictly the two-column image calculation, without
   resolutions, derived functors, comparison independence or convergence. Checked
   zero bicomplexes and zero morphisms, p=0 (negative incoming extended column),
   q=0 (negative horizontal term), a single nonzero bidegree, and a two-column
   complex with a nonzero vertical differential. The formula gives the expected
   kernel modulo image, with sign (-1)^q removed by (-1)^(p*q). The quotient
   projection and step inclusion equations uniquely fix the supplied target
   map. Repeated LeanFinder, Loogle and Mathlib-source searches with different
   queries, and searched both library roots. Existing row results use the flipped
   filtration; low-degree and spectral-object APIs do not provide this specified
   natural comparison. Checked the signs against
   [Stacks 0130](https://stacks.math.columbia.edu/tag/0130) and the representative
   formulas against [Stacks 012K](https://stacks.math.columbia.edu/tag/012K).

4. **Route, imports and pruning: PASS.** The main proof opens the original hole
   and combines Mathlib injective-resolution comparison homotopies and derived
   naturality with the actual CE homotopy and filtered-homotopy dependencies.
   It uses the supplied presentations and page-two model throughout. The helper
   proves the missing natural two-column calculation; it does not restate the
   original theorem. Proof-only imports use plain `import` (including `import
   all` for explicitly reused private lemmas). Public imports of the new module
   supply its statement's total complex, extension, Grothendieck instances and
   filtered quotients. Recomputed the source import closure and confirmed the
   nine modules listed above are absent from this item's new closure. This is
   an item-local audit, not a claim of nine globally pruned target modules. The
   unit's `realized` record contains no CE statement or step; it and its route
   are untouched. Every removed old proof dependency is named under
   `## No longer needed`; the filtration and derived-functor definition nodes
   are retained rather than incorrectly counted as unnecessary.

5. **DAG agreement: PASS after metadata repair.** Checked each proof step against
   its implementation, both exact unions of step `uses` against `proof_deps`,
   and the new node's Lean statement byte-for-byte. The main node changes only
   `proof`, `proof_deps` and `proof_origin`. The new node has its complete source,
   searches, creation, blueprint, chapter, unit and Lean records. Restored
   `def-sp-filtration` in both proof routes and `def-sp-left-exact-additive` in
   the main route, since the proofs explicitly use the corresponding APIs.

Second-reading changes: corrected the dependency metadata, recorded independent
searches and the above review, and clarified the pruning report. No Lean proof or
statement repair was necessary. Closed one of one original holes, added zero
holes, and introduced one already-proved helper theorem: this is a proof, not a
decomposition. The transitive main-theorem closure still contains existing holes.


## Second reading by N2

1. **Visible interface: PASS.** Compared the delivered main module with the
   shared version using `diff` and declaration-table inspection. The original
   `cartanEilenberg_comparison_independence` statement is byte-for-byte unchanged,
   and its four public imports are identical. The helper module is new. No
   existing definition, visibility, target or other group's module changed;
   no change record or forced adaptation is required.

2. **Proof, axioms and data: PASS.** Read both delivered modules in full and
   recompiled scratch copies of their final contents in import order with
   appended `#print axioms` through `lcompile.py --all`. The two-column theorem
   uses only `propext`, `Classical.choice`, `Quot.sound`. The main theorem also
   depends on inherited `sorryAx` from existing open dependencies; this is one
   original hole closed, with zero new holes, rather than a claim that its
   transitive closure is complete. Neither delivered file contains `sorry` or
   a forbidden declaration, and compilation emits no warnings. Final scratch
   compiles took 21.4 s for the helper and 22.2 s for the main file. The explicit
   horizontal-cohomology resolution retains the supplied complex and augmentation.
   Filtration choices are determined by degreewise step equations; left-exact
   cohomology comparisons are determined by the normalized epic cycle projection.
   Page differentials and successor isomorphisms have uniqueness statements.
   Other chosen lifts are fixed by monic inclusion or epic projection equations.
   No arbitrary data is extracted from an unproved mere-existence statement.

3. **New statement and duplication: PASS after repair.** No statement is split
   off with `sorry`. The proved helper concerns only two-column quotient images
   and their naturality; it has no derived functors, presentations or comparison
   homotopies, and therefore does not restate the original item. Checked p=0,
   q=0, zero bicomplexes and maps, a single nonzero bidegree, and a two-column
   complex with nonzero vertical differential. These give the expected kernel
   modulo image; the totalization sign is removed by (-1)^(p*q). The target
   quotient map is fixed by its epic projection square. Fresh LeanFinder,
   Loogle and Mathlib-source searches used different queries from the previous
   worker; no existing natural two-column image comparison was found. Searched
   both library roots as well. Verified that the four previously duplicated
   row lemmas are now imported from their original modules. Found and removed
   two further duplicates between this delivery's modules: the main module now
   imports and reuses the helper's private filtered-map constructions.
   Checked the sign and iterated-cohomology formulas against
   [Stacks 0130](https://stacks.math.columbia.edu/tag/0130), and the representative
   formulas and cohomology image filtration against
   [Stacks 012K](https://stacks.math.columbia.edu/tag/012K).

4. **Route, imports and pruning: PASS.** Followed the proof from the original
   theorem downward: Mathlib resolution homotopies, the stated CE double-complex
   homotopy and filtered-homotopy invariance, explicit identity/composite maps,
   the normalized two-column calculation, derived-functor naturality, and the
   degreewise stable quotient comparison. Read the reused normalization APIs
   to check uniqueness and naturality. New proof imports are plain `import`
   or `import all`; the helper's public imports supply its statement's types
   and constructions. All six removed old proof dependencies are named under
   `## No longer needed`. Recomputed the source import graph: exactly the nine
   listed local modules leave this item's closure. The closure also gains
   modules needed by the explicit calculation, so this is not a claim of nine
   globally pruned modules or a net module reduction. A separate `TargetsCheck`
   audit finds this item currently outside the active targets' import closure,
   so the active-target closure ledger is unchanged. The inherited unit has
   `realized.statement = []` and `realized.steps = [[]]`, with no CE step;
   the unit and its route are unchanged.

5. **DAG agreement: PASS.** Checked each proof step against the Lean, exact
   unions of step `uses` against `proof_deps`, and the new node's Lean statement
   byte-for-byte. The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. The new node has its source, full proof, recorded real
   searches, creation, blueprint, chapter, unit, and Lean fields. Its row-node
   citations represent the actually imported generic private helpers; they
   do not claim use of the specialized flipped-row page statements. Retained
   the filtration and derived-functor definition dependencies. Updated the main
   proof-origin note to record reuse of the filtered-map constructions, and
   added the fresh search records to the new node.

Second-reading changes: removed two duplicate private theorem bodies from the
main module, changed its helper import to proof-only `import all`, updated the
proof-origin/search metadata, and recorded this independent review. No statement
or mathematical proof repair was needed. Closed one of one original holes;
added zero holes; one new helper theorem is already proved.

Delivery verification: the required `deliver3.py --no-push` returned OK after
compilation, axiom probes and preflight (CODEX class because the delivery adds
a proved node and its module).
