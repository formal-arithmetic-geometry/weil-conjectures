## What changed
The target theorem is proved by constructing the canonical quotient transition morphisms via the cokernel universal property, then applying the canonical-pages theorem. The latter is stated as a separate intermediate theorem with its full proof plan and remains the sole `sorry` introduced by this delivery.

## Proved and sorry left
`CategoryTheory.boundedFilteredComplex_spectralSequence` is proved. `CategoryTheory.boundedFilteredComplex_canonicalPages` remains `sorry` in the new node `thm-sp-spectral-object-yields-canonical-pages`.

## No longer needed
Removed direct proof imports from the target: `Sheaf.Algebra.Homology.FilteredComplexZBDescription`,
`Sheaf.CategoryTheory.ExactCouple`, `Sheaf.CategoryTheory.ExactCoupleMorphism`, and
`Sheaf.CategoryTheory.SpectralSequencePageInduction`. These are retained for the proof plan
of the new canonical-pages module. No module or old dependency is pruned from the target closure.
The old direct proof dependencies `lem-sp-long-exact-of-triangle`, `def-sp-exact-couple`,
`def-sp-spectral-sequence`, `lem-sp-page-induction`, `lem-sp-filtered-complex-ZB-description`,
`def-sp-convergence`, and `lem-sp-couple-morphism` are now dependencies of the intermediate
construction, rather than direct uses in the target proof. The target's direct dependencies
are `def-sp-filtered-complex-subquotients` and `thm-sp-spectral-object-yields-canonical-pages`.

## Where the brief, the DAG or earlier work was wrong
The original node placed the entire construction and all six long proof steps in one theorem. The cokernel construction is fully proved here; the long canonical-pages argument is isolated as a strict intermediate theorem, while the target statement remains unchanged.

## New nodes
`thm-sp-spectral-object-yields-canonical-pages` records the canonical-pages, compatibility, convergence, and stabilization component used by the proved target.

## Earlier second reading (a previous round; superseded)
The target signature is unchanged. The cokernel transition proof compiles, and the canonical-pages intermediate theorem is strictly the remaining construction required by the target.

## Second reading by E2
1. Compared the existing module with the repository using `diff -u`: its theorem signature
   and existing documentation are byte-for-byte unchanged. Only four private proof imports
   and the proof body differ. There are no existing definitions altered and no change records
   are needed. The added module has one new theorem, not a changed existing declaration.
2. Both delivered modules compile locally in import order without errors or warnings.
   Separate scratch copies with `#print axioms` were checked. The target and intermediate
   use only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` (the explicitly open
   canonical-pages theorem and imported open proofs). There is exactly one new `sorry`,
   in that named theorem; no definitions or forbidden declarations are added.
3. Read the intermediate's whole statement and proof docstring against the quotient
   definitions, exact-couple indexing and existing Z/B theorem. At r=1 the transition is
   the identity by its projection equation and cokernel epimorphy. For a complex concentrated
   in degree zero with a one-step filtration the image pages are the graded cohomology;
   for the identity two-term complex filtered by F^1=(0,A), F^0=(A,A), F^2=0, the r=2 image
   vanishes as required. Zero complexes satisfy all comparisons and support assertions.
   Checked the degree conversion (P,Q)=(2p+q,-p): filtered differential (r,1-r) becomes
   (r+1,-r). The new theorem assumes already constructed canonical transitions and leaves
   only the page/comparison/convergence component open; the target proves their existence
   by a genuine cokernel-desc argument, not by a renamed application of its whole statement.
   Independent leanfinder, loogle and grep searches found no theorem supplying this full
   construction. Mathlib's spectral-object API supplies pages from an existing spectral
   object, not all these filtered-complex and exact-couple comparisons. The existing Z/B
   theorem supplies pointwise page data but not the functor, naturality or convergence here.
   Closing the remaining construction is not a few-minute task.
4. All public imports name objects used in the signatures; construction-only imports are
   private. The cokernel construction uses existing Mathlib universal-property lemmas.
   The pruning section now names every removed direct import and old direct dependency,
   and explicitly records that none is removed from the closure. The unit's `realized`
   record is unchanged: this node does not realize the unit's proper/quasi-finite statement
   or its step. Its original six construction steps remain in the intermediate proof plan.
5. Repaired the missing parent-node update: its proof now describes the cokernel construction
   and application of the intermediate, with corresponding direct dependencies and origin.
   Checked all new-node fields, dependency union, source, chapter/unit and declaration.
   Replaced the vague natural-language statement with a self-contained account of all clauses,
   copied the Lean signature verbatim into its Lean record and added independent searches.

Changes on second reading: repaired DAG metadata, completed the pruning report and search
record, and made the new node statement self-contained. The Lean proofs were already correct
as a partial reduction and were not rewritten. The result closes the target proof body,
not its axiom-free transitive proof: canonical pages remain open.
