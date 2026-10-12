## What changed

Replaced the single proof hole of `CategoryTheory.filteredComplex_successor_cycles_cover`
by a combination of the kernel-factorization theorem
`CategoryTheory.filteredComplex_successor_cycles_cover_exists` and the epimorphy theorem
`CategoryTheory.filteredComplex_successor_cycles_cover_epi`. The original declaration's
signature and docstring are unchanged. Both new modules are imported privately (plain
`import`); their signatures use the two public imports they declare. No definition or
existing public interface changes, and no change record is required.

This is a decomposition into two strictly smaller obligations, not a completed proof of
the underlying mathematical result. The existence statement makes no epimorphy assertion;
the epimorphy statement assumes a factorization and does not construct one.

## Proved and sorry left

Holes closed: `CategoryTheory.filteredComplex_successor_cycles_cover`
(node `lem-sp-filtered-complex-successor-cycles-cover`), by the two new statements.

Holes added and still open:

- `CategoryTheory.filteredComplex_successor_cycles_cover_exists`
  (node `lem-sp-filtered-complex-successor-cycles-cover-exists`).
- `CategoryTheory.filteredComplex_successor_cycles_cover_epi`
  (node `lem-sp-filtered-complex-successor-cycles-cover-epi`).

The delivery replaces one hole by two: local net holes closed minus added is -1.
There are no other holes in the delivered modules, and no data definitions are added.
The original theorem still depends on `sorryAx` through these open statements; it is not
an axiom-free proof. No claim of positive sorry-ledger progress is made. Global closure
and pruning figures are for the maintainer's pinned-baseline ledger to determine.

## No longer needed

No imports or modules are pruned. All old dependencies are still needed transitively.
The old direct proof dependencies `def-sp-abelian`, `def-sp-filtration`,
`def-sp-filtered-complex-subquotients`, and `lem-sp-filtered-complex-page-differential`
are replaced in the parent node's direct proof dependency list by the two new nodes;
each new node retains those four dependencies. This is a change of dependency depth,
not removal of those mathematical inputs.

## Where the brief, the DAG or earlier work was wrong

The initial draft's new nodes depended on the parent theorem they were supposed to prove.
That circular plan has been removed. Their new proof plans and docstrings give separate
kernel-factorization and representative-correction arguments. The parent node now matches
the actual two-lemma Lean proof. The draft also copied unrelated historical review records
onto the new nodes; those records have been removed. Its short docstrings lacked complete
natural-language proofs and precise sources; these have been supplied.

The inherited unit identifier is `sk-prop-av-pqf-finite`, whose unit is about proper
quasi-finite morphisms and whose `realized.statement` and `realized.steps` lists are empty.
This appears to be inherited classification metadata, rather than a unit realized by this
spectral-sequence auxiliary lemma. No unit route, unit record or blueprint step is changed.

## New nodes

`lem-sp-filtered-complex-successor-cycles-cover-exists`, in
`Sheaf.CategoryTheory.FilteredComplexSuccessorCyclesCoverExists`, states only the kernel
factorization. Its proof first annihilates the successor inclusion using the representative
formula and then applies the kernel universal property.

`lem-sp-filtered-complex-successor-cycles-cover-epi`, in
`Sheaf.CategoryTheory.FilteredComplexSuccessorCyclesCoverEpi`, states only epimorphy for a
map satisfying the representative equation. Its proof corrects a lifted representative
x by y in F^(p+1) so that d(x-y) lies in F^(p+r+1). Both nodes have sources, complete
proof plans, creation and blueprint metadata, and verbatim Lean statements. No change
record is needed because no existing statement or definition changes.

## Earlier second reading (a previous round; superseded)

The initial draft contained a short earlier review; this section records that it is
superseded by the independent second reading below.

## Second reading by B3

1. Compared the delivered target module against the repository with `diff -u` and checked
   the declaration signature byte for byte. PASS: only its proof and two plain imports
   differ; its hypotheses, conclusion, universe variables, visibility and docstring are
   unchanged. The two added modules introduce only new theorem declarations.
2. Compiled all three modules in import order through `lcompile.py --all`. PASS: no
   errors or warnings. There are exactly two named theorem holes, listed above; no axiom,
   unsafe, opaque, implemented_by, extern, hidden proof hole or data definition is added.
   Independent scratch `#print axioms` checks cover the parent and both new declarations;
   only the standard axioms and `sorryAx` are permitted because the split statements
   remain open. The final delivery tool also probes every delivered declaration.
3. Read the definitions of graded cycles, graded boundaries and page differential data,
   and checked both new statements against the displayed formulas in Stacks Tag 012K
   (https://stacks.math.columbia.edu/tag/012K). PASS as strict substatements. The target
   boundary uses incoming filtration (p+r)-r+1 = p+1, so the correction preserves the
   source graded class. At r=1 the same correction works; if the graded source is zero,
   the representative argument forces the outgoing kernel to be zero; for the zero
   complex and a filtration with zero graded pieces both assertions reduce to the zero
   map between zero objects. For d=0, the successor cycles agree with the r-cycles and
   the quotient projection covers the whole page. The lifting arguments use epimorphic
   refinements, never projectivity. Separate leanfinder, loogle and grep searches and
   local rg searches found no duplicate of these filtered statements. The required
   leansearch request returned Internal Server Error; this unavailability is recorded
   separately in each new node, without claiming a negative search result. Mathlib liftCycles
   supplies the generic factorization once annihilation is established, but does not
   close that concrete representative calculation or the epimorphy calculation.
4. Checked the original proof plan and searched for a shorter existing route. PASS with
   the limitation that this is a decomposition. The lower representative calculations
   remain substantial; neither closes in a short application of a searched theorem.
   Imports are needed by the signatures or by the parent proof; all old dependencies
   remain transitively used and are accounted for above. The inherited unit's realized
   lists are empty, and this change bypasses no realized unit statement or step.
5. Compared all node proof plans, dependency lists and Lean records with the modules.
   PASS after repair: the parent depends on the two new statements, and the new nodes
   depend on the original definitions and differential data, with no edge to the parent.
   New nodes have the required source, search, created, blueprint, chapter, unit and Lean
   fields. Their Lean statements are copied verbatim from their new declarations.

Second reading changed: expanded the two split-theorem docstrings into complete sourced
proofs; repaired the circular new-node dependencies and stale parent proof plan; removed
copied review metadata; repeated searches using different wording; corrected the report to
state the decomposition and negative local hole balance explicitly. No Lean proof body
or existing signature needed repair.
