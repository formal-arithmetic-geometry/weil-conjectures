## What changed

Repair of return X-59b54: retire the unused duplicate declaration
AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_local from
Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal. Map its existing
DAG node new-determinant-split-local to the already-proved
AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_exists in
Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison. The latter supplies
exactly the requested local wedge formula together with naturality. Update the
node statement and Lean record to the canonical signature, with a statement_change
record documenting the retained hypotheses and added naturality. Update its proof
and proof_deps to reuse lem-sc-determinant-split-comparison.
Remove the two unused private proof imports. Keep the public imports and the
restriction-transfer theorem, including its signature, docstring and proof,
unchanged. No other Lean module or target is changed.
Change record: coord/changes/determinant-split-local-naturality.md.

## Proved and sorry left

Holes closed: 0 of 0 baseline holes. Holes added: 0. Split off: 0.
AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction
(new-determinant-split-restriction) remains completely proved by substitution.
AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_local is retired,
not counted as a proof gain. The existing determinant_split_comparison_exists
(lem-sc-determinant-split-comparison) already proves the desired stronger result
and is now the Lean realization of new-determinant-split-local. No sorry remains
in the item and none is introduced elsewhere. This is duplicate pruning.
The repaired file compiles cleanly locally in 2.4 seconds and on the server.
import_prune_check.py passes; the axiom probe reports no forbidden axioms.
The delivery dry run passes pending the independent second reading.

## No longer needed

Removed imports from this item:

- Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearMaps
- Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective

Retired duplicate declaration determinant_split_comparison_local and its separate
construction proof. The node now reuses the existing canonical comparison.
lem-sc-split-determinant-linear-maps and
lem-sc-split-determinant-linear-bijective are no longer direct proof dependencies
of new-determinant-split-local, but remain needed by the canonical theorem;
no whole-library pruning of their modules is claimed. The item module remains
needed for new-determinant-split-restriction. No module is claimed unreachable.
The unit route through determinant additivity is retained.

## Where the brief, the DAG or earlier work was wrong

The returned delivery proved a strengthened local theorem whose complete statement
was already determinant_split_comparison_exists. An import of that theorem into
this module would create a cycle through the restriction-transfer lemma. Retirement
of the unused duplicate plus a DAG realization redirect resolves both issues.
Full-library textual search and downstream --uses found no Lean caller of the
retired declaration. No DAG node names new-determinant-split-local in stmt_deps
or proof_deps. The existing canonical theorem has all original hypotheses and
both requested conclusions; no target or source conclusion is weakened.
Its rank-zero, empty-open and zero-ring cases retain the same hypotheses and
conclusions. No new mathematical statement, witness or definition is introduced.
The previous second reading describes the superseded delivery and has been
removed; the second reader must independently review this repair.

## Second reading by M1

1. Compared the delivered module with the repository by diff. The only Lean
   changes are retirement of determinant_split_comparison_local and removal of
   its two private proof imports, exactly as declared in the change record.
   The restriction theorem's signature, docstring, and proof are byte-for-byte
   unchanged. Full-library rg finds no caller of the retired name. No target,
   definition, public import, or other module changes. Verdict: pass.
2. Independently compiled the delivered file using lcompile.py without errors or
   warnings. Inspected its entire proof: rewriting the pointwise equality on both
   sides reduces the conclusion to hn. No sorry, forbidden declaration, or data
   construction occurs. A fresh scratch copy's #print axioms for the restriction
   theorem reports exactly propext, Classical.choice, Quot.sound. A separate
   import probe reports the same for determinant_split_comparison_exists.
   Verdict: pass; the canonical theorem is proved, not merely stated.
3. No new statement or split-off hole is introduced. Independently searched Lean
   for the retired name and read the existing canonical comparison theorem and
   proof. Its hypotheses match the retired theorem verbatim; its first conjunct
   is the same wedge conclusion. The empty-open case is vacuous at the point
   quantifier; rank-zero and zero-ring cases add no new assumptions. The retained
   restriction theorem is substitution for arbitrary ranks and sections, hence
   covers these cases directly. An independent msearch grep query using
   'restriction natural linear equivalence' returned no match. Verdict: pass.
4. Reusing the canonical theorem eliminates the duplicate construction without
   introducing an import cycle: its module already imports this module solely
   for the retained restriction theorem. Both removed imports and both obsolete
   direct dependencies are listed under No longer needed; they remain needed by
   the canonical theorem, so no unreachable module is claimed. Read the unit's
   realized record: neither changed node is a designated unit statement or step;
   determinant additivity's route is preserved. Public signature imports remain
   unchanged. Verdict: pass.
5. Checked the delivered node's statement and lean.statement against the actual
   canonical signature, and its proof/proof_deps/proof_origin against the reuse
   route. Its dependency on lem-sc-determinant-split-comparison is acyclic: that
   node depends on the two linear lemmas and the restriction node, not the retired
   local node. Searched all node stmt_deps/proof_deps: no citer of the redirected
   local node requires adaptation. The unchanged restriction node describes the
   substitution proof accurately. The change record documents the retirement,
   old/new signatures, downstream effects, and open status. Verdict: pass.

Second reading changed only this report, adding independent review evidence;
no Lean or DAG repair was necessary. Holes closed 0 of 0; holes added 0.
