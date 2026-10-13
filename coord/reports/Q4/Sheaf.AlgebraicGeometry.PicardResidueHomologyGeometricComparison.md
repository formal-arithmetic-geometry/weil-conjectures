## What changed

The unchanged main theorem is derived by unpacking separate Nonempty witnesses for
its source and target-family equivalences, then pairing them with True.intro.
Two new modules isolate these strictly smaller comparisons; the target comparison
is proved from the source comparison and existing pullback declarations. All imports of these
helpers by the main module are private. The source helper has no target-family
data; the target helper has no source complex or source model and does not assume
flatness, properness or finite presentation of f. No existing signature changes.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.picard_residue_homology_geometric_comparison`
(node `new-picard-residue-homology-comparison`), the only original hole.

New hole left:

- `AlgebraicGeometry.Scheme.picard_residue_homology_geometric_comparison_source`
  (node `new-picard-residue-homology-comparison-source`).

New theorem also proved: `AlgebraicGeometry.Scheme.picard_residue_homology_geometric_comparison_targets`
(node `new-picard-residue-homology-comparison-targets`). The target-family hole
proposed by the first worker was closed by specializing the source comparison.
The new Lean proof constructs the fibre map, transports tau using tensor pullback
composition and preservation of the unit, and transports invertibility.

This is a decomposition, not a completed geometric proof: one upper hole closed,
one lower hole added, net zero holes closed in this delivery. The main
statement still depends on sorryAx through the source obligation. No definition
is added or changed, and no data is chosen from a mere unproved existence theorem.

## No longer needed

Removed proof-only imports from the main module and omitted them from both helpers:
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`,
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`.
They were unused by the delivered Lean proof. Their mathematical arguments remain
part of the documented plan for the open geometric obligations. The old item's
proof_deps was empty, so there are no old proof-dependency nodes to remove.
No claim is made that these modules leave the full targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The first worker described the upper theorem as proved without explicitly counting
the two added holes. The report now calls this a decomposition and states its net.
The target-family hole was avoidable: it follows from the source comparison.
The helpers unnecessarily carried all the main theorem's hypotheses. Their
proof descriptions omitted residue-field transport and target coefficient
trivialization. Their nodes copied stale review records, attributed the work to
H3, and did not record their actual signatures or independently repeated searches.
These defects are repaired; the main theorem's statement was never changed.

## New nodes

`new-picard-residue-homology-comparison-source` states only the source comparison,
with complete finite-projective/K-flat, residue-field, base-change and coefficient
trivialization argument in its docstring. Its exact Lean signature is in the node.

`new-picard-residue-homology-comparison-targets` states only the target-family
comparison. The proof treats each i, transports tau along the induced fibre
map using hui, applies the source helper, and assembles the resulting equivalences. Both nodes record fresh
LeanFinder, Loogle, LeanSearch and grep searches; LeanSearch was unavailable.
Neither new statement has an existing user, so no change record is required.

## Second reading by Q4

1. Compared the main module with the read-only repository using diff. Its theorem
   signature, universes, instance assumptions and public imports are byte for byte
   unchanged. Only its docstring, private imports and proof changed. Both helper
   modules and nodes are new; their simplified signatures do not change an existing
   interface. Verdict: pass.
2. Compiled all three modules in import order using lcompile.py. The only sorry
   is the named public source helper theorem listed above. Scanned the files
   for forbidden declarations and hollow definitions. Scratch #print axioms checks
   confirm only standard axioms and sorryAx. Verdict: pass as a decomposition.
3. Checked each new statement as a proper part of the conjunction: source alone,
   target family alone. Neither restates the entire item. Removing unrelated data
   makes the separation explicit. Checked n=0 (empty target family), zero/rank-zero
   terms (retractions and quotient still work), and n=1 with ui the identity
   (the two comparisons agree). Nonzero differentials are retained. Immersion is
   essential for the residue-field identification, and tau and hui are essential
   for coefficient trivialization. Searched Mathlib and upstream/Sheaf code using
   fresh words. The existing affineFree_residueSections_cohomologyLinearEquiv
   requires free terms and compares to derived fibre cohomology; it does not close
   the strictly-projective geometric source comparison in a few minutes.
   Verdict: pass. The target helper is now proved using the source helper and
   existing tensor-pullback declarations; only the geometric source comparison is open.
4. Reviewed the shorter routes and removed unused proof imports. Existing public
   imports stay unchanged. The unit sk-prop-av-cube has empty realized entries;
   none is bypassed or changed by this internal source/target decomposition.
   The one retained source obligation makes this a net-zero decomposition
   rather than a net reduction in the sorry ledger. Verdict: pass.
5. The main node records the two actual helper dependencies and their packaging.
   New node signatures agree with Lean. The source node describes its open geometric
   argument with empty proof_deps because its current Lean body is sorry. The proved
   target node names the source, tensor composition, unit and invertibility dependencies.
   Creation, provenance, source, blueprint parent, chapter, unit and search fields
   are present. Removed stale review records from new nodes. Verdict: pass.

Second reading changed: proved the target-family helper; removed irrelevant hypotheses from
new helpers and updated calls; expanded source and target docstring proofs; removed unused helper imports
and scoped the linter suppression to the existing theorem; repaired node signatures/provenance/searches;
corrected decomposition accounting and pruning claims in this report.

Additional proof-only imports in the target helper: the source helper,
`Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor` and
`Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`. The two unused Mathlib
tensor/residue imports were also omitted from the new helper modules.
