## What changed

Repaired the returned delivery of
`Sheaf.AlgebraicGeometry.RestrictionNaturality`. Removed both copied private
helper declarations, `lift_nat_quasiIso` and `unique_nat_quasiIso`, and reused
the existing private theorems in `ModuleCohomologyFMapComparison` through
`import all Sheaf.AlgebraicGeometry.ModuleCohomologyFMapComparison`.
This is a proof-only import: no existing signature, visibility, definition or
docstring changes, and no other module is adapted. The import is acyclic.

The remaining local proof compares the actual coefficient morphism, proves
sections and resolution transport naturality, and cancels the resulting homology
squares. Updated only the existing node's proof, proof_deps and proof_origin
to record reuse of the comparison module's existing helper arguments.
The unit sk-thm-p1 and its realized route are unchanged.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_target_iso_naturality`
(node `lem-weil-pbc-module-cohomology-fmap-target-iso-naturality`).
No sorry remains in this module; no holes were added and none were split off.
All retained private helpers are proved. The repaired module compiles without
warnings through lcompile.py. The delivery dry run checks axioms for all
its declarations; only propext, Classical.choice and Quot.sound are permitted.

## No longer needed

Removed the direct proof-only imports
`Mathlib.Algebra.Homology.DerivedCategory.KInjective` and
`Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy` from the returned
version. Their arguments remain needed transitively through
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapComparison`; neither module is
claimed as pruned from the targets' closure. Replaced the direct proof-dependency
edges to `lem-weil-pbc-kinjective-hom-derived` and
`lem-weil-pbc-lift-to-injective-unique-up-to-homotopy` with
`lem-weil-pbc-module-cohomology-fmap-comparison`, whose proof includes them.
The original public import and the enough-injectives proof import remain needed.
No entire node or module is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The returned delivery and its prior second reading incorrectly treated private
helpers as unavailable for reuse and copied their proofs. Lean's module system
supports import all, making those helpers available inside this module without
changing their original visibility. Both duplicated declarations are now removed
and their existing proofs are used directly, as the return requests.
The previous second reading applied to the superseded delivery and has been
removed so that the new independent reader can review this repair.
The broader target-naturality theorem in ModuleCohomologyFMapFunctorial still
cannot be imported because it reaches this module; the comparison module does not.
No mathematical statement correction was needed.

## Second reading by G2

1. PASS — Compared the sole delivered Lean module against the repository with
   diff and separately checked the existing theorem signature byte for byte.
   The public import, theorem visibility, signature and docstring are unchanged.
   All additional declarations are private proof helpers; no existing definition
   or target statement changes, and no change record or forced adaptation is needed.
2. PASS — Independently compiled the delivered module with lcompile.py: exit 0,
   no warnings (15.3 seconds). Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_target_iso_naturality`:
   exactly propext, Classical.choice and Quot.sound; no sorryAx (14.9 seconds).
   Read every helper proof and the explicit resolution comparison isomorphism.
   No sorry, axiom, unsafe, opaque, extern, implemented_by or kernel-check bypass
   occurs. The final choices merely unfold the existing canonical map; its
   existence theorem is proved, and this delivery introduces no data chosen
   from an unproved mere-existence theorem.
3. PASS — No statements are split off, no holes are added, and no new nodes are
   introduced. The proved private lemmas are actual intermediate steps: the
   coefficient comparison homotopies, sections naturality, resolution transport
   and cancellation. Checked identity coefficient maps, zero coefficients,
   and degree zero against these equations; no positivity or nonzero assumption
   enters. The comparison works for arbitrary b, so specializing to e.hom needs
   no hidden invertibility assumption. Existing generic lift/uniqueness helpers
   are imported and used, with neither copied locally.
4. PASS — Repeated LeanFinder search with “derived cohomology coefficient
   morphism naturality injective resolution comparison”; its eight hits include
   isoRightDerivedObj_hom_naturality, already used by the proof, and no shorter
   scheme h-map theorem. Searched both library roots for target naturality and
   sections transports. The broader target theorem and data-target theorem
   both import this item through Functorial -> BasicProperties ->
   BasicPropertiesRestriction -> RestrictionNaturality, so neither is an
   admissible shorter route here. Comparison has no path back to this item.
   The remaining sections transport helper in Functorial also cannot be imported
   for the same reason. Each direct import serves the signature or proof.
   The No longer needed section names both removed old proof_deps and correctly
   distinguishes replacement direct edges from pruning whole modules. Read
   sk-thm-p1's realized statement and steps: this auxiliary node replaces none
   of them, and the unit record and route remain unchanged.
5. PASS — Compared the JSON files: only proof, proof_deps and proof_origin
   change. proof_deps is exactly the union of the proof steps' uses. The steps
   describe the actual coefficient descent, reuse of Comparison's private
   helpers, componentwise sections square, homology transport and cancellation.
   There are no new nodes requiring additional metadata.

Second reading changed only this report, adding the independent checks and
verdicts above. No Lean repair was needed. Net local holes: one closed
(moduleCohomologyFMap_target_iso_naturality), zero added, zero split off;
no whole module is claimed as pruned.
