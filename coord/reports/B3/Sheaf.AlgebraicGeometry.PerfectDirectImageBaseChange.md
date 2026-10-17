## What changed

The earlier B3 duplicate retirement landed during the initial read of this task. This delivery
completes its pruning: remove the unused proof-only import of
Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange from its last two importers,
PicardSingleRankPerfectChart and SmoothCurveEtaleStructureDirectImages, then withdraw the
item with deleted.txt under brief step 8d. The tool will retain its empty module file.
All declarations, proof bodies, public imports and signatures of both consumers are unchanged.
The existing node lem-pc-rf-perfect-base-change retains its statement and source attachment;
its metadata no longer claims the withdrawn shim publicly re-exports the source theorem.

Change record: coord/changes/PerfectDirectImageBaseChange-final-withdrawal.md.

## Proved and sorry left

Item: 0 holes before, 0 after. Holes closed: 0 of 0. Holes added: 0. Split off: 0.
This is duplicate-module retirement and pruning, not a new theorem proof.
PicardSingleRankPerfectChart stays locally sorry-free. The only existing sorry in the
adapted modules remains AlgebraicGeometry.Etale.smooth_curve_etale_structure_direct_images
(node lem-weil-pbc-smooth-curve-etale-structure-direct-images), whose signature, docstring
and proof are untouched. No imported open result is claimed proved.

Both adapted modules compiled without warnings or errors through lcompile.py --all:
PicardSingleRankPerfectChart in 6.7 seconds, SmoothCurveEtaleStructureDirectImages in
5.8 seconds. Every consumer declaration and proof is byte-for-byte unchanged after stripping
the one removed import line. Final delivery validation is the required deliver3.py dry run.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange. Both direct imports
are removed. No library module now imports the withdrawn item. Independent second-reading
import-graph analysis finds that this item is already outside the current TargetsCheck closure,
so this delivery claims zero modules pruned from that closure and zero holes reduced. Its four public imports
(DerivedModuleBaseChangeMap, PerfectComplex, DirectImage.Basic and DirectImage.PerfectBaseChange)
are no longer pulled through this compatibility module. Each underlying module still has
other users, so no whole-library pruning or hole reduction is claimed for those modules.
The node lem-pc-rf-perfect-base-change remains attached to the source-library theorem;
it is neither deleted nor claimed mathematically unnecessary.

## Where the brief, the DAG or earlier work was wrong

The assignment was issued just as the earlier duplicate retirement landed. Resubmitting
that already landed code would be a no-op. Source inspection instead found two remaining
unused library imports of the declaration-free shim. The original report incorrectly said
these kept it in the targets' import closure: the current TargetsCheck already does not reach
the item or its two consumers. Withdrawal applies after removing those last library imports;
this cleanup has no target-closure progress claim. The source theorem's affine Cech interface
remains distinct from the removed combined derived theorem, as the earlier repair documented;
this delivery asserts no bridge between them and does not change the unit route.

## Second reading by B3

1. **Interfaces and accidental edits: PASS.** Read the retired item and both complete
   consumers, and diffed each delivered consumer against the shared repository. Each diff
   deletes exactly `import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`, a private
   proof import. Removing that line from the repository copies makes them byte-for-byte
   equal to the sandbox copies. All existing signatures, visibility, definitions, proofs,
   docstrings and public imports are identical. The retired item contains no declarations;
   deleted.txt requests only its withdrawal. The change record quotes its old module and
   records the replacement empty module and the two direct users.
2. **Compilation, holes and axioms: PASS for pruning.** Independently ran lcompile.py --all:
   both consumers compiled without diagnostics. Scratch copies outside the delivered lean/
   tree compiled with `#print axioms` for all eight declarations, including the two private
   Picard helpers. The six helpers/definitions use only propext, Classical.choice and
   Quot.sound. `AlgebraicGeometry.Scheme.exists_picardSingleRankPerfectChart` also uses
   sorryAx through unchanged imported open results; it has no local sorry.
   `AlgebraicGeometry.Etale.smooth_curve_etale_structure_direct_images` is the single
   unchanged local sorry, and its axioms are those same four. The attached source theorem
   `AlgebraicGeometry.Scheme.Modules.perfect_and_baseChange_cechModuleComplex_of_isProper`
   was checked separately and uses only the three permitted axioms. No forbidden
   declaration forms, hollow definitions or arbitrary witnesses from unproved existence
   theorems were added. This delivery closes zero holes and adds zero holes.
3. **Split statements and duplication: PASS, none introduced.** There are no new modules,
   statements, definitions or split-off theorems. The item has already lost its duplicate
   theorem in the earlier landed retirement. Its source theorem is retained directly at
   the existing WeilConjectures module. No new Mathlib search or small-case test is needed
   for this purely import-level withdrawal.
4. **Shortest route, pruning and unit: PASS with an existing metadata limitation.** A search
   of the full library finds exactly the two removed import lines as module dependencies;
   neither consumer invokes a declaration from the retired module. The Picard proof obtains
   its complex from exists_properFlatDirectImagePerfectChart; the smooth-curve module
   already directly imports the source PerfectBaseChange module. Thus no theorem application
   is replaced or bypassed. The four compatibility public imports leave with the item, but
   their modules still have independent users, as the report states. Reconstructed the import
   graph and verified the change record contains exactly all 29 transitive users. The item
   and its two consumers are already outside the current TargetsCheck closure: zero modules
   leave that closure. Corrected the report's claim that these imports prevented target-closure
   pruning. No proof_deps entry is newly discarded, and no node is claimed pruned. Read the unit record
   sk-thm-picard-semicon: its realized.statement and sole realized.steps entry are already
   empty. This delivery leaves that existing realization gap unchanged; it changes no unit
   statement, step, route or attachment. Pre-existing prose in consumer docstrings still
   names the retired combined theorem; those unchanged proof plans are not new proofs or
   claimed bridges from the source Cech statement.
5. **DAG and Lean correspondence: PASS for this change.** The full node diff changes only
   the first proof step's re-export description, proof_origin.note and lean.note. Its
   mathematical statement, statement dependencies, source, proof dependencies and source
   declaration attachment are unchanged. The new wording correctly describes an empty,
   unimported compatibility module and preserves the explicit warning that the source
   Cech formulation is not identified with the retired derived comparison theorem. No new
   node is required; the five proof dependencies describe the earlier caller reductions,
   which this delivery does not alter or claim to prove.

Second reading changed the report only: corrected the target-closure pruning claim and added
this independent review with explicit axiom, remaining-hole and unit-realization findings.
No Lean or DAG repair was needed.

Validation: deliver3.py --no-push passed compilation and preflight at dry-run commit
9bdf048ddf. The tool classifies the set CODEX because it includes node metadata, a change
record, the two import-only consumer adaptations and withdrawal of public re-exports.
