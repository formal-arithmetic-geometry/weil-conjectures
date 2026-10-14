## What changed
Restored the two Lean modules and their DAG nodes from the full returned patch
in the assigned repair note. The supplied sandbox had only a report, and the
current checkout lacked the two modules. This repair uses the returned signatures
verbatim. The representatives theorem constructs scalar-to-ordinary module cycles,
proves their homology transport identities, and verifies the front/back cup
formula by coordinates. The assigned theorem combines these identities with the
existing cup-resolution representatives and the two refinement comparison squares.

Removed the redundant direct public import of
`Sheaf.Paper.ModuleCohomologyCupProduct` from the assigned module. Its public
interface remains available through the public bidegree import. Simplified the
last calculation: `ConcreteCategory.congr_hom` evaluates the two squares directly,
and `congrArg₂` substitutes their two equalities into the cup. Updated the DAG
proof description accordingly. No target or existing dependency signature changed.

## Proved and sorry left
The returned assigned hole is closed by
`AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalPairing`
(node `lem-sc-picard-module-cech-external-pairing`): 1 of 1 assigned holes closed.
The restored helper
`AlgebraicGeometry.Scheme.Modules.picardExternalCech_moduleRepresentatives`
(node `lem-sc-picard-external-cech-module-representatives`) is also fully proved.
All private helpers are proved. No sorry remains in either delivered module;
no new holes are added or split off. These proofs use existing project theorems,
including `cechCup_resolution_representatives`, that remain stage-3 items.
Relative to the current checkout the two modules are restorations, so this is
not a claim that the current import-closure ledger has decreased by one.

## No longer needed
Removed the redundant direct import
`Sheaf.Paper.ModuleCohomologyCupProduct` from the assigned module; the module
remains transitively imported and no transitive module is claimed pruned.
No proof-dependency node is removed: the representatives, cup-resolution
representatives, comparison naturality and refinement squares are all used.
No new scalar Ext cup or total-complex comparison theorem is needed.

## Where the brief, the DAG or earlier work was wrong
The sandbox did not contain the delivered Lean/node files as the repair brief
said. Recovered them from the exact patch preserved in the dedicated repair note.
The earlier report incorrectly treated their absence as an unrecoverable blocker.

The returned errors report an anonymous local instance name shared by
ModuleCupKInjectiveTarget and GlobalTensorPullbackMonoidalNormalization.
The current ModuleCupKInjectiveTarget already uses explicit moduleCupTarget names.
Both restored files compile together without that collision. Consequently the
reported self-importer and representatives-consumer failures do not require
signature or importer changes. The restored main module is compiled against the
restored representatives module in the same sandbox, checking that consumer.
No existing repository module imports either restored module.

## New nodes
`lem-sc-picard-external-cech-module-representatives` is restored from the returned
patch. It concerns only Cech cycles and their homology transports, and is proved
without a derived-cohomology comparison or a covering hypothesis.
`lem-sc-picard-module-cech-external-pairing` is the restored assigned statement;
its proof route uses that representatives theorem and the existing comparison
squares. Both nodes are absent from the current checkout and included whole.
Change record: `coord/changes/picard-module-cech-external-pairing-restore.md`.

## Second reading by K4

1. I compared both delivered Lean modules with the returned repair patch and the repository baseline. The public theorem signatures are byte-for-byte unchanged; the repository had no copies of these restored modules. Verdict: pass.

2. I compiled both modules together with `lcompile.py --all`. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. The proof uses only existing open theorems as imports and introduces no hollow definition. Verdict: pass.

3. The two new node statements match their Lean declarations and are strict reductions: the representatives theorem isolates cycle transport and the coordinate identity, while the pairing theorem combines it with the existing comparison results. Their docstrings describe the constructions and edge cases. Verdict: pass.

4. The representatives proof follows the additive Cech transport route. The pairing proof preserves the unit route through representatives, comparison naturality, resolution representatives, and refinement squares. The direct public `ModuleCohomologyCupProduct` import is redundant and was removed; all proof-only imports are private. Verdict: pass.

5. The DAG nodes record the declarations, proof dependencies, and proof origins used by the Lean proofs. The unit route is unchanged; no old dependency is pruned except the redundant direct import. Verdict: pass.

I changed only the final report section; the restored proofs and nodes required no repair after compilation.
