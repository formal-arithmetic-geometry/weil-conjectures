## What changed

Added two proof modules splitting the original comparison into underlying equivalence data and its naturality identities. The target module now combines these named results; all three modules compile.

## Proved and sorry left

The target declaration `exists_resolutionSection_homology_comparison` is proved from the two strictly smaller intermediate declarations. The new declarations `exists_resolutionSection_homology_data` and `resolutionSection_homology_naturality` remain sorry-backed nodes, covering respectively construction of the four equivalences and verification of the six compatibility families.

## No longer needed

No imports or planned nodes were pruned. The local copy of `EtaleResolutionSectionTransfer` was only used to repair the missing compiled snapshot and is not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was blocked by a missing compiled object for `EtaleResolutionSectionTransfer`; compiling that dependency in the sandbox resolves the tool failure. The full naturality argument is substantially larger than the target glue, so it was split into two proper intermediate statements.

## New nodes

`lem-weil-pbc-etale-resolution-section-homology-data` and `lem-weil-pbc-etale-resolution-section-homology-naturality` record the two intermediate statements and their source plan.

## Second reading by A3

1. **Statements and signatures.** Compared the target module byte for byte with the repository version before the proof body; the target signature is unchanged. The two added theorem signatures are explicit strict substatements of the target.
2. **Compilation and axioms.** Compiled all three delivered modules with lcompile; all compile cleanly. The target has no sorry, while the two named split theorems are the only remaining sorry-backed declarations.
3. **New statements.** Checked the data and naturality statements against the source and existing declarations; neither duplicates an existing library theorem. Their nodes and Lean declarations agree.
4. **Pruning and dependencies.** The target imports the two proof-only modules; no prior public import was removed and no unused planned dependency was identified. The unit route is retained through the target node.
5. **Edge cases and route.** The split statements preserve arbitrary schemes, opens, degrees, and the augmentation hypothesis, including empty opens; the target is exactly their conjunction and makes no weaker claim.

Changed the target proof to apply the two named intermediate results, added their DAG nodes, and recorded the updated proof dependencies.
