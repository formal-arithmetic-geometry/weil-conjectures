## What changed

Reduction of `etaleAdditiveCech_normalized_inverseImage` to two new public
intermediate theorems, each in a separate module, with node records. The original
signature is unchanged. The proof chooses canonical resolution comparisons,
uses source normalization to identify the source global class, transports a
supplied augmentation equality, and uses target normalization to finish.
All work is in the sandbox. Nothing was pushed.

The shared library now contains the previously missing normalization object.
The candidate combination proof compiles against the shared library. A first
dry run exceeded the 60-second single-file limit during concurrent compilation;
the final dry run printed OK: all modules compile and preflight passes except
for the required second reading. Nothing was pushed. No unchanged dependency
source is included.

## Proved and sorry left

The combination proof is compiler-verified against the shared library. In it,
the original hole
`AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_normalized_inverseImage`
is replaced by a complete combination proof. Two new holes remain:

- `AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_cycle_realization`, node
  `lem-pbc-etale-additive-cech-cycle-realization`.
- `AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_augmentation_transfer`, node
  `lem-pbc-etale-additive-cech-augmentation-transfer`.

This is a decomposition (one upper hole into two lower holes), not net
proof progress. Neither helper mentions an edge equivalence or its normalization.
The first is single-scheme augmentation realization; the second transports an
already supplied equality and identifies its resolution-global class. Witnesses
are obtained only in a theorem proof, never used to define arbitrary data.

Edge cases were checked mathematically: degree zero uses gluing/restriction;
an empty covering implies an empty source scheme; empty intersections carry zero
sections; repeated opens leave the coface identities intact. The transport step
uses exact inverse image and a separate resolution, never assumes inverse image
preserves injectives, and needs no flatness of g.

## No longer needed

The original direct proof-only import of
`Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalTransfer` is removed from
the assigned module. It remains a planned dependency of the new transfer lemma,
so its node and module are NOT pruned from the overall closure. Canonical data,
normalization and TopologicalInvariance imports remain. No other planned node or
module is claimed pruned. No blueprint unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous missing normalization object is now present in the shared library.

The original plan names canonical comparison data and transfer, but neither
statement supplies coefficient beta cycles, quasi-isomorphism of the specified
alpha components, or transport of alpha/beta equality. The nearby theorem
`nonempty_etale_openCech_resolution_total_iso` asserts an unspecified homology
isomorphism, not that its map is the specified alpha. Its proof cannot be used as
an exported statement. The new realization plan instead cites injective row
augmentation and first-quadrant column augmentation, retaining the component
identifications as explicit work.

Actual searches: LeanFinder returned generic injective-resolution naturality
lemmas; Loogle returned homology projection/naturality APIs; Mathlib grep found
augmented nerves but no fixed additive normalization theorem. LeanSearch returned
Internal Server Error (recorded as unavailable). Blueprint searches for Cech
augmentation/refinement found no exact imported statement. Sources 01EQ, 01FD
and 03P2 were read from their Stacks pages.

## New nodes

`lem-pbc-etale-additive-cech-cycle-realization` records the coefficient cycle
realization step from the two augmentations of 01EQ. It does not require affine
acyclicity and makes no claim about an inverse-image map or an edge equivalence.

`lem-pbc-etale-additive-cech-augmentation-transfer` records the refinement
pentagon step of 01FD for already supplied matching augmentation classes and
canonical resolution comparisons. It does not construct or normalize an edge.

No statement/definition was changed, no other module adapted, and no change record
is needed. The two helper modules compile with their named theorem holes.

## Second reading by W2

1. **Visible declarations and statements.** Compared the delivered target module with the repository version. The theorem signature of `etaleAdditiveCech_normalized_inverseImage` is byte-for-byte unchanged; only its proof and proof-only imports differ. The two added helper modules contain new, explicitly named split statements and do not alter existing declarations.

2. **Compilation and proof hygiene.** Compiled all three sandbox modules with `lcompile.py`; compilation succeeded. The target proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The only remaining holes are the two named helper theorems, each documented and represented by a split DAG node. No definition contains `sorry`.

3. **Truth and strength of split statements.** The cycle-realization theorem supplies representatives for a given coefficient cycle through the alpha and beta augmentations and asserts equality of the resulting total homology classes. The augmentation-transfer theorem transports a supplied source augmentation equality to the target while retaining the coordinate hypothesis; neither introduces an edge equivalence, normalization, or arbitrary data definition. Both are strictly smaller than the target and match their node statements.

4. **Shortest route and pruning.** The target proof uses the existing canonical comparison data, the two necessary split lemmas, and the target normalization predicates. The former direct transfer import was removed from the target module because transfer is now isolated in the helper module, where that import remains required. No other planned dependency is pruned, and the unit route remains the augmented-resolution route recorded in `sk-thm-p1`.

5. **DAG and unit agreement.** Checked both new node records against their Lean declarations, including module names, theorem names, statements, proof dependencies, source, and `status: split`. The target node records the combination proof and its two helper dependencies. The unit's realized route is unchanged.

Changed only the target proof/imports, added the two documented helper modules and matching node records, and added this second-reading record.
