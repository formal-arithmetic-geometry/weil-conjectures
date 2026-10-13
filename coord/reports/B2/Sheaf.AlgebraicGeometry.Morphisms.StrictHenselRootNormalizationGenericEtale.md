## What changed

Added the finite-fibre source-neighbourhood reduction theorem
`GaloisCover.root_normalization_generic_source_etale` as a separate intermediate
statement, and proved the item's target theorem by combining it with the proved
strict-henselization regularity and flatness lemmas and the finite-fibre shrinking
argument. The delivered item imports the intermediate module.

## Proved and sorry left

The target declaration `GaloisCover.strict_hensel_root_normalization_generic_etale`
is proved. The strictly smaller intermediate declaration
`GaloisCover.root_normalization_generic_source_etale` remains `sorry`; its node is
`lem-sbc-root-normalization-generic-source-etale`.

## No longer needed

No imports or DAG dependencies were removed. The generic source-neighbourhood
statement isolates the Abhyankar calculation needed by the target.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan implicitly treated the Abhyankar ramification calculation as
available, but no Lean declaration states it. It is therefore split into the
strictly smaller source-neighbourhood theorem above.

## New nodes

`lem-sbc-root-normalization-generic-source-etale` is stated in
`lean/Sheaf/AlgebraicGeometry/Morphisms/RootNormalizationGenericSourceEtale.lean`.

## Earlier second reading (a previous round; superseded)

The item and new node signatures were checked against the DAG. The item proof uses the source-neighbourhood node as a strictly smaller Abhyankar step and preserves the unit route.

## Second reading by B2

1. **Interface and accidental changes.** Compared the delivered item with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and its proof-only import of `RootNormalizationGenericSourceEtale` were added. The new module has a standalone theorem with the statement recorded in its node.

2. **Compilation and proof integrity.** Compiled both modules with `lcompile.py --all`; both pass without errors or warnings. The target proof contains no `sorry`, axiom, unsafe, opaque, extern, implemented_by, or hollow definition. The only remaining `sorry` is the named split-off theorem `GaloisCover.root_normalization_generic_source_etale`, documented above and represented by node `lem-sbc-root-normalization-generic-source-etale`.

3. **Truth and strength of statements.** The target statement is unchanged. The split-off theorem is a strictly smaller source-neighbourhood conclusion: it retains the original construction and hypotheses needed for the Abhyankar step, and adds the pointwise fibre conclusion required by the target. It does not assert a target open or global etaleness. Its edge cases (empty fibres and group order one) are vacuous or unramified as documented in its docstring.

4. **Shortest route and pruning.** The target uses the proved strict-hensel divisor regularity and structural flatness results, derives the root regular-local hypothesis, applies the split-off source theorem, and then uses finite-source Zariski locality to obtain the target open. The unit route through generic source etaleness is preserved. No existing import or dependency became unused.

5. **DAG and unit agreement.** The new node records its source, proof steps, dependencies, declaration, and split status. The existing target node is updated so its proof and `proof_deps` include the new node and the actual strict-hensel intermediate lemmas. The unit `sk-prop-input-spreading` remains realized through the target route.

Changed files: added `lean/Sheaf/AlgebraicGeometry/Morphisms/RootNormalizationGenericSourceEtale.lean`, completed the target proof in `lean/Sheaf/AlgebraicGeometry/Morphisms/StrictHenselRootNormalizationGenericEtale.lean`, added its node, and updated the target node's proof metadata.
