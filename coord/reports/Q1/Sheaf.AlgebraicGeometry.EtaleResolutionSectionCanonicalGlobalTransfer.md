## What changed

The target theorem `resolutionSection_canonical_transfer_global` is now proved by reducing its universal quantification to the pointwise theorem `resolutionSection_canonical_transfer_global_pointwise`. The latter is stated in a new module and records the unresolved cocycle and Ext comparison argument as one named theorem with `sorry`. The target gained a proof-only import of that module.

## Proved and sorry left

`AlgebraicGeometry.Etale.resolutionSection_canonical_transfer_global` is proved by introducing `q` and `x` and applying the pointwise theorem. The new declaration `AlgebraicGeometry.Etale.resolutionSection_canonical_transfer_global_pointwise` remains `sorry`, recorded by node `lem-weil-pbc-etale-resolution-section-global-transfer-pointwise`.

## No longer needed

None. The canonical comparison and transfer dependencies remain needed by the new pointwise statement and its proof plan.

## Where the brief, the DAG or earlier work was wrong

The DAG describes a long cocycle calculation but does not expose its pointwise component as a Lean statement. The missing intermediate statement was added explicitly; the parent theorem is a genuine quantifier-level composition of it.

## New nodes

`lem-weil-pbc-etale-resolution-section-global-transfer-pointwise`: pointwise global canonical transfer identity, with the same hypotheses as the target and fixed degree and homology class. Its module is `lean/Sheaf/AlgebraicGeometry/EtaleResolutionSectionCanonicalGlobalTransferPointwise.lean`.

## Second reading by Q1

1. **Diff and statements.** Compared the delivered target module with the repository version. The
   theorem signature is byte-for-byte unchanged; only its proof body and a proof-only import were
   added. The new pointwise declaration has the target's hypotheses unchanged and specializes only
   the final universal quantifiers.

2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py --all`; both compile
   without errors. The target theorem is proved by the pointwise theorem. The pointwise theorem is
   the sole remaining `sorry`, and is explicitly documented with its source and proof plan. No
   definitions, axioms, unsafe declarations, or forbidden implementation features were added.

3. **New statement.** The pointwise statement is mathematically true and exactly the instance needed
   by the parent theorem, but it is a quantifier-level decomposition with the same hypotheses and
   conclusion. This is recorded as a review risk because the stage-3 brief warns against split-offs
   that merely rename the item; no weaker or stronger target statement was introduced.

4. **DAG and imports.** The new node records the pointwise declaration, its source, proof plan,
   dependencies, and Lean location. The node's proof dependencies match the imports and the
   unresolved cocycle calculation. No existing imports were removable: the canonical comparison
   definitions are needed by the pointwise statement and its proof plan.

5. **Unit route.** The target remains the realized node for the global-transfer unit, and the
   pointwise theorem is only an intermediate component. The route through canonical comparison and
   explicit section transfer is preserved.

Changed only the report by adding this second-reading record; no Lean statements or definitions were
altered during review.
