## What changed

Shortened determinant_split_comparison_restriction to rewrite both occurrences using hd and apply hn. Its statement is unchanged. Replaced the direct Invertible and ShortComplex.Basic imports with TensorSection; ExteriorSheaf is retained. The import change is recorded in coord/changes/determinant-split-local-imports.md.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction` is
proved. No `sorry` remains in the module, and no new holes were added.

## No longer needed

The direct imports WeilConjectures.AlgebraicGeometry.Modules.Invertible and Mathlib.Algebra.Homology.ShortComplex.Basic are no longer needed. The proposed LocallyFree, ShortExact, and BinaryBiproducts imports are also unnecessary and have been removed.

## Where the brief, the DAG or earlier work was wrong

The theorem was already proved; this delivery simplifies its proof and changes its import header without closing any holes.

## Earlier second reading (a previous round; superseded)

A second reader should verify the unchanged restriction theorem and the previously
landed retirement of the duplicate local declaration. The proof compiles and its
statement matches node `new-determinant-split-restriction` exactly.

The import adaptation is recorded in
`coord/changes/determinant-split-local-imports.md`.

## Earlier second reading (a previous round; superseded)

1. **Signatures and accidental changes.** Compared the delivered module with
   the repository version. The theorem statement is byte-for-byte unchanged;
   only the proof and imports differ. No definition or target statement was
   changed.
2. **Compilation and axioms.** Compiled the sandbox module and the repository
   module with `lcompile.py`. Both compile cleanly. The theorem's axioms are
   exactly `propext`, `Classical.choice`, and `Quot.sound`; there are no
   `sorry`s, forbidden declarations, or hollow definitions.
3. **Statements and nodes.** The restriction theorem matches node
   `new-determinant-split-restriction` exactly. Its proof is the direct
   substitution of `hd` into `hn`, so it is true and has no extra hypotheses.
   No new statements or nodes were introduced.
4. **Route and pruning.** The proof uses only `hd` and `hn`, as recorded by the
   node. The existing unit route is preserved. The retained ExteriorSheaf and TensorSection imports suffice. Removing LocallyFree, ShortExact, and BinaryBiproducts together preserves clean compilation of this module and its direct importer Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison.
5. **Earlier work.** The earlier duplicate local construction was already
   retired and its import adaptation is documented in the change records. No
   further repair was necessary.

Changed by this reading: this report section only.

## Second reading by G1

1. **Signatures and accidental changes.** Compared the sandbox module with the repository version. The theorem signature is byte-for-byte unchanged; only its proof and imports differ. No target, definition, or existing declaration statement changed.
2. **Compilation and axioms.** Compiled the delivered module with `lcompile.py`; it compiles cleanly with no warnings or `sorry`. The proof is a direct rewrite by `hd` followed by `hn`, and introduces no forbidden declarations or hollow definitions.
3. **Statements and nodes.** The declaration matches node `new-determinant-split-restriction` exactly. Its hypotheses and conclusion are unchanged, and the node records the proof with no proof dependencies. No new statements or nodes were added.
4. **Route and pruning.** The proof uses only the stated pointwise equality and naturality hypothesis, which is the shortest route and preserves the unit route. `TensorSection` is required for the tensor notation and monoidal instance; `ExteriorSheaf` supplies the sheaf definitions. The old direct imports are unnecessary.
5. **DAG and earlier work.** The node proof text agrees with the Lean proof, and the existing import and retirement change records explain the prior adaptation. No further repair was needed.

Changed by this reading: appended this second-reading verification only.
