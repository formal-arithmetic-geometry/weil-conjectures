## What changed

Added the proof-only import `SquareZeroRelativeSectionKernelIdeal` and proved
`squareZeroRelativeSectionKernel` by identifying the two sections with elements
of the restriction kernel ideal and applying its square-zero product bound.
Added the intermediate module and node
`lem-sc-square-zero-relative-section-kernel-ideal`, whose proof remains a named
`sorry` for the affine-local algebraic geometry argument.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.squareZeroRelativeSectionKernel`.
The new theorem `AlgebraicGeometry.Scheme.relativeSectionKernel_ker_mul_le_bot`
remains `sorry` (node `lem-sc-square-zero-relative-section-kernel-ideal`).

## No longer needed

None beyond the original imports; the stated `Gm` and `IdealSheaf.Subscheme`
imports remain needed by the declarations.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted the intermediate kernel-ideal statement required to
separate the affine-local geometric argument from the elementary ring argument.

## New nodes

`lem-sc-square-zero-relative-section-kernel-ideal` is the square-zero kernel
ideal statement used by the completed theorem.

## Earlier second reading (a previous round; superseded)

Pending independent second reading of the target and the new intermediate node.

## Second reading by N1

1. **Statements and interfaces.** Compared the delivered target module with the repository version. The declaration of `squareZeroRelativeSectionKernel` is byte-for-byte unchanged; the added `relativeSectionKernel_ker_mul_le_bot` is a separate intermediate statement with the same kernel and hypotheses used by the proof.

2. **Proof and axioms.** Compiled both sandbox modules with `lcompile.py --all`; they compile without errors or warnings. The target proof reduces the section hypotheses to kernel membership, applies `Ideal.mul_le` to the split-off square-zero kernel theorem, and concludes from membership in `⊥`. The only remaining `sorry` is the named geometric theorem `relativeSectionKernel_ker_mul_le_bot`; no definition contains `sorry`, and no forbidden declarations occur. Since that theorem is still open, the target's transitive axioms may include `sorryAx` until it is proved.

3. **Split statement and node.** Checked that the new theorem is true and exactly the intermediate square-zero kernel-ideal assertion needed by the elementary ring argument, rather than a restatement of the target. Its docstring gives the affine-local source and proof plan, and node `lem-sc-square-zero-relative-section-kernel-ideal` records the matching statement, source, proof dependency, and Lean declaration.

4. **Pruning and imports.** The proof uses the existing public imports for the scheme, ideal-sheaf, and etale structure declarations, plus the proof-only import of `SquareZeroRelativeSectionKernelIdeal`. No imported module or DAG dependency is unused, so no pruning is reported.

5. **DAG and unit route.** The target node's proof and `proof_deps` now follow the Lean proof through the new kernel-ideal node. The route remains below the `sk-prop-h2` unit boundary: the unit statement and route are untouched, and the new node isolates the affine-local geometric step rather than bypassing the unit.

**Changes made.** Added this second-reading record only; no source or node repairs were needed after compilation and comparison.
