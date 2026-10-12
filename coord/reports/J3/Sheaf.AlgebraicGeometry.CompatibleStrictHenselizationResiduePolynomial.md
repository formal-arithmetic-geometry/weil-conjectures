## What changed

Added the proved minimal-polynomial lemma in `CompatibleStrictHenselizationResiduePolynomialCore` and used it in the target module. Isolated the geometric residue-field separability step in `CompatibleStrictHenselizationResidueSeparability`, whose proof remains a named `sorry`.

## Proved and sorry left

`exists_separable_polynomial_of_isSeparable` is proved. The target theorem `Etale.compatibleStrictHenselization_residue_separable_polynomial` is proved from it and the new separability theorem. The only remaining sorry is `Etale.compatibleStrictHenselization_residue_isSeparable`, node `lem-weil-pbc-compatible-strict-henselization-residue-separability`.

## No longer needed

No stated imports were removed; both strict-henselization triple imports remain required by the separability split.

## Where the brief, the DAG or earlier work was wrong

The original plan combined geometric residue separability and the minimal-polynomial construction in one theorem. The latter is an independent Mathlib argument and was split out; no statement was weakened.

## New nodes

`lem-weil-pbc-compatible-strict-henselization-residue-polynomial-core` records the proved minimal-polynomial construction. `lem-weil-pbc-compatible-strict-henselization-residue-separability` records the remaining geometric step.

## Second reading by J3

1. **Interface comparison.** Compared the delivered target module with the repository version. The target theorem signature is byte-for-byte unchanged; the only changes are proof imports and proof terms. The two new modules contain the split-off declarations recorded by their new nodes.
2. **Compilation and axioms.** Compiled all three sandbox modules with `lcompile.py --all`; they compile successfully. The only remaining `sorry` is the named geometric separability theorem in `CompatibleStrictHenselizationResidueSeparability`, and it is recorded by node `lem-weil-pbc-compatible-strict-henselization-residue-separability`. No definitions contain `sorry`, and no forbidden declarations were added. The minimal-polynomial theorem uses only the permitted algebraic proof route.
3. **Statements and nodes.** Checked both new statements against their Lean declarations and source. `exists_separable_polynomial_of_isSeparable` is the standard minimal-polynomial consequence and is strictly simpler than the target. The separability split is exactly the remaining geometric residue-field step and is needed by the target proof; its node, docstring, source, and `lean` record agree with the module.
4. **Proof route and pruning.** The target now applies the minimal-polynomial theorem to the separability split. The strict-henselization and étale-local-ring-triple imports remain required by the split theorem. The core import was narrowed from `Mathlib` to `Mathlib.FieldTheory.Separable`; no stated proof dependency was removed.
5. **Unit route.** The target remains in unit `sk-thm-p1`, and the proof still uses the geometric separability step before constructing the polynomial, so the unit route and realized nodes are preserved.

I changed the core module to use the narrower `Mathlib.FieldTheory.Separable` import and added this second-reading record. No target statement or definition was changed.
