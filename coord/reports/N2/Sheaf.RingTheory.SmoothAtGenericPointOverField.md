## What changed
Implemented the smoothness theorem by identifying the localization at the zero prime with the fraction field and applying `regularLocal_iff_smoothAtPrime`. Added the intermediate separability transfer theorem.

## Proved and sorry left
`Algebra.smoothAtPrime_bot_of_isSeparable_fractionRing` is proved. `Algebra.separableExtension_bot_residueField` remains sorry as a strictly lower intermediate statement.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The DAG omitted the required explicit transport of separability from `L` to the generic residue field.

## New nodes
`lem-weil-pbc-smooth-at-generic-point-over-field-residue-separable`.

## Second reading by N2

1. I compared the delivered module with the repository version. Existing theorem signatures are unchanged; the only added declaration is the explicitly split intermediate separability theorem.
2. I compiled the module with `lcompile.py`; it succeeds with no errors. The smoothness theorem has no `sorry`; the sole remaining `sorry` is the named split theorem, and no forbidden declarations or hollow definitions were introduced.
3. The split theorem is true by the canonical fraction-field/residue-field isomorphism and is strictly lower than the target. Its node now records the full hypotheses, proof route, dependencies, and declaration metadata. The target statement is unchanged.
4. The proof uses the regular-local smoothness criterion and the separability transfer theorem. All imports are used; no old proof dependency can be removed. The unit route through regular-local smoothness is preserved.
5. The DAG and Lean agree on declarations and proof dependencies. No existing library theorem duplicates the split declaration.

Changed the split theorem docstring and node to give a complete proof description and self-contained statement, and recorded this second reading.
