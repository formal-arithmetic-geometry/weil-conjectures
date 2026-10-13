## What changed

The target theorem now has a complete categorical calculation from a new algebraic factorization theorem. Added the proof-only import `Sheaf.Algebra.Homology.UniversalH0SplitFactorization`. The factorization theorem isolates the local matrix and projective-cokernel argument as one named stage-3 hole.

## Proved and sorry left

Closed `CochainComplex.universalH0_split_differential` by composing the two split maps and verifying `d ≫ s ≫ d = d` with associativity. Added one named sorry, `CochainComplex.universalH0_split_factorization`, in the new module and node `new-universal-h0-split-factorization`; it is the strictly smaller factorization output of the local algebra argument.

## No longer needed

No imports or existing nodes were removed. The three original proof dependencies remain relevant to the factorization argument.

## Where the brief, the DAG or earlier work was wrong

The DAG's local matrix and projectivity argument had no Lean interface. It is now isolated as factorization data, while the generalized-inverse calculation is fully proved. No target statement or existing interface was changed.

## New nodes

`new-universal-h0-split-factorization` is stated in `lean/Sheaf/Algebra/Homology/UniversalH0SplitFactorization.lean` and records the local splitting output described above.

## Second reading by G2

1. Compared `UniversalH0SplitDifferential.lean` with the repository version. The theorem signature is byte-for-byte unchanged; the only interface addition is the declared proof-only import and the separate split-off theorem recorded by the new node.

2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds with no warnings after removing an unused simp argument. The only remaining `sorry` is the named theorem `CochainComplex.universalH0_split_factorization`, which has a matching node and is not inside a definition. The generalized-inverse theorem uses only the permitted categorical calculation over that split-off result.

3. Checked the factorization statement against the hypotheses and the required calculation. It is a strictly smaller intermediate existence statement (factorization and two retractions), with its source and proof outline documented in the module and node; no duplicate declaration was found in the repository or Mathlib.

4. The proof follows the factorization route and retains all imports needed by the theorem statements. The new factorization module carries the original algebraic imports; the differential module imports it plainly because it is proof-only. No old proof dependency can be removed without bypassing the unit route.

5. The node and Lean declarations agree on names, hypotheses, conclusion, source, and proof dependency. The unit route remains represented by `lem-sc-universal-h0-split-differential`; the new node records the strictly lower local factorization step.

Changed in this second reading: removed the unused `Category.comp_id` simp argument in the categorical calculation and added this review record.
