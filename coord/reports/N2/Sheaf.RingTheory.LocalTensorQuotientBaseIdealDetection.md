## What changed

Proved `AdicCompletion.local_tensor_quotient_base_ideal_detection` by applying the
injective component map, distributing it over the finite sum, and using the pure-tensor
formula together with `Ideal.Quotient.eq_zero_iff_mem`. Added the intermediate module
`Sheaf.RingTheory.LocalTensorQuotientComponentMap` for the Artinian product decomposition;
its theorem remains a named `sorry` because that decomposition is not available in the
imported API.

## Proved and sorry left

The target declaration `AdicCompletion.local_tensor_quotient_base_ideal_detection` is
proved. The added declaration `AdicCompletion.tensor_quotient_component_map` remains a
`sorry`, with node `lem-weil-pbc-local-tensor-quotient-component-map`.

## No longer needed

None. The target proof uses all of its existing public imports and the new component-map
module.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt omitted the exact recorded signature for the new node and did not
record all three required Mathlib searches. The product-decomposition argument itself is
correctly isolated as the strictly simpler component-map statement.

## Earlier second reading (a previous round; superseded)

A second reading should check that the target proof uses the component-map injectivity,
linearity, and pure-tensor formula without changing the target statement, and that the
new component-map statement is exactly the Artinian product-decomposition step required
by the unit route. No unit-level route is bypassed.

## New nodes

`lem-weil-pbc-local-tensor-quotient-component-map`: the injective component map for the
quotient tensor product, stated in `lean/Sheaf/RingTheory/LocalTensorQuotientComponentMap.lean`.

## Second reading by N2

1. **Visible changes and signatures.** Compared the delivered target module with the repository version. The target declaration's signature is byte-for-byte unchanged; the only target-file changes are the proof and its proof-only import. The additional component-map module and node are explicitly recorded in this delivery.

2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py --all`; both compile cleanly. The target proof has no `sorry`, while the component-map theorem is the sole named split-off `sorry` and its node is present. The component-map theorem is the only source of `sorryAx` in the target's proof closure.

3. **Statements and searches.** Checked the component-map statement against the quotient-product argument in Stacks Tag 07N9 and tested the edge cases `n > 0`, empty finite sums, and an empty prime-over set in the stated construction. It is a strictly simpler intermediate assertion: injectivity plus the pure-tensor component formula, exactly what the target proof applies. Searches recorded in the component-map node found only partial Mathlib ingredients and no existing theorem with this statement.

4. **Route and pruning.** The target proof follows the unit route through the component-map decomposition, then uses linearity and `Ideal.Quotient.eq_zero_iff_mem`; no unit step is bypassed. The prior imports remain needed for the target statement and proof. The component-map module's direct `Ideal.Quotient.Operations` import was tested as unnecessary and removed; its quotient notation and operations are available through the remaining imports.

5. **DAG agreement.** The target node's proof and `proof_deps` now name only `lem-weil-pbc-local-tensor-quotient-component-map`, matching the actual proof. The new component-map node records its exact Lean declaration, source, proof origin, searches, and split status. The unit realization is unchanged.

**Changes made during second reading.** Removed the unused public `Mathlib.RingTheory.Ideal.Quotient.Operations` import from `LocalTensorQuotientComponentMap.lean`; added this review section. No theorem statements or definitions were changed.
