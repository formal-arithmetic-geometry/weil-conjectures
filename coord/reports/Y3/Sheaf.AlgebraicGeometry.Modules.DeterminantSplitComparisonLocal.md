## What changed

The restriction theorem uses the repaired interface with a natural linear family
`dNatural` and pointwise equality `hd`; the unconstrained tuple family `c` from the
reviewed statement is absent. Its proof substitutes `hd` on both sides and applies
the naturality hypothesis `hn`.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction` is fully
proved. No `sorry` remains and no new holes were added.

## No longer needed

No imports, declarations, or DAG proof dependencies were pruned: `TensorSection` must
remain public because its monoidal instance is part of elaborating the visible tensor
types in this theorem's statement.

## Where the brief, the DAG or earlier work was wrong

The original statement was false because `c` was unconstrained and could vary under
restriction. The current statement repairs this by requiring a natural linear family
and equality with the linear equivalences pointwise. The local comparison theorem
already supplies this naturality conjunct through the repaired restriction theorem.

## New nodes

None.

## Second reading by Y3

1. **Repository comparison.** The theorem signature is byte-for-byte unchanged from the
repository version. The only source changes are the proof term and removal of an unused
public import; no target or existing declaration was weakened or otherwise altered.

2. **Proof and axioms.** The module compiles with the prescribed launcher, contains no
`sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and the axiom probe
reports only `propext`, `Classical.choice`, and `Quot.sound`. The `simpa only [hd]`
proof substitutes the pointwise equality on both sides and applies `hn` exactly.

3. **Statements and split nodes.** The restriction statement is true by direct
substitution and is exactly the corrected naturality interface. The local-comparison
node is already redirected to the canonical `determinant_split_comparison_exists`
theorem; this delivery adds no statements or holes.

4. **Pruning and route.** The proof uses no additional declarations or imports beyond
`ExteriorSheaf` and public `TensorSection`; both are required to elaborate the visible
tensor types. The unit route and existing DAG proof dependencies remain intact.

5. **DAG consistency.** The restriction node records an elementary proof with no proof
dependencies, matching the source. The local node records its canonical theorem
redirection and remains unchanged.

Changed in this second reading: no source change was needed beyond the worker's proof;
the attempted import narrowing was rejected by Lean because downstream elaboration needs
the public monoidal instance.
