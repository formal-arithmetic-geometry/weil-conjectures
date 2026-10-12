## What changed

Added a proof-only import of `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber` and proved `AlgebraicGeometry.finite_pushforward_set_stalk_fiber_finite` by applying the existing `Scheme.Hom.GeometricFiber.finite` instance. The subtype in the target is definitionally the existing `GeometricFiber` abbreviation.

## Proved and sorry left

The declaration `finite_pushforward_set_stalk_fiber_finite` is proved. No sorries were added or left in the delivered module.

## No longer needed

The prior planned dependency `lem-weil-pbc-sets-finite-pushforward-set-stalk` is not needed for this direct proof.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan described a geometric argument to be isolated later, but the source library already contains and proves the exact finite geometric-fibre instance. The route was shortened to that existing declaration.

## Second reading by Q3

1. **Statements and accidental changes.** Compared the delivered module with the repository version. The theorem signature and docstring are unchanged; only a proof-only import and the proof body were added. The accompanying node updates only its proof route and proof dependencies.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it is warning-free and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. `#print axioms AlgebraicGeometry.finite_pushforward_set_stalk_fiber_finite` reports only `propext`, `Classical.choice`, and `Quot.sound`.
3. **New or split statements.** No new Lean statements were introduced. The existing split node is proved directly by `Scheme.Hom.GeometricFiber.finite`; its subtype is definitionally the geometric-fibre type, so the statement is true with exactly the declared hypotheses and conclusion. The existing Mathlib and library search record found no duplicate theorem.
4. **Pruning and route.** The proof uses the existing finite geometric-fibre instance, so the prior parent-node dependency is unnecessary and is removed from `proof_deps`; the proof-only geometric-fibre import is retained. The unit route and its realized declarations are unchanged.
5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` now match the Lean proof, and the theorem statement remains byte-for-byte equivalent after JSON decoding.

Changed only the module proof/import, the corresponding node proof metadata, and this second-reading report. No definitions, target statements, or additional holes were added.
