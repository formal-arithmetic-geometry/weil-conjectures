## What changed

Proved `RingTheory.dvr_normalized_tensor_factor_lift` in
`lean/Sheaf/RingTheory/DvrNormalizedTensorFactorLift.lean`, preserving its complete
statement and all existing public imports. Added proof-only imports of
`Mathlib.RingTheory.TensorProduct.Nontrivial`,
`Mathlib.RingTheory.Flat.TorsionFree`, `Mathlib.RingTheory.Ideal.GoingUp`, and
`Sheaf.RingTheory.DvrRootTensorFactorIntegralClosureFinite`.

Choose a maximal quotient G of the nonzero ring F tensor_A A₁. Its right map
is injective by integral incomparability. Two tensor inductions prove that
E tensor_B A₁ surjects onto G. The quotient-kernel equivalence therefore gives
the required P₁ and compatible field embedding F -> F₁. The existing, proved
normalization-finiteness theorem supplies finiteness of S₁. Restrict the field
embedding to integral closures, apply lying over, identify the contraction in
the local integral extension A₁/A, and prove flatness using torsion freedom
over the Dedekind domain S.

Updated the original node's proof, proof_deps, and proof_origin to record this
route. The dependency is now
`lem-sbc-dvr-root-tensor-factor-integral-closure-finite`; its own proof already
uses the original Tag 032L dependency. No definitions, signatures, or other
modules were changed. The elaboration heartbeat option is scoped to this
large proof; the 60-second compiler limit is unchanged. Unused-variable linting is scoped off to preserve the original unused `hQ`
binder inside the statement verbatim.

## Proved and sorry left

Closed the only original hole:
`RingTheory.dvr_normalized_tensor_factor_lift`
(node `lem-sbc-dvr-normalized-tensor-factor-lift`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module,
and no intermediate statements were split off. The imported tensor-factor
normalization-finiteness theorem already has a complete Lean proof.

Validation uses the required single-file `lcompile.py` and the delivery dry
run, including its axiom probe. No global build or push is performed by this
worker.

## No longer needed

No original imports were removed and no named modules or DAG nodes are
pruned. The finite product decomposition, normalization of that product, and
selection of a prime in one of its factors are unnecessary: a single maximal
quotient of F tensor_A A₁ suffices, and its normalization is integral over S,
so every Q lifts to this same normalization. There were no separate named
nodes for those discarded constructions. The original direct dependency
`lem-weil-pbc-noetherian-normal-separable-integral-closure-finite` remains
needed transitively through the tensor-factor finiteness theorem.

## Where the brief, the DAG or earlier work was wrong

No false statement or broken interface was found. The DAG planned a larger
product construction than necessary. Its route is replaced only below the
unit level; no unit statement or realized unit step is bypassed. The unit
record `sk-prop-input-spreading` has no realized nodes for this auxiliary
argument. The source theorem's unused internal `hQ` binder generated a lint
warning once its proof was completed; the statement is retained verbatim.

## Second reading by R4

1. **Statements and interfaces.** Compared the delivered module with the
   repository version. The theorem signature and existing declarations are
   unchanged; only proof-only imports, options, and the proof body changed.
   The node statement agrees with the Lean statement.
2. **Proof and axioms.** `lcompile.py` compiles the module cleanly. There is no
   `sorry`, axiom, unsafe construct, or hollow definition in the delivery; the
   delivery probe checks the permitted axiom set.
3. **Split statements.** No statements were split off and no new nodes were
   introduced. The proof uses existing tensor, lying-over, flatness, and
   normalization-finiteness results.
4. **Pruning and route.** The direct maximal quotient route is shorter than the
   old product route and preserves the unit route. The node dependency records
   the normalization-finiteness theorem actually used.
5. **DAG consistency.** The node proof steps, dependencies, and origin match the
   Lean proof. No target or definition changed.

The second reading found no defects. This section is the only change made during
the reading.
