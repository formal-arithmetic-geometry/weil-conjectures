## What changed

Replaced the sole hole in `lean/Sheaf/RingTheory/TorIdealHomologyExactness.lean`,
`ModuleCat.tor_ideal_homology_exactness`, by a direct cycle proof.
The statement and its existing docstring are unchanged.

Added proof imports of `Sheaf.RingTheory.TorIdealCycleLift` and Mathlib's
`LinearAlgebra.TensorProduct.RightExactness`, `LinearAlgebra.TensorProduct.Finiteness`,
`Algebra.Homology.ShortComplex.ModuleCat`, and `Algebra.Homology.ConcreteCategory`.
The cycle-lift theorem already has a complete proof. The remaining argument uses
Mathlib's resolution exactness in degrees zero and one, tensor right exactness,
and homology's cycle inclusion and projection. Multiplication on ideal tensors
is constructed from the ideal inclusion and the tensor unit isomorphism.
All witnesses are used in proofs; no data is chosen from an unproved existence theorem.

Updated the existing DAG node's `proof`, `proof_deps`, and `proof_origin` to match
this proof. No new declarations, modules, nodes, or interface changes.
The unit's realized statements and steps are unaffected.

## Proved and sorry left

Closed: `ModuleCat.tor_ideal_homology_exactness`
(node `lem-weil-pbc-tor-ideal-homology-exactness`).
One original hole closed; zero holes added or split off; no holes remain in the module.
The proof proves injectivity by reducing a killed class to a boundary and proves
both inclusions of `LinearMap.range δH = LinearMap.ker μR`.

The construction works with the zero ideal, the unit ideal, the zero module,
and empty finite sums. It requires no nonzero-ring or finite-generation hypothesis.
The supplied free-term hypothesis `hP` is retained but mathematically unnecessary
for exactness of a map already satisfying the specified cycle formula.

## No longer needed

Pruned proof dependencies of this node:

- `lem-weil-pbc-flat-tensor-exact`
  (`Module.Flat.rTensor_exact`, `Module.Flat.lTensor_exact`).
- `lem-weil-pbc-free-module-projective` (`Module.Projective.of_free`).
- `lem-weil-pbc-projective-module-flat` (`Module.Flat.of_projective`).

These nodes are Mathlib leaves, so this removes no Sheaf module from the existing
import closure. They can still be needed by other nodes. The proof needs only
tensor right exactness, not tensor preservation of injections or general exact pairs.
No original import was removed: all original imports are public and the signature
and exposed interface are preserved. No unused added proof import remains.

## Where the brief, the DAG or earlier work was wrong

The original step 3 lists flat tensor exactness and conversions from free to
projective to flat, but its boundary-subtraction argument only needs tensor right
exactness of the augmented resolution. No injectivity of `I ⊗ P₀ → P₀` is used.
The already proved `ModuleCat.exists_quotient_cycle_lift` supplies step 1.

The cited Stacks source file is not present in this read-only clone. The cited
results were checked at [Tag 00M5](https://stacks.math.columbia.edu/tag/00M5) and
[Tag 00M6](https://stacks.math.columbia.edu/tag/00M6). The proof follows the existing
node's explicit cycle argument, expanding its elementary algebra in Lean.

## Second reading by A3

1. **Interface and statements.** Compared the delivered module with the repository version byte for byte at every existing declaration. The theorem signature and exposed imports are unchanged; the added imports are proof-only. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds with no warnings or errors. The theorem body contains no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declarations, and no definition contains a hole. A scratch copy with `#print axioms ModuleCat.tor_ideal_homology_exactness` reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Verdict: pass.

3. **Split-off statements and search.** No statements were split off and no new nodes were added. The existing theorem is proved directly using the cycle-lift declaration and Mathlib tensor right exactness; an independent repository search for the cycle-lift and ideal-kernel formula and Loogle search `Function.Exact, TensorProduct` found the exactness ingredients already used, but no shorter theorem proving the specified cycle map. Zero and unit ideals, zero modules, and empty sums introduce no extra assumptions. Verdict: pass.

4. **Pruning and route.** The direct proof uses only right exactness, resolution exactness, and the existing quotient-cycle lift. The old flatness, free-to-projective, and projective-to-flat dependencies are unused and are removed from the node proof route; the unit route remains represented. Verdict: pass.

5. **DAG agreement.** Updated proof steps, proof dependencies, and proof origin match the Lean proof. The theorem closes the sole original hole, adds none, and preserves the stated source and unit. Verdict: pass.

Changed during second reading: no Lean statements or proofs; added this review record only.
