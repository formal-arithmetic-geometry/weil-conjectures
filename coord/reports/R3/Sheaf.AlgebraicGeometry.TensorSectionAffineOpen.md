## What changed

Proved `AlgebraicGeometry.Scheme.Modules.tensor_section_affine_open` in
`Sheaf.AlgebraicGeometry.TensorSectionAffineOpen`, without changing its signature,
visibility, definitions, or the unit route. Six proved private helpers establish the
residue-value criterion, nonzero pure tensors, the binary locus equality, invertibility
of the initial tensor family, the finite-family locus equality, and affine finite
intersections. The affine proof starts at the given affine factor and applies
`affine_cap_section_open` once per factor by finite-set induction.

Added proof-only imports `Mathlib.LinearAlgebra.TensorProduct.Quotient` and
`Mathlib.RingTheory.Flat.Basic`. Updated the existing node's proof, proof_deps, and
proof_origin to record the actual proof. All public imports are preserved.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.Modules.tensor_section_affine_open`
(node `lem-sc-tensor-section-affine-open`). No holes were added or split off, and no
sorry remains in the delivered module. This is a proof from the existing tensor-fibre
and affine-intersection declarations, not a decomposition into new statements.

The compiler accepts the complete module without warnings. The one-factor case is
explicitly covered by the induction base; zero factors give empty tensor loci by the
binary tensor criterion; the empty scheme requires no inhabited-point assumption.
The private pure-tensor helper works for arbitrary vector spaces, including zero ones.

## No longer needed

Removed proof-only import `Sheaf.Paper.NonvanishingSectionTrivializes` and proof dependency
`lem-weil-pbc-nonvanishing-section-trivializes`: the quotient-tensor equivalence proves
the residue-value criterion directly. This module and node are unnecessary for this
item's proof; other users may still need them. No other original imports or proof
nodes were removed. A trial direct import of
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula` was also removed:
tensor invertibility is obtained from the already used `invertible_pullback_tensor`.
No downstream subgraph is claimed globally pruned beyond this removed dependency edge.

## Where the brief, the DAG or earlier work was wrong

The original route unnecessarily uses the trivialization theorem for the elementary
fibre/nonvanishing criterion and rank-one bases for nonzero pure tensors. The direct
Mathlib quotient comparison and linear independence suffice. The second reader updated the theorem docstring to describe the refined route,
matching the delivered DAG and proof.
No statement was found false, and no interface adaptation is needed.


## Second reading by R3

1. **Unchanged interface: pass.** Compared the sole delivered module with the
   repository version using `diff` and the declaration parser. The existing theorem
   signature and visibility are byte-for-byte unchanged; no definitions changed.
   Only proved private helpers, proof bodies, proof-only imports and documentation
   differ. No change record or forced adaptation is needed.
2. **Proof verification: pass.** Local compilation succeeds without warnings.
   There is no `sorry`, forbidden axiom command, unsafe declaration, opaque
   declaration or external implementation in the module. A scratch copy printed
   axioms for all six helpers and the public theorem. The first two helpers use
   only `propext`, `Classical.choice` and `Quot.sound`; the others additionally
   use `sorryAx` through existing imported open statements. The public theorem
   therefore closes its local hole, but is not yet independent of all upstream
   holes. No new data construction or arbitrary existential witness is introduced.
3. **Split-off statements: pass, none.** All six helpers are proved; no new public
   statement, node or hole was added. Checked the quotient kernel calculation and
   the pure-tensor criterion, including zero vector spaces and zero sections.
   The one-factor base case and empty scheme require no extra hypothesis.
   Independent searches of both library roots and Mathlib, and a Loogle query
   `TensorProduct.tmul, _ ≠ 0`, found no direct replacement for the item. The
   upstream `IsLocalRing.one_tmul_eq_zero_iff` repeats the small quotient
   calculation but lives in the much broader projective-dimension module; keeping
   the direct Mathlib quotient proof avoids that unnecessary dependency.
4. **Top-down route and pruning: pass.** The proof uses the existing tensor-fibre
   comparison, finite-family induction and affine-intersection theorem. All six
   imports are needed for the signatures or proof; both added Mathlib imports
   remain proof-only. The only removed old dependency is
   `lem-weil-pbc-nonvanishing-section-trivializes`, fully listed above. The
   `sk-thm-curveestimate` unit record realizes `thm-sc-proper-cohomology`, with no
   separate realized steps; this auxiliary node's elementary fibre calculation
   does not bypass any unit statement or realized step.
5. **DAG agreement: pass.** Only the existing node's `proof`, `proof_deps` and
   `proof_origin` changed. Its step dependency union equals `proof_deps`, and
   the steps match the actual Lean reductions. No new nodes need validation.

**Second-reader change:** corrected the public theorem's proof docstring, which
still described choosing rank-one bases and applying the now-pruned
trivialization theorem. It now describes the quotient-tensor kernel and singleton
linear-independence argument actually used. No proof or signature repair was
needed. One original hole closed; zero holes added or split off.
