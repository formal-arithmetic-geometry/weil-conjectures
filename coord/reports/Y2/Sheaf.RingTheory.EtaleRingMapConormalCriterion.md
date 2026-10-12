## What changed

Proved `Algebra.etale_ring_map_conormal_criterion` in
`Sheaf.RingTheory.EtaleRingMapConormalCriterion`, with its signature unchanged.
Constructed the conormal differential using Mathlib's `kerCotangentToTensor`,
extended its scalars along the surjective presentation, and composed it with
the scalar-extended polynomial differential basis. Proved the coordinate formula.
Used Mathlib's conormal injectivity criterion and exact conormal sequence to
identify injectivity with vanishing H1 and surjectivity with vanishing differentials.
The supplied finite presentation and affine etale comparison finish the argument.
Updated the node's proof, proof dependencies and proof origin to match this route.

Added proof-only imports `Mathlib.RingTheory.Kaehler.Polynomial` and
`Mathlib.LinearAlgebra.TensorProduct.Basis`. The public imports are unchanged.
The local compiler succeeds without warnings. No new declarations or statements.
The proof works for n = 0 and zero rings: the finite-index function equivalence,
exact sequence, and subsingleton arguments impose no nontriviality assumptions.

## Proved and sorry left

Closed: `Algebra.etale_ring_map_conormal_criterion`
(node `lem-weil-pbc-etale-ring-map-conormal-criterion`).
Holes closed: 1. Holes added: 0. No sorry remains in the delivered module.
No split-off theorem and no decomposition.

## No longer needed

Removed import `Sheaf.RingTheory.JacobiZariskiQuotientSmooth` and the proof dependency
`lem-weil-pbc-jacobi-zariski-quotient-smooth` (`Algebra.jacobiZariski_quotient_smooth`).
The proof uses only Mathlib, so no project Jacobi-Zariski homology sequence,
left-term vanishing, or further dependencies reached solely through the removed
import are needed by this item. Their global reachability remains for the maintainer
to compute. All other original proof-dependency nodes remain relevant through
Mathlib definitions, the polynomial instance/basis, and the affine comparison.
No unit statement or realized step is bypassed: this item is below the realized
statements and steps of `sk-thm-p1`.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The old DAG route through the project's
Jacobi-Zariski quotient theorem is unnecessary: Mathlib already proves the
needed kernel criterion and cokernel exactness. The original docstring describes
that mathematical route; the updated node records the actual Mathlib proof.
Searches used the supplied leanfinder and loogle wrappers and local rg on Mathlib
and both library roots. No direct one-lemma criterion was found; the existing
Mathlib pieces combine to a complete proof.

## Second reading by Y2

1. **Visible declarations and statements.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports and the theorem proof differ. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it compiles without errors or warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. `#print axioms Algebra.etale_ring_map_conormal_criterion` reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. **Statements and split-offs.** No statement was split off and no new declaration was added. The existing target theorem is proved with its original hypotheses and conclusion; edge cases including `n = 0` and zero rings are covered by the finite-index and subsingleton arguments. Verdict: pass.
4. **Route and pruning.** The proof uses Mathlib's conormal kernel/exactness APIs and the polynomial Kähler basis, while retaining the unit-level polynomial basis, H1 vanishing, affine étale comparison, and definition dependencies. The obsolete Jacobi–Zariski quotient import and node are removed from the proof dependencies. Verdict: pass.
5. **DAG agreement.** The delivered node's proof steps, dependencies, and proof origin match the Lean proof, and the unit's realized route is retained. Verdict: pass.

I changed nothing after this reading; the delivered proof and DAG metadata are internally consistent.
