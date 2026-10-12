## What changed

Proved `AlgebraicGeometry.smallEtaleRepresentablePresheaf_isSheaf` with its original signature. Replaced the proof-only import `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale` by `Mathlib.AlgebraicGeometry.Sites.Proetale`. Updated the existing node's proof, proof dependencies and proof origin to the compiling route.

Mathlib makes the étale topology subcanonical by its inclusion in the subcanonical pro-étale topology (whose instance comes from fpqc subcanonicity). `subcanonical_over` gives the sheaf of morphisms over `T`, including the structure-map check by uniqueness. The inclusion of the small étale site preserves finite limits and covers, so its continuity restricts this sheaf to the required presheaf. The last line applies the sheaf condition to the given covering presieve. There are no hypotheses on `X` beyond being over `T`; no finiteness or nonemptiness assumptions on a cover were introduced.

## Proved and sorry left

Proved `AlgebraicGeometry.smallEtaleRepresentablePresheaf_isSheaf` (node `lem-weil-pbc-small-etale-representable-presheaf-sheaf`), the only original sorry. No sorry remains in the delivery, and none was split off. Local `lcompile.py` compilation succeeds without warnings. The required dry run additionally checks the axioms and server compilation.

## No longer needed

Removed import `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`; the proof no longer needs node `lem-weil-pbc-fpqc-finer-than-etale` or its module. Mathlib's proved topology comparison supplies the covering comparison instead. No other project module is needed by this proof. Node `lem-weil-pbc-fpqc-representable-descent` is retained as the substantive Mathlib descent leaf used through subcanonicity; it has no project module to import. The statement and steps recorded in `dag/units/sk-thm-p1.json` are not bypassed: this representability node occurs only below those unit realizations.

## Where the brief, the DAG or earlier work was wrong

The original mathematics is correct. The prior Mathlib searches missed the short categorical route through `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Mathlib.CategoryTheory.Sites.SubcanonicalOver`, and continuous restriction. In particular, no new intermediate statements and no unproved project covering-comparison lemma are necessary. The existing docstring describes the underlying descent/structure-map argument; Mathlib's `subcanonical_over` implements that argument.

## Second reading by G2

1. The theorem signature is byte-for-byte unchanged from the repository; the proof introduces no hypotheses or weakened conclusions. Verdict: pass.
2. The module compiles locally with no warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses only Mathlib declarations; its axioms are therefore within the permitted foundation. Verdict: pass.
3. No statement was split off and no new node was added. The retained proof dependency is the existing fpqc representable-descent leaf, while the categorical route is supplied by Mathlib. Verdict: pass.
4. The shorter Mathlib route through pro-étale subcanonicity and continuous restriction is valid; the removed project import was unnecessary. The unit route is retained because this node remains the representability/sheaf step. Verdict: pass.
5. The DAG proof text, `proof_deps`, and `proof_origin` match the implemented route; the removed finer-than-étale node is absent from the proof dependencies. Verdict: pass.

Changed only the proof import and proof body, updated the existing node's proof metadata, and added this second-reading record.
