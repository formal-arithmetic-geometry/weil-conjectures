## What changed

Proved `exists_generic_product_map_denominators` in
`Sheaf.AlgebraicGeometry.GenericProductMapDenominators` without changing its statement.
Added proof-only imports `Mathlib.RingTheory.TensorProduct.Maps` and
`Mathlib.Algebra.Ring.Hom.InjSurj`. The tensor universal property constructs the map,
reducedness gives its quotient factorization, and double tensor induction shows that
its image spans the generic product. The proved private helper
`clear_denominator_of_span` clears denominators by span induction.
Updated the existing node's proof to describe this implementation. No unit route changes.

## Proved and sorry left

Closed the one existing hole: `exists_generic_product_map_denominators`
(node `lem-weil-pbc-generic-product-map-denominators`).
Added zero holes. No sorry remains in the item or is added elsewhere.
The private helper `clear_denominator_of_span` is fully proved.

## No longer needed

None: no imports, nodes, or modules removed. No Sheaf proof dependencies are needed.
The explicit tensor-associativity equivalence in the informal plan is unnecessary:
the tensor universal property and double tensor induction provide the same calculation.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The node had no named proof dependencies, but Mathlib's
standard constructions suffice. The proof handles zero vectors with denominator 1,
empty tensor sums with numerator 0, and r = 0 without any coordinate obligation.
The referenced literature markdown is absent on this machine; the existing node and
module docstring supply the complete argument used here. No new sourced claim is introduced.

## Second reading by M2

1. I compared the delivered Lean module and node with the repository versions. The theorem
signature and all existing declarations are unchanged; only the proof, proof-only imports,
and the node's proof metadata differ. Verdict: pass.

2. I compiled the module with `lcompile.py`; it compiles without errors or warnings. The
module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and
the denominator helper is a private fully proved theorem. Verdict: pass.

3. The existing theorem is proved directly by tensor-product maps, quotient factorization,
and span induction. No split-off statements or new nodes were added, and the argument does
not restate the target as an unproved theorem. Verdict: pass.

4. The route still realizes the unit's generic-product map step: the tensor construction,
reduced quotient, and denominator clearing are all explicit in the proof. The proof-only
imports are minimal for the declarations used. Verdict: pass.

5. The node's proof steps and `proof_origin` match the delivered implementation, and its
`proof_deps` remains empty. No unit `realized` route is changed. Verdict: pass.

I changed only this report section; no Lean declarations or node statements were changed.
