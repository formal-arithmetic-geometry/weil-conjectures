## What changed

Proved `PadicAlgCl.finiteSubextensions_directed` in
`Sheaf.Paper.FiniteSubextensionsDirected`, preserving its signature, imports and docstrings.
The proof follows the existing node's four steps: finite-supremum finiteness and inclusion,
induction on `Fin n` for the product degree bound using
`IntermediateField.finrank_sup_le`, binary suprema for directedness, and the actual
`IntermediateField.adjoin` of a finite subset for containment. Singleton containment gives
the final assertion. No definition, consumer, node or public interface changes.

Searched with the required msearch wrapper (LeanFinder for finite-compositum degree bounds,
Loogle for `IntermediateField.finrank_sup_le`, and grep for compositum finiteness and finite
adjunction), and searched both project roots. Mathlib provides all field-theoretic
components of the existing plan; no unfinished project theorem is needed.

## Proved and sorry left

Closed one original hole: `PadicAlgCl.finiteSubextensions_directed`
(node `det-def-sfb-qlbar-condensed-subextensions`). Proved all five conjuncts.
Added zero holes; zero sorries remain. Zero statements split off.

The induction treats `n = 0` explicitly: the empty supremum is bottom, of degree one,
and the empty product is one. The finite-adjunction argument includes the empty subset.
Witnesses are explicit intermediate fields paired with proved finiteness, rather than
arbitrary data chosen from an unproved existence theorem.

## No longer needed

None. Both existing imports remain; the proof uses the existing node's declared
dependencies on algebraic closure and finite algebraic adjunction through their Mathlib
APIs. The current DAG already records the direct binary degree bound and finite-subset
adjunction used here. No module or node is withdrawn, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The current node records that an earlier V8 proof was lost
when this module was withdrawn and later restored with a hole. This delivery proves the
restored statement along its already recorded proof plan.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
