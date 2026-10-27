## What changed

Completed `AlgebraicGeometry.Scheme.Hom.genus_baseChange_of_isAlgClosed` in
`Sheaf.AlgebraicGeometry.CurveGenus`. Apply `genus_jacobian_invariant (K := K) f`,
eliminate its three existential witnesses, and retain the genus equality from its
conjunction. The fields, structure morphism, hypotheses and pullback agree exactly.
The theorem signature, definitions and imports are unchanged. This implements the
existing proof step of `sk-def-curve`; no node update is necessary.

Search: LeanFinder for genus invariance under algebraically closed extension returned
elliptic-curve and proper-scheme results, with no arbitrary-curve genus theorem.
Repository search found the already imported `genus_jacobian_invariant`, which supplies
exactly the required equality. The more specialized `genus_baseChangeField` requires
smooth relative dimension one and would need additional glue. The planned extraction
is already a two-line proof.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Hom.genus_baseChange_of_isAlgClosed` (`sk-def-curve`).
Added 0 holes; split off 0 statements. No sorry remains in the item module.

## No longer needed

None. No import, node or module was removed. The proof uses the planned
`lem-sc-genus-invariant` and the genus definition `def-sc-genus`. Discarding the
Jacobian conclusions requires no new Jacobian argument or imports.

## Where the brief, the DAG or earlier work was wrong

No defect affecting this proof. The current blueprint's genus-invariance lemma has
been generalized, but the recorded Lean declaration still contains precisely the
equality needed here under the item's existing hypotheses. The existing unit route
is preserved. No definitions, statements, consumers or upstream modules were changed.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
