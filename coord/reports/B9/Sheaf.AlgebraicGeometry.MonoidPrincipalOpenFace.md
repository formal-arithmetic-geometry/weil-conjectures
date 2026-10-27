## What changed

Filled `AlgebraicGeometry.FineFan.monoid_principalOpen_face` in
`Sheaf.AlgebraicGeometry.MonoidPrincipalOpenFace` without changing its signature,
`principalFace`, or any public import. Proved private helpers for the face calculations,
prime-ideal avoidance, the complementary greatest prime, downward closure of generated
opens, basic-open containment, and the explicit fraction inclusion. The last clauses
use `IsUnit.map` and equality of subtype representatives. Updated node
`lem-trf-monoid-principal-open-face` step 3 to match the generated-topology induction.

The proof follows ILO VIII 3.1.1–3.1.4, printed pp. 98–99 (PDF pp. 104–105),
read from the cited local PDF. Library grep found no existing matching principal-face
result. Logged LeanFinder found divisibility/prime-power results requiring additional
structures, and Loogle supplied the applicable `isUnit_iff_exists_inv` equivalence.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.FineFan.monoid_principalOpen_face`
(node `lem-trf-monoid-principal-open-face`). Added 0 holes and split off 0 statements.
There are no remaining `sorry` declarations in this delivery. All private helpers
have complete proofs.

## No longer needed

None. The sole public import `Sheaf.AlgebraicGeometry.FineFanBlowup` remains necessary
for the statements and definitions. The sole declared dependency
`def-trf-fine-fan-blowup` remains used; no node or module is pruned. No extra proof
imports were needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The generated topology makes downward closure under
prime-ideal inclusion directly inductive, so a separate proof that the basic opens
form a basis is unnecessary. The argument works for every commutative monoid;
the original fine-monoid hypothesis is retained unchanged.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
