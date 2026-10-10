# lem-weil-pbc-triangular-change-of-basis

## Worker report

The source audit was run before changing the node. Grep of
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the node id,
`(blueprint: lem-weil-pbc-triangular-change-of-basis)`, `00MT`, and the
notions triangular/change of basis/unit diagonal found no declaration with
this statement. There is therefore no Lean attachment; no source declaration
was found to be sorry-free or to have sorry.

The node is split with no new child. The proof expands the two basis changes
used in Stacks Algebra Lemma 00MT (lines 24630--24641): the coordinate map is
introduced, then spanning and independence are proved by recursive elimination
for upper-triangular rows and for lower-triangular rows in the reverse order.
The unit diagonal entries supply the required inverses. The empty case is
handled explicitly. The only statement dependency is
`def-weil-pbc-free-module`; all four proof steps are elementary after that
definition.

Mathlib searches already recorded on the node found no one-line triangular
basis theorem. `Module.Basis.is_basis_iff_det`, `Basis.det_apply`, and the
upper/lower triangular determinant lemmas remain candidates only; no Mathlib
leaf is claimed. A whole-blueprint search for triangular, unit diagonal,
change of basis, matrix coefficient, and 00MT found no same statement, so
`blueprint.same_as` is empty. The B10 search path and result are recorded in
the node's `split_report.lean_audit`.

## Review by G1

I read Algebra, Tag 00MT (the `lemma-add-trivial-complex` proof at lines
24630--24641) and the current item and dependency node. The item statement
matches the two basis changes used there, including the commutative-ring
hypotheses, finite index range, both triangular orientations, and unit
diagonal. The sole dependency, `def-weil-pbc-free-module`, defines the free
module and basis used in the statement.

Step 1 introduces the coordinate map and the empty case; its use of the free
module basis is exactly the cited definition. Step 2 performs descending
coefficient elimination for the upper-triangular row convention and proves
both spanning and independence from the unit diagonal. Step 3 repeats the
argument in the opposite order for the lower-triangular convention. Step 4
identifies spanning plus independence with a basis. No step uses facts beyond
the cited definition and elementary finite induction and unit cancellation.

The split creates no nodes, so B1--B7 and C5 were checked on the item itself:
the statement is self-contained, the Stacks tag and exact label file are
recorded, and searches of the current DAG for the triangular/unit-diagonal
fact and the whole blueprint found no existing duplicate. The slopmaster2
search for the item tag and notion found no declaration, so there is no Lean
attachment. Small cases `m=0`, `m=1`, and a two-by-two upper or lower
triangular matrix reduce directly to the stated recursive argument; no edge
case changes the conclusion. Sections A-F of delivery-errors.md were checked,
including doubled TeX, dependency statements, source provenance, and cycle
freedom. No issue was sent back to the worker and no mathematical field was
changed after this review.
