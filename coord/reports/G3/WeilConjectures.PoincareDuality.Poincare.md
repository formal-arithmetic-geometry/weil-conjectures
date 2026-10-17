## What changed

Marked the unrestricted upstream `boundedConstructible_tateTwistDerived` as
STATEMENT-DISPUTED, following the counterexample already independently accepted in
`nt-target-poincare-tate-bc`. Its signature and its original sorry remain unchanged.
Removed the previous sandbox's false unrestricted module-constructibility split.
The source file uses local irreducibility and local instance-priority commands,
explicit arguments in the trace-cup proof, and a proved private helper for the
composition-of-isomorphisms argument. These retain every existing public signature.

Proved `AlgebraicGeometry.ProEtale.boundedConstructible_shift_single` in
`Sheaf.PoincareDuality.ConstructibleShiftSingle` and
`AlgebraicGeometry.ProEtale.zeroTwist_constructible` in
`Sheaf.PoincareDuality.TateTwistLocalLine`. The source module combines them in the private
`boundedConstructible_zeroTateTwistDerived`: the zero-twist case, for every scheme and
integer shift, is fully proved. The helpers introduce no sorry or arbitrary choice of data.

## Proved and sorry left

Original holes closed: zero of one. Holes added: zero. The original
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived` remains
sorry and disputed; the attached upstream target is `nt-target-poincare-tate-bc`.
The retained split's `AlgebraicGeometry.ProEtale.tateTwist_constructible` is not delivered:
its unrestricted statement is false. Its experimental source and metadata remain in
scratchpad, outside the delivery.

The generic shifted-single theorem, zero-twist constructibility theorem, and private
shifted zero-twist theorem are proved. These prove a special case, not closure of the
original hole and not a decomposition introducing lower holes.

## No longer needed

No existing library module, import or node is pruned. The never-landed false
`lem-poincare-tate-constructible` proposal is removed from the delivery. The geometric
rank-one proof is unnecessary for the zero-twist case. The generic shift calculation
uses no triangulated-subcategory closure theorem.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the source theorem quantifies over arbitrary schemes, whereas the
reviewed DAG theorem requires ell invertible. The section's field and characteristic
variables do not occur in this theorem's Lean type. The current node's reviewed
counterexample is X = Spec(Fbar_ell[direct_sum_i Q_ell/Z_ell]) with infinitely many
summands: compatible roots yield an infinite-rank Tate module. The retained split repeated
the same false unrestricted claim and its supposed proof silently used invertibility.
No false module theorem is imported, and no target signature is changed here.

The upstream-signature gate does not list this theorem or its wrapper among permitted
statement corrections. The corrected ell-invertible route therefore cannot replace this
source theorem in this delivery. Correcting the theorem also requires propagating the
hypothesis to `boundedConstructibleTateTwist` and deriving it from the base field for the
smooth-purity consumers. A source-only downstream audit found only `TargetsCheck` and
`WeilConjectures` as importers and no external declaration-level use of either wrapper.

Edge cases checked: zero twist on every scheme, arbitrary positive/negative/zero shift,
empty scheme, zero module, and generic noncommutative coefficient ring for the shift
calculation. No claim of rank-one triviality outside the ell-invertible domain is made.

## New nodes

`lem-poincare-constructible-shift-single` records the proved shifted-single calculation.
`lem-poincare-zero-twist-constructible` records the proved regular-module presentation
for the zero twist. Both are strictly valid pieces of the intended constructibility
argument and have zero holes. The local elaboration commands and their downstream audit
are recorded in `coord/changes/poincare-local-elaboration.md`; these attributes are local
and no existing public signature, definition body or public import changes.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
