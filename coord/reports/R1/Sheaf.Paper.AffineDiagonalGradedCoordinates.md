## What changed

Replaced the proof hole of
`AlgebraicGeometry.PurityNormalBundle.affineDiagonalGradedCoordinates_isIso`
by a reduction to local regularity of the specified coordinate differences.
The public signature and the exact homogeneous representatives, difference sign,
coordinate order, cone and counit remain unchanged.

The original module now proves the affine polynomial-evaluation criterion,
the comparison with the actual associated-graded affine chart, compatibility
of homogeneous classes and cone functions with restriction, transport through
the counit and the open-section isomorphisms, and the affine-cover gluing
argument. It uses the existing proved
`Ideal.regularSequence_gradedPolynomial`; it does not introduce a second
graded-polynomial theorem. Proof imports are
`Sheaf.RingTheory.RegularSequenceGradedPolynomial` and the new geometry module below.

The remaining elementary-coordinate geometry is isolated in
`Sheaf.AlgebraicGeometry.AffineDiagonalRegularDifferences`:
`AlgebraicGeometry.affineDiagonal_regular_differences`. It asserts local
regular generators for the original diagonal only. It mentions neither the
normal cone nor its coordinate map, and is strictly a part of the original
argument, rather than its conclusion repackaged.

Validation: the new geometry module compiled in 6.1 seconds, with only its
expected named theorem hole. The original module compiled cleanly in 18.0
seconds through lcompile.py after all proof edits and import cleanup. The
original theorem signature was compared verbatim and is unchanged. The
import-direction checks permit the proof dependencies, and both DAG dependency
lists equal the union of the dependencies cited by their proof steps.

Both DAG records describe this actual argument. No existing statements,
definitions, source-library modules or consumers were changed.

## Proved and sorry left

Closed: the one original hole in
`AlgebraicGeometry.PurityNormalBundle.affineDiagonalGradedCoordinates_isIso`
(node `lem-pur-affine-diagonal-graded-coordinates`), conditional on the named
local geometry theorem.

Added: one hole in
`AlgebraicGeometry.affineDiagonal_regular_differences`
(node `lem-pur-affine-diagonal-regular-differences`). Its complete polynomial
substitution proof is in its docstring and DAG record. This is a decomposition:
one original hole closed, one strictly smaller hole added; net zero holes.
There are no holes in definitions or private helpers, and no other holes are
added by this delivery.

Edge cases: the original theorem assumes neither positive dimension nor a
nonempty base. The new statement is pointwise in z. Its affine neighborhood
contains the diagonal point, ensuring the final polynomial quotient is
nonzero and therefore that Mathlib's `IsRegular` condition holds. For d=0
it gives the empty sequence and zero ideal on a nonempty chart. For empty Y
there are no points z, so it is vacuous. No regular sequence over a zero ring
is claimed.

## No longer needed

No original import was removed. The redundant direct proof import
`Mathlib.Algebra.MvPolynomial.Equiv` was removed: it is publicly imported by
`Mathlib.RingTheory.MvPolynomial.Homogeneous`, itself publicly imported by the
regular-sequence theorem module. All six original dependency nodes remain
used, either directly or through the local geometry lemma. The original
module still needs `AffineTraceTower` and `ReesConeNormalization` for its
statement. No node or module is withdrawn or pruned.

The direct monomial-basis argument in original steps 2 and 4 is replaced by
the existing regular-sequence graded-polynomial theorem. A separate
localization-of-monomial-bases lemma is unnecessary: naturality of the actual
homogeneous representatives and counit, followed by Zariski-locality of
isomorphisms, suffices. No extended-Rees comparison or integration theorem is
imported for the proof. `normalConeChartRingIso` concerns the extended-Rees
cone and is not the displayed intrinsic relative-Spec map.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the entire coordinate calculation as
"elementary" while providing only definition interfaces. Those interfaces
supply the affine graded chart but do not already state the regularity and
ideal-generation facts for the ordered differences on the global tower.
The proof now uses the available graded-polynomial theorem and isolates only
that missing local geometric assertion. The unit route through the standard
diagonal and its ordered difference coordinates is preserved.

The blueprint ancestor helper printed `blueprint.from.node = None` for the
item, although its actual JSON explicitly points to
`lem-pur-projection-purity-agreement`. The new node uses that explicit
ancestor and records both intervening nodes in `via`.

## New nodes

`lem-pur-affine-diagonal-regular-differences`, module
`Sheaf.AlgebraicGeometry.AffineDiagonalRegularDifferences`, states that every
point of the tower has an ambient affine neighborhood on which the restricted
ordered differences are a regular sequence generating the diagonal kernel.
The substitution u=y−x identifies the map with polynomial evaluation at zero;
coefficient comparison proves regularity, and the specified point ensures
properness of the ideal. The source is the blueprint's standard-pair
translation calculation, expanded in the original item's first proof step.
Searches used LeanSearch, LeanFinder, Loogle, Mathlib grep, and blueprint/source searches;
none supplied the same global ordered-neighborhood statement. No change
record is needed because no existing interface was changed.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
