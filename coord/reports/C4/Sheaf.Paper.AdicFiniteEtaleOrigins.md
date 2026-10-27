## What changed

Completed the Lean assembly of
`AlgebraicGeometry.Scheme.adicFiniteEtale_origins`, keeping its signature and its
public import unchanged. Added only proof imports, proved private helpers, and the
new one-theorem module `Sheaf.Paper.AdicFiniteReductionConstructibility`.

The private comparison proof uses constant inverse-image scalar normalization to
identify the two ordinary pullbacks as left adjoints of the same module
pushforward. Uniqueness of derived functors then identifies the adic pullback with
the functor in the existing constructible comparison theorem. The main proof
transports residue constructibility, applies the new cohomological filtration
step, obtains cohomological bounds from the existing flat-model theorem, and uses
the inverse finite-Tor comparison equivalence and its counit to construct each
origin. Tor reflection preserves precisely the given interval.

Updated the item's DAG proof and dependency lists to this assembly. No existing
shared definition, statement, public import, instance, or source-tree file changed.
The unit route through the Stacks integral criterion is retained.

Both modules compiled through `lcompile.py --all`: 29.5 seconds for the new module
and 39.3 seconds for the item, with exit code zero. All delivered Lean lines fit
100 columns. Every added import is used by the proof or by the new statement.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.adicFiniteEtale_origins`
(node `lem-sfb-adic-finite-etale-origins`). Its proof contains no `sorry`.
The ordinary and derived pullback comparisons, Tor isomorphism invariance,
cohomological bounds from Tor amplitude, and bounded-constructibility isomorphism
transport are proved private helpers.

Added one hole:
`AlgebraicGeometry.Scheme.adicFiniteReduction_constructible_cohomology`
(node `lem-sfb-adic-finite-reduction-constructibility`), in the new module
`Sheaf.Paper.AdicFiniteReductionConstructibility`. Its entire proof is `by sorry`.
There are no other holes in this packet. The count is one original hole closed
and one new hole added: this is a decomposition, not a net hole reduction or an
axiom-free proof of the entire dependency closure.

The new statement is strictly the coefficient-filtration constructibility step:
it has no Tor hypothesis or conclusion, no etale object, no pullback comparison,
and no compatibility data. The parent separately proves boundedness and performs
the descent and exact Tor reflection in Lean. Thus it does not merely apply a
renamed version of itself.

## No longer needed

No original import was removed: the original file had only its public reduction
data import. No module is withdrawn and no source-library declaration is removed.

The parent's planned invocation of
`lem-weil-pbc-nilpotent-reduction-lissity`
(`Sheaf.Paper.NilpotentReductionLissity`) is not used. The new step follows the
coefficient-filtration proof of Stacks 09BR, using locally constant tensor closure
on common residue strata instead of nilpotent lissity reflection. This only
removes that planned dependency from this argument; it does not claim the module
is unused elsewhere.

The common-stratification, pro-etale restriction, and tensor-pullback inputs are
still needed by the new step and are not pruned. Constructible comparison still
uses the classical-sheaf infrastructure transitively. The separate planned
finite-affine-cover argument for qcqs is replaced by the existing Noetherian
scheme instances; no supporting Mathlib declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No original statement is changed or disputed. The original geometric plan is
mathematically usable but its packaged nilpotent-coefficient bridge cannot be
imported here: `Sheaf.Paper.NilpotentCoefficientLissity` publicly imports
`AdicConstructibleFiniteReductions`, a parent of this item. The present route
avoids that cycle and isolates only the sourced constructibility step.

The printed proof of Stacks 09BQ uses the fixed truncation cutoff i-1, which does
not work without accounting for upper bounds. For example over a field on a point,
factors concentrated in degrees 2 and -2 have nonzero tensor in degree 0, whereas
truncating both below -1 kills the second factor. The new node does not use this
cutoff: its residue is already bounded, so one finite common stratification makes
all its cohomology locally constant, and the existing locally constant tensor
theorem 094H applies directly on each stratum. This is the needed special case of
the tensor step in the proof of 09BR.

Checked the new assertion against J=0, J=the unit ideal, the zero ring and the
empty scheme. No bound on N itself, completeness, finite underlying coefficient
set, or invertibility on X is used. No arbitrary data is chosen from a new
unproved existence assertion.

## New nodes

`lem-sfb-adic-finite-reduction-constructibility` states only constructibility of
cohomology of the higher derived coefficient reductions from a bounded
constructible residue. Its source is Stacks 09BR with exponent shifted by one.
Its docstring and DAG proof give the graded coefficient triangle, derived
balancing, local tensor argument, scalar restriction, and weak-Serre induction.
LeanFinder, LeanSearch and Mathlib grep found no matching theorem; project source
searches and blueprint searches for 09BR and compare-truncations-constructible
found no duplicate. Existing tensor results with finite torsion or field
coefficients do not apply to the arbitrary Noetherian coefficient ring here.

No change record is required: only the item, its node, and the new module and
node are changed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
