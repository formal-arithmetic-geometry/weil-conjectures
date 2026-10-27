## What changed

Proved `AlgebraicGeometry.Etale.presentedFiniteP1Trace_exchange` without changing
its statement or public imports. The proof identifies the standard projective-line
exchange with the ordinary derived mate, transports coefficient exchange through
the two presentation isomorphisms using composition pasting and the mate-unit
identity, applies the second clause of the given splitting base-change law, and
compares compact-support exchange using the existing unbounded forget-supports
identities. All supporting helpers in the item are private and proved.

Added `Sheaf.AlgebraicGeometry.FiniteShiftedLineSquare` with the proved public
lemma `AlgebraicGeometry.Etale.ordinaryFiniteShiftedLinePullback_square`. This is
coefficient coherence for an arbitrary commuting square, with no trace,
projective-line, properness, cartesianness or finite-ring assumption. The positive
case adapts the already proved private degree-zero and shift calculations of
`FiniteP1TwistedUnitBaseChange`. For N = 0, invertibility on the base makes the
source empty, and the derived target object is zero. All new definitions are
explicit composites of existing constructed maps, not arbitrary witnesses.

Updated the item's proof plan and dependency list and added the matching node
for the new proved lemma. No other existing module or node was changed.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Etale.presentedFiniteP1Trace_exchange`
(node `lem-asd-presented-projective-line-coefficient-trace-exchange`).

Added zero holes. The new
`AlgebraicGeometry.Etale.ordinaryFiniteShiftedLinePullback_square`
(node `lem-asd-finite-shifted-line-square`) and all private helpers are proved.
There are no `sorry` occurrences in either delivered Lean module. This is a proof,
not a decomposition into further obligations. Existing upstream dependencies are
used under the stage-3 rules. The final sandbox compile passes cleanly: 52.0 seconds for the coefficient module
and 35.4 seconds for the complete item. The coefficient proof shares the canonical
proposition instances, reduces the current cached degree-zero functor wrapper,
and supplies the functors and comparison isomorphism explicitly.

## No longer needed

The proof does not need the planned dependencies
`lem-kun-derived-pullback-composition-monoidal`
(`Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`) or
`cor-cbc-proper-coincidence`
(`Sheaf.AlgebraicGeometry.ProperCoincidenceNormalized`). The first is replaced by
coherence for the particular normalized shifted line; no tensor product enters.
The second is replaced by a direct calculation with the already proved source
forget-supports identities. These nodes were removed from this item's proof
edges; their modules were never imported here and are not withdrawn. No claim is
made that other parents cease needing them. No source-library declaration is
removed or changed.

Removed redundant proof imports from the copied helper setup:
`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`,
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor`, and
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`.
The retained imports already expose their APIs. The broad `Supports` proof import
is replaced by `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic`:
the empty-scheme case follows directly from the zero-sheaf and zero-derived-category
lemmas. The coefficient module retains `MapDerivedCategoryMate` for its mate API. The item uses the precise
compactification-refinement, cup-product-coherence and projection-exchange
modules, rather than importing `LowerShriekLowerStarWeil`. Its redundant proof
imports of `UpperLowerStarAdjunctionCompat` and `MapDerivedCategoryMate` were also
removed; they are exposed by the existing public dependency.
The item's original sole public import is retained. The standard splitting,
trace-model, fibre-product and mate-pasting dependencies remain in the proof.
The unit route is preserved; the unit's `realized` lists are empty.

## Where the brief, the DAG or earlier work was wrong

The previous DAG plan proposed restricting to bounded-below coefficients and
then passing to the unbounded category for proper coincidence. The source
library already proves the needed unbounded compactification exchange and
forget-supports identities. Their composition proves the general proper square
comparison directly, so no bounded-below preservation or detection argument is
needed. The underlying theorem statement is unchanged.

The normalized positive-case line composition calculation in
`FiniteP1TwistedUnitBaseChange` is private and assumes N > 0. It cannot simply be
applied to this arbitrary-N item. Its proof has been reused for a general square,
and the N = 0 case has been supplied by the empty-scheme argument. Identity maps,
N = 1, zero coefficient rings and empty schemes require no additional hypotheses.

## New nodes

`lem-asd-finite-shifted-line-square`, in
`dag/nodes/sec-six-functors-basics/lem-asd-finite-shifted-line-square.json`, records
the fully proved normalized coefficient square. It is strictly coefficient
coherence, independent of every trace and presentation exchange in the item.
Its Lean attachment is
module `Sheaf.AlgebraicGeometry.FiniteShiftedLineSquare`, declaration
`AlgebraicGeometry.Etale.ordinaryFiniteShiftedLinePullback_square`. The node has
the source, complete proof steps, dependency union and three Mathlib searches.
No change record is needed: no existing statement or shared definition changed.

The presentation equality is eliminated before expanding the trace definition;
this avoids expensive dependent conversions in the inverse comparison. No timing,
profiling or diagnostic commands remain in the delivered modules.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
