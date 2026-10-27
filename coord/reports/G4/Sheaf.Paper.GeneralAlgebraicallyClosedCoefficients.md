## What changed

Filled `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_comparisons`
in the assigned module, including both its associator and unit clauses. Two proved private
lemmas first establish independence of the characteristic parameter over arbitrary
coefficient fields. They unfold the rational and integral normalizations and the integral
scalar restriction: the parameter occurs only in preservation proofs, which proof
irrelevance identifies. Specialization to the small coefficient models, the general
associator specification, and explicit reduction of finite-field transition/category
caches prove the existing conjunction.

All existing public signatures, public imports and definition bodies are preserved.
The item's node records the additional proof step. No other module is changed.

The comparison proof compiled in isolation in 26.8 seconds. Full-file compilation and
preflight are performed by the delivery tool. Scratch modules and profiling options are
excluded from the delivery.

## Proved and sorry left

Closed one of the six original holes, with no holes added and none split off:
`WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_comparisons`.

Five original holes remain, all attached to
`def-weil-algebraically-closed-coefficients`:

- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.shift_existsUnique`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.transitionIso_commShift`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_homCoordinates`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_commShift_existsUnique`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_distinguished`.

The supporting stage module is unchanged by this delivery.

## No longer needed

None. No import, module, declaration or dependency node is withdrawn. The remaining
shift, coordinate and triangulation obligations retain the existing planned dependencies
and unit route. No new intermediate theorem with `sorry` is introduced.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The existing normalized comparison specifications suffice for
this obligation. A scratch attempt at the Hom-coordinate obligation proved abstract
stage-equality and representative-extensionality glue, but its concrete specialization
still incurred expensive equality checks between cached additive structures; that attempt
is excluded and the original obligation is retained unchanged.

The latest blueprint no longer has the historical order-1462 definition file. Its current
finite-coefficient two-colimit discussion was read in
`sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/_section.md`. The assigned statements
and existing source references are preserved.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
