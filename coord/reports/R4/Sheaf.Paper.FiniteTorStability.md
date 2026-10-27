## What changed

Filled `WeilConjectures.finiteTor_stability_integral_images` without changing any
public statement or definition. Support preservation follows from the published
constructible support realization, whose package identifies its coherent tower and total
right derived limit with exactly the choices used here. Exceptional preservation follows from integral Verdier duality,
completed pullback, and integral Verdier duality again.

Private proved helpers identify reduced completed pullback with finite pullback and
transport finite Verdier bounds to integral reductions. Applying the two finite dual
bounds gives the specified uniform interval `[a-2dX,b+2dY]` at every positive level.
The proof allows zero and empty inputs, residue level zero, and zero dimension bounds.
The DAG records this proof route and its existing dependencies.

## Proved and sorry left

Closed one of the six original holes:
`WeilConjectures.finiteTor_stability_integral_images`.
Added zero holes and split off zero statements.

The five unchanged holes are:

- `WeilConjectures.finiteTor_stability_origin`;
- `WeilConjectures.finiteTor_stability_geometric_quotients`;
- `WeilConjectures.finiteTor_stability_integral_adjunction`;
- `WeilConjectures.finiteTor_stability_rational`;
- `WeilConjectures.finiteTor_stability_algebraicClosure`.

Validation: the complete item module compiled through `lcompile.py` in 54.3 seconds,
within the 60-second limit, after the proof was complete. The pullback comparison
also compiled independently. The final delivery checks recompile the cleaned module.
Local irreducibility attributes keep the existing completed-operation and selected
support-value definitions folded during proof checking; no exported attribute,
statement, definition body, or consumer is changed. Temporary profiling options
and all scratch modules have been removed.

## No longer needed

No module or node is withdrawn, and no existing import is removed. The integral-image
proof does not use `prop-coef-integral-exceptional-adjoint`; that dependency remains
needed for the unfinished integral adjunction. All earlier finite, quotient, Hom,
and Verdier proofs are retained.

## Where the brief, the DAG or earlier work was wrong

The former integral-image plan proposed applying the integral exceptional-adjoint
package directly. Its recorded Lean declaration uses a different presentation of the
integral category and does not directly identify the chosen functors in this module.
The proof now uses the published comparison for exactly the chosen support tower and
proves preservation and the bound from the displayed duality composite. No statement
is disputed or weakened.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
