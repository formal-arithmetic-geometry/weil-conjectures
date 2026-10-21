## What changed

Proved `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_adjunct`, including both
its adjunct characterization and its restriction equation. The proof follows step 2
of `lem-sf-semilinear-proper-open-mate-pasting`.

Private, proved categorical helpers transport the Hom equivalence through the
conjugate of beta, cancel the invertible open unit, identify the clopen projection
with the proper unit, and compute the inverse composite-adjunction conjugate.
A private projection-square constructor and its equality with alpha keep these
calculations abstract until application to the actual derived categories.

Every existing public signature, public definition body, instance body, attribute
and import is unchanged. The existing private `conjugate_transport` helper was
moved earlier, with its statement and proof unchanged, so the compositor transport
arguments are grouped together. There are no consumer adaptations. The interface
comparison reports no changes. `tools/downstream.py` reports zero downstream Lean
modules; the queried declarations occur only in this item. Existing DAG parents
and the unit route remain in place.

The complete module compiled through `lcompile.py`. Its final delivery is also
checked by `deliver3.py` against the server's published library.

## Proved and sorry left

Closed one of the original ten holes:

- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_adjunct`.

Added holes: zero. Split-off statements: zero.

Nine original holes remain, all in the namespace
`AlgebraicGeometry.ProEtale.SemilinearProperOpen`:

- `semilinearProperOpenMatePasting`
- `gamma_identities`
- `rhoPullInv_isIso`
- `rhoR_isIso`
- `rhoJInv_isIso`
- `gamma_scalarRestriction`
- `evalR_isIso`
- `evalJInv_isIso`
- `gamma_evaluation`

The private auxiliary declarations are all proved; their data constructions contain
no holes. The proof uses the library's existing stated dependencies in accordance
with stage 3.

## No longer needed

None. No import, node or module is withdrawn. The remaining declarations continue
to use the existing dependencies, and this proof follows the recorded route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or dependency was disputed. Directly rewriting the alpha
formula inside a composite of concrete derived morphisms caused kernel timeouts.
The proved abstract projection-square formula and the named equality for alpha
resolve this without changing any public construction or increasing a compile limit.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
