## What changed

Filled the two theorem proofs in `Sheaf.Paper.IsomorphismComparisonNatural`, preserving
both public signatures and all public imports. The finite proof checks the recorded
sectionwise components against the pullback adjunction unit and descends their natural
transformation with Mathlib's localization API.

The integral proof constructs the natural transformation from the specified strict
Roos maps. Ordinary reduction naturality, product extensionality, and a generic
zero-homotopy cone calculation prove naturality before localization. The existing
good-complex localization gives the transformation on the derived category; its
naturality along a quasi-isomorphism proves the formula for every good resolution.
Conjugating by the chosen representative isomorphism identifies its components with
`inverseImagePullbackComparisonDerived`.

The existing normalization theorem supplies the remaining normalization clause for
each coherent coefficient calculus. Its interface requires a complete test object,
so a private proof shows that the zero complex is derived complete, using its zero
reduction tower and distinguished zero triangle. Postcomposition in both cases is
composition with `Functor.whiskerRight`.

The added proof imports are `import all Sheaf.Paper.IntegralOperationsWellDefined`
and `import all Sheaf.Paper.IntegralReductionTowerUnrestricted`, to use existing
proved localization and ordinary-reduction helpers without duplicating their APIs.

Private helpers are fully proved. No new public declaration or interface change is
introduced. The node's proof and proof dependencies record the actual argument. The final
module compiled cleanly through `lcompile.py` in 20.2 seconds; both public theorem
signatures were checked against the original. Added elaboration commands are recorded
in `coord/changes/r6-isomorphism-comparison-natural-proof-context.md`, as required by
server preflight; downstream checking found no current importing modules.

## Proved and sorry left

Closed the two original holes:

- `WeilConjectures.inverseImagePullbackComparisonFinite_natural`.
- `WeilConjectures.inverseImagePullbackComparisonIntegral_natural`.

Both belong to `lem-weil-isomorphism-comparison-natural`. No holes are added and no
`sorry` remains in the delivered module. The proof uses existing stated dependencies,
including the ambient normalization theorem, which is not proved in this packet.

## No longer needed

Removed direct proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Mathlib.CategoryTheory.Sites.Sheafification`.

No module is withdrawn, and the unit route is preserved. The proof does not need a
new tensor-product construction or a separate sheafification calculation: the
specified comparison's section formula and the existing pullback adjunction suffice.
It also does not need `finiteCoefficientModulePullback_exact` from
`Sheaf.AlgebraicGeometry.ProEtaleConstantExact`; the exactness instances for the actual
recorded finite pullback and inverse image are already exported by their defining
module. The obsolete `prop-weil-pbc-proetale-constant-exact` tool-use approval is
removed from this node.

The node no longer directly uses `def-pur-sheaf-tensor-product` or
`def-weil-pbc-sheafification` as proof dependencies. Those constructions still enter
through the existing definitions; their modules and upstream declarations remain.

## Where the brief, the DAG or earlier work was wrong

The normalization theorem's Lean signature does not directly provide the ambient
family without supplying a derived-complete test object. Applying it to the proved
complete zero object supplies that family without any completeness assumption on
an arbitrary input. Its Lean statement also omits the arbitrary-resolution identity
claimed by the original natural-language step. This packet proves that identity
from the actual strict maps and good-complex localization, rather than assuming it
from normalization or reconstructing a derived morphism from finite projections.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
