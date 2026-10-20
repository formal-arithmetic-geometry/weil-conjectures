## What changed

Closed `AlgebraicGeometry.ProEtale.cartierRootsComparison_isIso` without changing its
statement. The proof identifies the actual kernel lift with the kernel comparison followed
by `kernel.map` of an invertible square. A private helper identifies the units comparison
with the counit by the adjunction formula.

Added the fully proved module `Sheaf.AlgebraicGeometry.ProEtaleUnitsComparison` and its
node `lem-sp-proetale-units-comparison`. Its theorem
`AlgebraicGeometry.ProEtale.proEtaleUnitsCounit_isIso` uses affine pro-etale presentations,
the existing source-library comparison colimit theorem, and an explicit proof that units
commute with filtered ring colimits. It handles every scheme and imposes no exponent
hypothesis. The empty scheme is covered by the same affine dense-subsite argument;
filtered diagrams are nonempty by their stated filteredness hypotheses.

Simplified the existing proof of `cartierForget_exact`: finite colimits follow directly
from the library's `Sheaf.forget₂CoinduceAdj`. This avoids reconstructing an adjunction by
restriction to integer modules and sheafification. Added a proof-only import of
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce`. The units module is also a
proof-only import. Updated step 4 and the dependency union of the original node.

Validation: the units module and the isolated roots proof compiled. The complete item
with the simplified exactness proof compiled in 57.4 seconds; further full-file checks
are recorded by the delivery tool. The three remaining holes are untouched.

## Proved and sorry left

Closed one of the item's four original holes:
`AlgebraicGeometry.ProEtale.cartierRootsComparison_isIso`.

Three original holes remain, all attached to
`lem-sp-cartier-reduction-site-comparison`:

- `AlgebraicGeometry.Etale.cartierPoleBoundary_existsUnique`.
- `AlgebraicGeometry.ProEtale.cartierReduction_existsUnique`.
- `AlgebraicGeometry.ProEtale.cartier_reduction_site_comparison`.

No holes added or split off. The new units comparison module has zero `sorry`.

## No longer needed

The roots-isomorphism proof no longer needs the separate section-formula argument or
finite-etale-roots pullback argument of the original step 4. The pro-etale Kummer exactness
proof also now transports the etale Kummer epimorphism across the units isomorphism, so its
explicit local-cover construction is no longer needed. It uses the stronger,
fully proved units comparison and preservation of kernels. Those nodes remain needed
by other steps of the unfinished overall comparison, so they are retained in its
proof dependencies. No modules are claimed pruned. Existing imports are retained for
the remaining planned proof and the current elaboration instance environment.

## Where the brief, the DAG or earlier work was wrong

The roots comparison does not require positivity or invertibility of the exponent:
comparison identifies the entire units sheaf and preserves kernels. The public
statement retains both hypotheses exactly. The previous plan deliberately avoided
identifying the full units sheaf; the proved affine-colimit argument supplies that
identification directly. No definition or target statement was changed.

## New nodes

`lem-sp-proetale-units-comparison`: the invertible comparison counit on full units.
Its own module proves it completely. It is strictly an input to the roots-kernel
comparison, and is not a restatement of the item. No change records are required:
existing statements and definitions retain their signatures and bodies.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
