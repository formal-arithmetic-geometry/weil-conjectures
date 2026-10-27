## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.stratumReduction_normalization`
by a composition calculation with the published adjunction mates. A proved private
categorical helper combines the two scalar adjunctions, their normalization mates,
and the restriction/pullback composition square. Cancelling the three invertible
finite comparisons gives the existing statement verbatim.

Added two supporting modules, imported privately by the item:
`Sheaf.Paper.ReductionNormalizationScalarMate` identifies the published quotient
normalization with the scalar-composition mate;
`Sheaf.Paper.RestrictionPullbackScalarComposition` proves coherence for successive
scalar restrictions and geometric pullback. Both use the actual chosen comparisons,
not arbitrary isomorphisms. Updated the item's proof route and added matching nodes.
No existing signature, definition, attribute or public import changes.

Validation: all three modules compiled through `lcompile.py`; the final clean
item compile took 49.5 seconds. The supporting modules also compile without warnings.

## Proved and sorry left

Closed one of the item's two original holes:
`AlgebraicGeometry.Scheme.stratumReduction_normalization`.
The added theorems `AlgebraicGeometry.Scheme.completedReductionNormalization_scalarMate`
and `AlgebraicGeometry.Scheme.proEtaleRestrictionPullback_scalarComposition`
are proved; no holes are added. This is one hole closed, zero split off.

The only remaining hole in this delivery is the unchanged
`AlgebraicGeometry.Scheme.stratumReduction_evaluation`, attached to
`lem-weil-pbc-stratum-completion-unit-restriction`.

The scalar argument includes equal quotient levels and the zero quotient ring;
the pullback argument includes empty schemes and arbitrary unbounded derived objects.
No extra flatness or Noetherian assumptions are introduced.

## No longer needed

None. No existing imports, modules or DAG dependencies are pruned. The normalization
proof uses two newly proved coherence facts instead of leaving the balancing
calculation as an unstated elementary step.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The representative-balancing step also requires
identification with the published scalar adjunction and exact-localization
comparisons. The new supporting results make those identifications explicit.
The unit's proof route is preserved. A read-only transitive dependency check found
the pre-existing cycle `lem-pc-ring-hom-extension-differential` to
`lem-pc-ring-hom-extension-differential-adjacent` and back, also present in the
unchanged repository baseline. This delivery introduces no dependency cycle and
does not modify those unrelated nodes.

## New nodes

`lem-weil-pbc-reduction-normalization-scalar-mate`, in
`dag/nodes/sec-proper-base-change/`, records the scalar-only identification of the
quotient normalization. Its proof uses the existing derived Hom, cochain-adjunction,
normalized-adjunction composition and exact-restriction composition theorems.

`lem-weil-pbc-restriction-pullback-scalar-composition`, in the same directory,
records coherence of geometric pullback with two successive scalar restrictions.
Its proof transposes the ordinary equation to identity maps on sections and then
uses exact-square localization composition. Neither new statement restates the
item: the first has no geometric morphism, and the second has no scalar extension
or quotient normalization. There are no change records because no other existing
module or interface changes.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
