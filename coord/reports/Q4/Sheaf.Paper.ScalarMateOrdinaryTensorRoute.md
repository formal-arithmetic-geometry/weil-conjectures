## What changed

Proved `AlgebraicGeometry.Scheme.DerivedScalarMate.scalarMate_ordinary_tensor_route`
with its original statement and the prescribed scalar-mate/ordinary-tensor route.
The main module constructs the ordinary scalar isomorphism by double mates, proves
its unit equation, and combines the restricted derived-counit square with the ordinary
cochain square. Functoriality of localization and naturality of the exact pullback
factor give the displayed conclusion.

Four new proved modules separate the calculations. The ordinary module proof computes
both maps on every local pure tensor after the geometric inverse-image adjunction.
It proves the coefficient-unit normalization from the selected tensor-unit property's
uniqueness. The single-coefficient proof identifies inverse total pullback with the
standard bifunctor comparison and applies the existing single-complex component and
coefficient-naturality formulas. The cochain theorem applies the module theorem degreewise
and conjugates by the fixed single-complex isomorphisms. The derived-counit theorem uses
the normalized adjunction units on K-flat representatives and the exact restriction square;
it accepts any ordinary scalar isomorphism with its unit equation.

This organization keeps the checking cost of each file below the 60-second limit.
The final ordered compile passed all five modules: OrdinaryModuleRoute 4.7 seconds,
RestrictionCounitRoute 5.2 seconds, TensorScalarOrdinarySinglePullback 46.6 seconds,
OrdinaryComplexRoute 36.7 seconds, and the assigned OrdinaryTensorRoute 22.7 seconds.
Every added import in the assigned module is proof-only. The new modules have the public
imports their statements need. No existing shared definition, declaration signature,
public import, attribute or instance was changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.DerivedScalarMate.scalarMate_ordinary_tensor_route`.
Added zero holes. No `sorry` remains in any delivered module. All private helpers and
the four new public lemmas are proved:

- `AlgebraicGeometry.Scheme.DerivedScalarMate.scalarMate_ordinary_module_route`;
- `AlgebraicGeometry.Scheme.DerivedScalarMate.tensorScalarOrdinaryPullback_single_f`;
- `AlgebraicGeometry.Scheme.DerivedScalarMate.scalarMate_ordinary_complex_route`;
- `AlgebraicGeometry.Scheme.DerivedScalarMate.scalarMate_restriction_counit_route`.

The proof uses existing project specifications for scalar adjunctions, tensor pullback
and representatives; their existing unproved obligations remain their own items.
There is no decomposition into new unproved statements.

## No longer needed

The original public import of `Sheaf.Paper.ScalarTensorOrdinaryPullback` is retained.
No original Lean import was removed: it was the assigned module's only original import.
Proof imports for the representative calculation now reside in its new module.

Removed `lem-sfb-kflat-scalar-comparison-normalization` from this node's direct proof
requirements. Its existing same-universe categorical statement does not specialize to the
pro-etale site's distinct object and morphism universes. A private categorical calculation
with independent object, morphism and derived-category universes proves the representative
formula needed here, inside `ScalarMateRestrictionCounitRoute`.
This does not withdraw `Sheaf.Paper.KFlatScalarComparisonNormalization`: the existing
scalar data still imports it transitively. The original adjunction-unit, K-flat pullback
and restriction dependencies remain needed in the extracted proved calculations.
No existing module or node is withdrawn, and no global obligation is pruned.

## Where the brief, the DAG or earlier work was wrong

The same-universe comparison dependency in the original plan cannot be instantiated
directly at these pro-etale module categories. The private abstract formula makes the
universes independent. The coefficient calculation also requires proving that the selected
pullback unit has the standard adjunction normalization; existence of an arbitrary
isomorphism would not supply its section formula. The proof derives that normalization
from the specified tensor/right-unitor property.

The statement is unchanged. No flatness of B or boundedness of P is assumed. The UNIT's
route remains derived scalar mate, ordinary scalar/tensor comparison, then tensor descent.
The concrete checking cost required separating the proved calculations into modules and
parameterizing the representative comparison by its ordinary isomorphism and unit equation.

## New nodes

`lem-sfb-scalar-mate-ordinary-module-route`, in
`Sheaf.Paper.ScalarMateOrdinaryModuleRoute`, is the ordinary module calculation, with no
derived categories, scalar counits, complexes or K-flatness. Its node records the local
pure-tensor calculation, coefficient normalization, source and searches.

`lem-sfb-tensor-scalar-ordinary-single-pullback`, in
`Sheaf.Paper.TensorScalarOrdinarySinglePullback`, is the ordinary total comparison with a
single coefficient. Its degreewise formula contains no scalar mate or derived category.

`lem-sfb-scalar-mate-ordinary-complex-route`, in
`Sheaf.Paper.ScalarMateOrdinaryComplexRoute`, combines those two ordinary calculations for
any scalar isomorphism satisfying its unit equation. It needs no K-flatness.

`lem-sfb-scalar-mate-restriction-counit-route`, in
`Sheaf.Paper.ScalarMateRestrictionCounitRoute`, is the representative scalar-counit square
before ordinary tensor-coordinate identifications. It accepts any unit-normalized ordinary
scalar isomorphism; the original module constructs the concrete double mate.

All four nodes attach complete proofs. Sources, searches and complete arguments are in
the node records and declaration docstrings. No change records or forced adaptations are
needed because only the assigned module, new modules, and their node records were changed.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
