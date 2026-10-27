## What changed

Replaced the sole sorry in
`AlgebraicGeometry.ProEtale.SpTowerShriek.strictSystemGeometricRealization`
by a reduction to three strictly smaller obligations. Its declaration signature,
existing public import, and existing docstring are unchanged. No other existing
Lean module or declaration was changed.

The item now privately imports:

- `Sheaf.Paper.SmoothPurityStrictCoordinatesExistence` for coordinates and operations
  without the two three-index equations;
- `Sheaf.Paper.SemilinearScalarTensorComposition` for the scalar/tensor equation on
  an arbitrary existing semilinear calculus;
- `Sheaf.Paper.SemilinearCoefficientPullbackComposition` for composition of the
  inverse-image coefficient squares, before geometric direct-image transposition.

The private, proved categorical lemma `mate_pasting_with_comparisons` supplies the
nontrivial combination step. It transposes through the last geometric adjunction,
uses counit naturality, the counit formula for each of the three mates, and naturality
of the intermediate square and of the coefficient associator. The resulting equation
is exactly the left-adjoint coefficient-square equation. Thus the third conjunct is
proved from inverse-image coherence, without an invertible geometric coefficient
mate, flat quotient maps, or equality detection by derived evaluation.

The parent node now records these actual proof steps. Each residual statement has
its own new module, node, source, natural-language proof, and recorded searches.
There are no shared-interface changes or forced consumer adaptations.

Validation: `lcompile.py --all` compiled all four modules successfully (exit 0).
The coefficient-square and scalar/tensor modules took 7.2 s and 7.1 s; the
coordinate module took 49.7 s and the item took 55.4 s. All are below 60 s.
Temporary profiling options were removed. The original item signature was also
checked byte-for-byte against the current source.

## Proved and sorry left

This is a decomposition, not a net proof gain. One original hole is closed in the
item and three holes are added below it; the delivered item itself has zero sorries.
The net textual hole change is +2. No additional target is claimed proved.

Closed:
`AlgebraicGeometry.ProEtale.SpTowerShriek.strictSystemGeometricRealization`
(node `lem-sp-strict-system-geometric-realization`). Its complete proof uses the
three residual theorems and a proved adjunction calculation.

The following are every sorry left in the delivery:

- `AlgebraicGeometry.ProEtale.SpTowerShriek.strictCoordinatesExistence`
  (`lem-sp-strict-coordinates-existence`): Base and Operations construction with
  the semilinear-derived-sections witnesses. It asserts neither coherence equation.
- `WeilConjectures.SemilinearSections.scalarTensor_composition`
  (`lem-sp-semilinear-scalar-tensor-composition`): one generic scalar/tensor
  coherence law, using the existing representative models and transpose normalization.
- `WeilConjectures.SemilinearSections.Geometry.coefficientPullback_composition`
  (`lem-sp-semilinear-coefficient-pullback-composition`): one generic left-adjoint
  coefficient-square law. It contains no geometric direct-image mate and no choice
  of Base or Operations.

## No longer needed

None. No original import or module was pruned. The original coefficient-tower and
semilinear-derived-sections construction dependencies remain needed by the coordinate
obligation. The generic mate-calculus dependency is used in the proved transposition
step. The original comparison-interface dependency remains public and fixes the exact
maps in the unchanged statement. Moving construction dependencies to the smaller
coordinate node is not counted as pruning mathematics.

## Where the brief, the DAG or earlier work was wrong

The previous single proof step compressed three independent substantial tasks.
`semilinearDerivedSections` gives normalized models and transpose formulas; its
public statement does not also assert either of the two three-index equations.
`mateEquiv_vcomp` supplies pasting, but the actual inverse-image coefficient square
still needs its compatibility with the specified scalar associators. The delivery
separates that missing input and proves its implication for the requested mates.
No mathematical error or disputed statement is asserted.

The simultaneous constant-section coordinate construction must retain the bundled
`Geometry.levelAdjunction_eq` normalization introduced by C4, not merely an HEq
between unrelated adjunction values. The coordinate obligation explicitly retains
this requirement. There is no weakening of a definition or of a target statement.

Sources checked: the current blueprint tower-operations proof, paragraph (2);
Zheng Construction 4.1 (p. 21), Lemma 4.10 and its preceding adjunction construction
(pp. 23--24), and Proposition 4.17 (pp. 25--26); the actual semilinear calculus and
geometry records; Mathlib's mateEquiv_counit and mate-pasting statements. The new
statements include equal coefficient indices, zero complexes, empty schemes, and
ramified coefficients. None assumes a quotient map flat or infers equality of
arbitrary derived morphisms from evaluations. The unit's fixed route is unchanged.

## New nodes

`lem-sp-strict-coordinates-existence`, in
`lean/Sheaf/Paper/SmoothPurityStrictCoordinatesExistence.lean`, isolates ordinary
constant-section coordinate construction. Omitting both coherence equations makes
it a strict part of the original existence assertion, not that assertion renamed.

`lem-sp-semilinear-scalar-tensor-composition`, in
`lean/Sheaf/Paper/SemilinearScalarTensorComposition.lean`, isolates the two-input
K-flat tensor/scalar associativity calculation. It neither constructs geometric
operations nor asserts any coefficient-mate property.

`lem-sp-semilinear-coefficient-pullback-composition`, in
`lean/Sheaf/Paper/SemilinearCoefficientPullbackComposition.lean`, isolates
left-adjoint inverse-image coefficient coherence. The proved categorical lemma in
the item turns this input into direct-image mate coherence.

All three new nodes remain in `sec-smooth-purity`, unit `sk-lem-sp-tower-bound`;
their blueprint ancestry follows the original node to `det-sp-tower-shriek-levels`.
Whole-blueprint searches found no duplicate nodes. LeanFinder, LeanSearch and grep
found generic ordinary-module scalar associators and module-sheaf constructors,
but no statement matching these actual normalized derived operations. No change
record is required: no existing public declaration or public import changed.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
