## What changed

Replaced the hole in `WeilConjectures.PurityFiniteSetting.finiteReduction_tensorPurity`
by a two-factor argument, preserving its signature and public imports. Three private
proof imports provide the two strictly smaller comparison obligations and the existing
diagonal-orientation reduction theorem.

The new `Sheaf.Paper.FiniteReductionTensorFactors` module constructs the two realized
factors and the comparison on their intermediate tensor with omega. That comparison
uses only scalarPresentation, the normalized binary tensorator, the specified pullback
mate and input counit, and the existing exceptional-unit omegaMap. It uses no purity
map or orientation. All data are explicit composites of existing maps.

The private `tensor_inverse_square` proves inversion and tensor compatibility directly
from the CoreMonoidal naturality field and tensor interchange. The private
`inverseOrientation_reduction` applies it to the existing diagonal reduction equation,
identifies its line comparison, and transports through scalarPresentation by naturality.
An explicitly typed scalarPresentation keeps the final equality in the same functor
coordinates and prevents derived-localization unfolding. The final proof chooses
etale presentations only as proof coordinates, expands both
specified purity maps using their defining characterization, and pastes the two squares.

## Proved and sorry left

Original holes: 1. Closed in the item module:
`WeilConjectures.PurityFiniteSetting.finiteReduction_tensorPurity`
(node `lem-pur-finite-reduction-tensor-purity`).

New holes: 2, each a whole public named theorem with source, proof in words, and node:

- `WeilConjectures.PurityFiniteSetting.finiteReduction_positiveLineComparison`, in
  `Sheaf.Paper.FiniteReductionPositiveLineComparison`, node
  `lem-pur-finite-reduction-positive-line-comparison`: agreement of the two coefficient-line
  reduction maps, without a morphism f, theta, or purity map.
- `WeilConjectures.PurityFiniteSetting.finiteReduction_thetaFactor`, in
  `Sheaf.Paper.FiniteReductionThetaFactor`, node `lem-pur-finite-reduction-theta-factor`:
  transport of the tensor adjunction square, without a diagonal orientation or purity map.

This is a decomposition of one hole into two smaller obligations, not a proof of the
complete mathematical statement from closed dependencies. No holes occur in the new
definitions or private helpers. The existing dependencies retain their own holes.

## No longer needed

None. No original imports, nodes or modules are withdrawn. The flat-model and
finite-adjoint-mate dependencies are still needed by the theta-factor obligation;
they have moved to that node's proof dependencies rather than being pruned. The
reassociation square and the full purity-reduction theorem are not used, just as in
the original plan. The unit route stays unchanged.

## Where the brief, the DAG or earlier work was wrong

The plan's last step treated all coordinate transport as elementary. The declared
tensor-mate theorem is an ordinary-etale equation, whereas the target uses an intrinsic
realization and a uniquely counit-normalized exceptional comparison. The line map in
diagonalOrientationReduction is specified by a CoefficientLineComparison; the tensor
source instead uses finiteTensorPositiveReduction. Their equality is not already a
published equation. Those two precise interfaces are now stated separately. The
inversion, tensorator naturality, realization naturality and pasting are written in Lean.

Edge cases checked in the new statements: d=0 (the scalar unit), m=P.level (the identity
quotient), arbitrary ramification, zero input, empty schemes, and arbitrary etale
presentations. No flatness of the quotient or boundedness of an arbitrary presentation
is added. Presentation independence of smoothPurityTheta already applies to every
presentation. The coefficient-line statement is independent of f and of constructibility.

## New nodes

`def-pur-finite-reduction-tensor-factors` records the explicit factor constructions and
the orientation-independent intermediate omega comparison in the new module
`Sheaf.Paper.FiniteReductionTensorFactors`.

`lem-pur-finite-reduction-positive-line-comparison` records the coefficient-line agreement
step. The proof compares root generators, derived scalar counits, ordered tensor powers,
and canonical site comparisons.

`lem-pur-finite-reduction-theta-factor` records the tensor-mate transport step. It uses
the existing finite-adjoint-mate equation, flat-model reduction, site comparisons and
the uniqueness equation of the intrinsic exceptional comparison.

No existing signature or public-import changes and no forced consumer adaptations are made.
The local proof transparency attributes are recorded in
`coord/changes/A2-finite-purity-tensor-proof-transparency.md`; they do not propagate to consumers.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
