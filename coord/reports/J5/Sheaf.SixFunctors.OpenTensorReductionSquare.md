## What changed

Proved the body of `WeilConjectures.OpenInterchangeReduction.openTensorReductionSquare`
from the ordinary restriction/tensor coefficient square. The item retains its exact
statement and public import. Added private proof imports of
`TensorAdjunctionReductionSquares` (including its private ordinary-comparison API),
`CanonicalOpenReductionIsIso`, and the new `CanonicalReductionPullTensor` module.

The private categorical lemma `projection_inverse_square` proves the adjunction
pasting calculation from tensor compatibility and the two adjunction squares.
`ordinary_open_tensor` applies it to the actual normalized ringed/system operations,
inserts the two child comparisons by naturality, and inverts the result. The existing
`assertion_of_ordinary_square` then cancels the short-word completion comparison.
No source-library file or shared interface changes.

Validation: the new primitive module compiled with `lcompile.py` in 48.4 seconds;
the complete combining module compiled in 16.6 seconds. Removed the two reported
unused simplifier arguments before the delivery checks. The existing public
signature matches the repository verbatim, and both node dependency lists match
the union of their proof-step uses.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.OpenInterchangeReduction.openTensorReductionSquare`
(node `lem-sf-open-tensor-reduction-square`). No sorry remains in the item module.

Added one strictly smaller hole:
`WeilConjectures.GeneratorReduction.canonicalReductionPullTensor`
(node `lem-sf-canonical-reduction-pull-tensor`). It is the ordinary whole-system
restriction/tensor square: no word, open extension, projection formula, completion
transport, length bound or admissibility hypothesis occurs in it. Its docstring and
node give the strict representative argument. Thus this delivery is a decomposition
(one original hole closed, one smaller hole added), not a net reduction in holes.
All private combining helpers are proved.

## No longer needed

No existing import was removed: the item's public import supplies its statement.
The direct proof no longer needs `lem-sf-immersion-completed-pullback-comparison`
(`Sheaf.Paper.SfImmersionCompletedPullbackComparison`),
`def-sf-tensor-completion-comparison` (`Sheaf.SixFunctors.OpenFactorTensorModel`),
`lem-weil-pbc-site-derived-tensor-descent`
(`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`),
`lem-sf-open-tensor-normalization` (`Sheaf.SixFunctors.OpenTensorNormalization`),
or `lem-sf-integral-open-reduction-comparison`
(`Sheaf.SixFunctors.IntegralOpenReductionComparison`) as additional direct proof
imports. Their roles are supplied by the existing completion-transport theorem,
the prescribed projection transpose fields, and the canonical inverse open mate.
The tensor-descent result remains a dependency of the new representative-level
obligation; tensor-completion and open-comparison definitions remain needed by the
existing public interface. This does not withdraw any module or claim that these
modules are globally unused.

## Where the brief, the DAG or earlier work was wrong

The old proof mixed the representative restriction/tensor check with the completed
projection argument. Its cited immersion and tensor-descent declarations do not by
themselves state the required normalized coefficient square. The new node isolates
that actual missing step. Existing ordinary-comparison and completion-transport
lemmas make the remaining mate calculation a direct categorical proof, with no
finite-evaluation equality detection. No mathematical statement or unit route changed.

## New nodes

`lem-sf-canonical-reduction-pull-tensor`, in
`lean/Sheaf/SixFunctors/CanonicalReductionPullTensor.lean`, is the restriction/tensor
step of the original node's proof. It is strictly smaller than the open projection
square and is needed by the explicit adjunction-pasting proof. The item node's
proof and proof dependencies now follow the Lean proof. No change record is needed:
all existing public signatures, definitions, attributes and public imports are unchanged.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
