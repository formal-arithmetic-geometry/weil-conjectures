## What changed

Proved `WeilConjectures.PurityFiniteSetting.smoothPurityMap_naturality_choice_independence`
in `Sheaf.SecSmoothPurity.SmoothPurityNaturality`, with its statement and existing docstring
unchanged. All four added helpers are private and proved in the same module. No definition,
public declaration signature, public import, or source-library file changes.

The proof obtains bounded etale origins for both intrinsic inputs, transports their Tor
intervals through the intrinsic realization counit, and lifts the coefficient arrow using
the bounded-below comparison Hom bijection. It applies the existing
`purityTensorMap_naturality`, then pastes tensor naturality for the fixed inverse orientation
with naturality of the specified tensor-shift comparison. The latter is proved directly
from the published shift's HEq characterization, `NatTrans.shift_app_comm`, and naturality
at the opposite-shift cancellation arrow. The defining specification of the tensor map
proves presentation independence by transitivity of equality.

Only proof imports are added: `Sheaf.Paper.PurityTensorMapNaturality`,
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`,
`Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport`, and
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`.
The node's proof and proof dependencies now describe this assembly.

The existing finite-ring origin and intrinsic Tor transport nodes are used as general
comparison tools from other units. Their statements supply precisely the comparison
coordinates and Tor predicate needed to apply the planned tensor-mate naturality lemma;
no unit-level geometric purity argument is bypassed. No new tool approval is authored.

## Proved and sorry left

Closed the module's sole hole:
`WeilConjectures.PurityFiniteSetting.smoothPurityMap_naturality_choice_independence`
(node `prop-pur-smooth-purity-naturality-cover`). Thus 1 of 1 original sorries is closed,
0 sorries are added, and 0 sorries remain in the delivered module. This is a proof from
existing stated dependencies, not a decomposition. Existing sorries in dependencies,
including the specified-map characterization and tensor-mate naturality, are unchanged.

The four private helpers prove generic tensor-shift naturality, its specialization to
coefficient sheaves, finite etale origins with the fixed-coefficient finite-Tor predicate,
and the final naturality assembly. None contains a hole.

The separate helper drafts and the assembly compiled through `lcompile.py`; the final
consolidated module is checked again by the required delivery compilation and axiom probe.

## No longer needed

Removed these proof imports from the item:

- `Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`
- `Sheaf.Paper.CohomologicalSmoothnessTheorem`
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`
- `Sheaf.Paper.PurityDiagonalDualizingObject`
- `Sheaf.Paper.PurityDncInvariance`
- `Sheaf.Targets.VectorBundlePurity`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution`

The item's assembly no longer directly uses
`lem-weil-pbc-derived-tensor-shift-descent`,
`lem-weil-derived-tensor-functorial`,
`lem-pur-diagonal-orientation-choice-independent`,
`lem-weil-derived-tensor-resolution-independent`, `lem-pc-kflat-resolution`,
`def-weil-derived-tensor`, or `lem-pur-tensor-map-presentation-independent`.
Tensor interchange is ordinary naturality of the existing bifunctor. Shift naturality
follows from the already constructed derived-monoidal shift and its exact HEq
characterization. Presentation independence is already specified by
`existsUnique_smoothPurityTensorMap`. The fixed diagonal orientation and its underlying
geometric construction remain present through `SmoothPurityMap`; this delivery does not
withdraw their declarations or claim their transitive dependencies are globally unused.
Likewise the counit-adjunction and projection-formula arguments belong to the existing
`lem-pur-tensor-map-naturality`, rather than being repeated in this assembly.

Removed the item's four old direct `tool_uses` entries:
`fix-prop-projection-formula`, `thm-sf-ambient-adjoint-class`,
`lem-weil-derived-tensor-resolution-independent`, and
`lem-weil-pbc-derived-tensor-shift-descent`. The first two are encapsulated by the
planned tensor-mate theorem; the last two are replaced in this assembly as explained above.

No module is withdrawn and no global pruning count is asserted. Both original public
imports, including `FiniteCoefficientSmoothPurity`, are preserved.

## Where the brief, the DAG or earlier work was wrong

The interrupted draft split off the whole naturality conjunct with a new `sorry`, but it
had no node and was not ready for delivery. That draft has been replaced by complete private
proofs; its two temporary helper files are absent from the delivery.

The planned general ringed-site tensor-shift descent theorem concerns a different coefficient
presentation from this file's published fixed-coefficient tensor. The local construction
already supplies a precise HEq to the derived-monoidal shift, so its naturality can be proved
without rebuilding or identifying the general descent construction. The plan's presentation
independence also need not be reproved: it is exactly an equality clause of the existing
specified-map theorem. No mathematical statement is disputed or changed.

Edge cases remain covered: the finite-support interval construction includes zero objects;
the shift calculation works for every integer, including zero; no nonzero relative dimension
or nonempty scheme is required. Presentation independence quantifies over the original
arbitrary representatives and comparison isomorphisms.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
