## What changed

Proved the thirteen existing theorems in `Sheaf.Paper.RationalScalarCompletionUnitSquare`.
The ambient strict-tower comparison uses the published reduction transport and its actual
augmentation, with uniqueness from the completion reflector. The main scalar square is a
calculation with that comparison, the specified scalar-completion unit equation, and
naturality. Existing scalar coherence theorems supply the four pasting equations.

Three proved private helpers implement regular-module transport along a ring-sheaf
isomorphism, transport of a finite-free product decomposition, and the completion-unitor
calculation. Finite freeness is transported from the existing completed-coefficient
presentation; the positive ramification factorization is lifted to the actual valuation
rings. The ordinary tensor formula follows by evaluating the conjugate-adjunction unit
identity and using linearity. The representative formula is the defining normalization
of the existing derived scalar-pullback comparison.

Only the item module and its own node are changed. The node's proof, proof dependencies
and proof origin now describe these arguments. Obsolete top-level tool approvals are
removed. No public signature or definition body is changed. No other consumer needs
adaptation.

## Proved and sorry left

Closed 13 existing holes, by declaration name (all in `AlgebraicGeometry.Scheme`):

- `pbcActualAmbientCompletedPullback_tower`
- `rationalScalarCompletionCoefficients`
- `rationalScalarCompletionKappa_unit`
- `rationalScalarCompletionUnitSquare`
- `rationalScalarCompletionUnitSquare_constructible`
- `rationalScalarCompletionRightAdjoint`
- `rationalScalarCompletionKappa_identity`
- `rationalScalarCompletionUnitSquare_identity`
- `rationalScalarCompletionUnitSquare_comp`
- `rationalScalarCompletionKappa_coefficients`
- `rationalScalarCompletionUnitSquare_coefficients`
- `rationalScalarOrdinaryBeta_tensor`
- `rationalScalarOrdinaryBeta_representative`

All are attached to `lem-per-rational-scalar-completion-unit-square`. Zero holes added;
zero split-off statements. No `sorry` remains in the item. The proof uses existing
statements such as `pbcScalarCompletionIso_exists`,
`pbcEmbeddingAmbientTensor_preserves`, `rationalModuleRealizationFunctor`, and
`rationalRealizationPullbackComparison`; their preexisting holes elsewhere are not
claimed as closed by this delivery.

Validation: remote single-file compilation passed in 29.3 seconds with exit code 0.
The updated dependency graph was checked for missing node ids and cycles through this
node. Identity coefficients, positive ramification, zero objects and empty schemes require
no additional hypotheses in the arguments.

## No longer needed

Removed these seven proof imports:

- `Sheaf.Paper.CompletedKoszulQuotientComparison`
- `Sheaf.Paper.ReductionPullbackDerivedTower`
- `Sheaf.CategoryTheory.FiniteFreeCompletionTransport`
- `Sheaf.Paper.FiniteFreeConstructibleScalarTransport`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`

Removed these direct proof dependencies and their obsolete top-level tool approvals:

- `lem-weil-l-adic-extension-absolute-value`
- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-pbc-constant-completion-equivalence`
- `lem-weil-pbc-finite-free-completion-transport`
- `lem-weil-pbc-finite-free-constructible-scalar-transport`
- `lem-weil-pbc-reflected-adjunction-coefficient-squares`
- `lem-weil-pbc-ringed-koszul-completion-reflector`
- `lem-weil-pbc-ringed-pushforward-completion`
- `lem-sfb-ringed-derived-monoidal-comparisons`

The written proof uses the normalized comparisons already provided by
`PbcScalarExtension` and `PbcCompletedPullbackActual`, rather than rebuilding those
comparisons from these generic results. Arithmetic factorization comes from the existing
`integral_ramification` proof. These are removals from this item's direct proof route;
no globally unused module or upstream declaration is asserted withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement repair was necessary. The planned generic reflected-square assembly was
longer than the available implementation: the canonical completion comparison already
has a unique unit normalization, and its completed-pullback comparison is defined from
the required ordinary and completion comparisons. Its coherence equations are already
proved in `PbcScalarExtension`.

For independent review, the additional generic tools used are
`def-pur-completed-coefficient-presentation-transport` (projection-normalized coefficient
presentation and its scalar square), `lem-weil-completed-integral-finite-free`
(the proved arithmetic ramification helper), `lem-pur-system-scalar-coherence`
(identity-on-sections restriction composition), and
`lem-weil-pbc-stratum-completion-unit-restriction` (the published augmentation transport).
They are proof dependencies in the updated node; no new maintainer approval was added.
The unit's realized statement and proof steps remain in place. No new nodes or change
records are needed.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
