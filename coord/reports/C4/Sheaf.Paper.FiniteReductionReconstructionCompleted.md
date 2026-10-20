## What changed

Replaced the original hole in `finiteReductionReconstructionCompleted` by an adjunction
argument for the specified counit, transfer of product preservation from a strict-perfect
tensor model, and the two adjunction naturality laws. All existing declarations, signatures,
visibility and definition bodies are preserved.

Added separate interfaces for the normalized completion unit, the normalized Koszul Roos
triangle, a strict-perfect quotient tensor model, and its derived scalar comparison. The
unit comparison is proved by completing the identities on the two product vertices to a
triangle morphism and applying the levelwise-isomorphism theorem. The tensor model is
proved by lifting the perfect quotient's derived isomorphism to a quasi-isomorphism,
applying completed constant sheaf reduction, and converting its finite coproduct retracts
into finite product retracts. New files have their own matching DAG nodes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.finiteReductionReconstructionCompleted`.

New proved declarations:
`AlgebraicGeometry.Scheme.completedReconstructionUnitComparison`,
`AlgebraicGeometry.Scheme.completedFiniteReductionTensorModel` and
`AlgebraicGeometry.Scheme.completedFiniteReductionTensorComparison`.

Remaining new holes:
`AlgebraicGeometry.Scheme.completedKoszulReductionRoosTriangle`, node
`lem-weil-pbc-completed-koszul-reduction-roos-triangle`.

This is a decomposition, not a proof independent of new holes: one original hole closed,
one new hole added. The retained assertion concerns reconstruction before
completeness, with its unit normalized at every quotient. It contains neither the
finite reduction counit nor product preservation or the parent naturality conjunction.
There is no hole in a definition, no changed
existing statement, no new axiom, and no arbitrary object selected by a definition from
an unproved existence assertion.

## No longer needed

Removed the item's proof imports of `Sheaf.Paper.AdicCoefficientDatum`,
`Sheaf.Paper.CompletedConstantSheafReduction`, `Sheaf.Paper.KoszulReconstruction`, and
`Sheaf.Paper.PbcRoosTriangle`: the parent now uses the more precise completed-presentation
interfaces. The completed constant reduction theorem remains needed by the new model;
the normalized Koszul comparison and the specified completedRlim Roos triangle
remain in the proof plan of the new source comparison. The new Roos source lemma has no proof-only import: its future source
comparison is recorded in its node and docstring. No existing declaration or module
is withdrawn, and no global pruning is claimed. The unit's realized nodes remain untouched.
The parent no longer cites `prop-weil-pbc-koszul-reconstruction`
(`Sheaf.Paper.KoszulReconstruction`) or `prop-weil-pbc-roos-triangle`
(`Sheaf.Paper.PbcRoosTriangle`). The new source comparison instead uses
`lem-weil-pbc-completed-koszul-quotient-comparison` and the specified Roos triangle
under `prop-weil-pbc-rlim-functoriality`. The coefficient-datum and constant-reduction
nodes remain needed through the new tensor lemmas; the finite-projective tensor
product node remains directly needed.

## Where the brief, the DAG or earlier work was wrong

The listed Koszul reconstruction signature uses coefficients in the scheme universe,
whereas this module uses coefficients one universe above it. Its continuous-function
coefficient presentation and derived-limit interface also differ from the explicit
completed constant coefficient and specified Roos triple here. The existing normalized
completed Koszul quotient comparison addresses that universe but still needs coefficient
and strict-tower transports to yield the evaluation-normalized Roos statement used here.
Application of completedKoszulQuotientComparison to the transported representative
was checked in Lean. A further scratch check constructs the round-trip comparison
between explicit completion fibers and verifies its unit equation by naturality.
The degreewise coefficient round trip also preserves the chain unit. The full
derived transport and its compatibility with the chosen model tower and normalized
derived scalar units remain to be supplied by the retained lemma. This is an interface gap, not a
claim that either mathematical assertion is false.

The completed constant reduction theorem supplies the strict-perfect complex and its
augmentation; it does not itself state a natural isomorphism of the chosen derived
scalar extension with the descended tensor functor. The proved comparison supplies
that derived-functor identification, using ordinary tensor cancellation, the existing
K-flat scalar counit theorem, and localization of K-flat homotopy objects. Zero quotients,
empty generators, the unit ideal and
the empty scheme are included in the normalization and tensor arguments.

## New nodes

`lem-weil-pbc-completed-reconstruction-unit-comparison` records the proved comparison with
any specified Roos triple under completeness.

`lem-weil-pbc-completed-finite-reduction-tensor-model` records the proved construction of
a bounded finite-free-retract quotient model with its natural tensor identification.

`lem-weil-pbc-completed-koszul-reduction-roos-triangle` records the normalized quotient
Roos triangle on explicit Koszul completion without a completeness hypothesis. Its proof
plan includes the coefficient transport, pro-zero Koszul cones, and unit normalization.

`lem-weil-pbc-completed-finite-reduction-tensor-comparison` records the derived tensor
calculation from a strict-perfect quasi-isomorphism to the restricted quotient. Its proof
uses ordinary tensor cancellation, the existing K-flat scalar comparison, and full
faithfulness of precomposition with K-flat localization.

No change record is required: no existing definition or statement changed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
