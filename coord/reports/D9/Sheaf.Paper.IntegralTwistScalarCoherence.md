## What changed

Replaced the sole `sorry` body of
`WeilConjectures.integral_twist_scalar_coherence` with a complete Lean assembly
from existing declarations and two smaller named interface statements. The
original statement and both helper definitions are unchanged. The existing
public imports are unchanged.

The ordinary associator is the derived projection of the specified
`CompletedLineTensor.associatorData`. Its normalized sheaf map gives the
termwise tensor formula and its counit equation. Expanding the canonical
completed associator and cancelling the completion isomorphisms proves the
ordinary-to-completed associator equation. The scalar multiplication unit,
both repeated-field scalar laws, and the rational component follow from the
existing canonical-restriction, scalar-coherence and rational-component
specifications.

The two new modules isolate different arguments: identification of the
published twist beta with the ambient line tower/unit, and normalization of
the common ordinary chain model. The latter conclusion has neither the named
completed associator nor the completed beta; the main proof composes the
published beta conjugation equation with the scalar associator equation to
obtain its requested completed right path. The ambient tower/unit are
transported to the named integral comparisons by canonical restriction.

Updated the parent node's proof, proof dependencies and proof origin to match
that implementation. Added private proof imports of the two new modules and
`Sheaf.Paper.CompletedLineTensorCoherence` and removed the unused private
imports listed below. No definitions, source-library files or consumers were
adapted.

## Proved and sorry left

Original hole removed: `WeilConjectures.integral_twist_scalar_coherence`
(node `lem-weil-integral-twist-scalar-coherence`). Its proof now assembles all
eight clauses without any internal `sorry`.

Holes added, each the entire proof of a named public theorem:

- `WeilConjectures.integral_twist_ambient_coherence`, node
  `lem-weil-integral-twist-ambient-coherence`, in
  `Sheaf.Paper.IntegralTwistAmbientCoherence`.
- `WeilConjectures.integral_twist_common_scalar_model`, node
  `lem-weil-integral-twist-common-scalar-model`, in
  `Sheaf.Paper.IntegralTwistCommonScalarModel`.

This is a decomposition: one old hole closed and two smaller holes added,
not a net proof of the original assertion. The item module itself has zero
holes; the delivered new modules have two holes in total. Five of the eight
original clauses are proved directly from already stated declarations; the
three twist clauses are assembled from the two new interface theorems.
Each new theorem has a source and a full proof in words in its docstring and
DAG node. The existing constituent declarations may still rest on their own
registered holes.

Validation: remote compilation and delivery preflight results are recorded
below once complete.

## No longer needed

Removed private proof imports:

- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`.
- `Sheaf.Paper.PurTwistSheafLocallyFree`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Mathlib.Algebra.Homology.BifunctorShift`.
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.

The parent no longer directly needs the following planned proof dependencies:

- `lem-weil-integral-scalar-extension-constructible`.
- `lem-weil-finite-free-completed-scalar-comparison`.
- `lem-weil-integral-constructible-triangulated`.
- `def-weil-derived-complete-integral-detailed`.
- `def-weil-pbc-proetale-site`.
- `lem-pur-twist-sheaf-locally-free`.
- `def-coefficient-twists-detailed`.
- `lem-pur-ordinary-line-derived-scalar-comparison`.
- `lem-weil-integral-twist-base-change`.
- `lem-pur-signed-line-scalar-tensor-tower`.
- `lem-pc-kflat-resolution`.
- `lem-pur-derived-change-of-rings`.
- `def-weil-integral-scalar-extension`.
- `lem-weil-natural-comparison-tower-transport`.
- `def-weil-rationalization-karoubi`.
- `lem-weil-integral-constructible-linear`.
- `lem-weil-l-adic-integers-localization-uniformizer`.

These are changes of direct proof dependencies, not withdrawals. Generic
line, K-flat and completion results used by either new interface node remain
its explicit proof dependencies. Existing public imports and adopted source
modules are retained. No module is claimed to be outside the targets' closure
or withdrawn by this delivery. The generic
`lem-weil-natural-comparison-tower-transport` is unnecessary in the main
assembly: the required conjugation calculation is written directly, and
rational naturality is already part of the specified rational comparison.

## Where the brief, the DAG or earlier work was wrong

No false statement was found, and there is no requested repair or current
return for this item in the local records. The unit route is retained; this
node is not itself a realized statement or proof step of its historical unit.

The original proof plan describes the mathematical normalizations, but the
existing Lean interfaces do not directly identify the beta chosen by
`integral_twist_derived_scalar` with `CompletedLineTensor.beta`. The former
is fixed by its own K-flat tensor/counit characterization, while the latter
uses `pairData`; comparing these is an argument, not definitional equality.
The ambient interface node isolates exactly that identification and its
unit specialization. Likewise the single-extension chain model and ordinary
associator exist independently, but no existing theorem states their combined
right-path normalization with the particular resolving comparison appearing
in this item. The common-model interface records that strictly smaller step.
Neither interface includes the five scalar/rational clauses, and the model
interface does not contain the completed square.

Checked the new statements for m=0, m<0, C=0, empty S, identity embeddings,
fully repeated fields and ramified towers. Their tensor formulas, counit
normalizations and use of derived rather than chain inverses remain valid.
The supplied proof hC in the ambient interface is exactly the existing
membership proof of the actual twist; it adds no assumption to the parent.

## New nodes

`lem-weil-integral-twist-ambient-coherence` states the ambient tower and
multiplication-unit equations for the published beta and the ambient
completed associator/unit. It records how the existing ordinary signed-line
comparisons and the published beta are identified through local tensor and
K-flat counit normalization. It has no rationalization or common-model clause.

`lem-weil-integral-twist-common-scalar-model` states the chain tensor formula
and its ordinary normalization mu >> alpha >> W(chi). It composes the
existing scalar associator with the single-extension chain comparison. The
main proof supplies the separate completed-associator/beta transport, so this
statement is a proper part of the original argument.

Both nodes retain chapter `sec-smooth-purity`, historical unit
`sk-prop-sf-existence`, and the blueprint ancestor `prop-weil-twist-preserves`.
No change record is needed: existing signatures, definitions and public
imports are unchanged.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
