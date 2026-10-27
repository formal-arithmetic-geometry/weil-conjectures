## What changed

Proved `WeilConjectures.CompactSupportCondensedRealization.realizedCoefficient_square`
from the existing finite, integral, coefficient and section chart normalizations.
All original declaration signatures, definition bodies, public imports and attributes
are retained. The item gains proof-only imports of two completely proved helper modules
and the existing pointwise extensionality API. Local irreducibility markers keep the
reconstruction composites and coefficient maps from repeatedly expanding during later
typeclass inference; exported reducibility and definition bodies are unchanged. The
existing `integralSupport_linear` proof now unfolds `integralSupport` explicitly before
using the same `rawSupport.map_smul` equation, as required by this local opacity.

`NormalizedRealizationIntegralScalar` identifies the completed scalar map on values.
The finite charts are determined on constant sections; naturality identifies the scalar
square at each finite level. The canonical quotient equivalences carry its maps to
reduction of the prescribed field embedding. Integral chart normalization and the
completed projection equation give equality of every positive residue. Injectivity of
the proved valuation-ring inverse-limit equivalence gives equality of integral values.

`NormalizedRealizationSectionScalar` identifies the reconstructed section map on values.
Naturality of the point-pullback adjunction and the profinite-test normalizations prove
the coefficient-object square. The section chart normalizations turn it into the
pointwise section-ring equation. The original theorem follows by cancelling the integral
chart inverse, using these two formulas and the normalized integral inclusions, and
cancelling the section chart inverse.

## Proved and sorry left

Original holes: 1. Closed: 1. Added: 0. Remaining: 0. Split off: 0.

Closed: `WeilConjectures.CompactSupportCondensedRealization.realizedCoefficient_square`
(node `lem-pur-compact-support-condensed-realization-setup`).

Both new helper theorems are completely proved:
`WeilConjectures.normalizedRealizationIntegralScalar` and
`WeilConjectures.normalizedRealizationSectionScalar`. No private helper contains a hole.
No axioms or noncomputable data with an unconstrained unproved existence source are added.

The argument imposes no Noetherian, dimension, invertibility, compactness or nonempty
hypothesis on the scheme or its test objects. Empty test objects are handled by pointwise
extensionality. The quotient maps use the actual recorded integral embedding at every
positive level and do not assume the extension is unramified. Identity extensions and
zero sections are covered by the same equations.

Validation: both helper modules passed the server sandbox compile. With profiling
options removed, the item passed `lcompile.py` in 43.6 seconds with no diagnostics.
The delivery command performs the required final compile and axiom checks.

## No longer needed

No existing Lean imports or modules are removed or withdrawn. The finite scalar-unit
identity is proved locally from its defining comparison equations, so the proof does not
need `AdicFiniteExchangeEncoding` or its derived smooth-exchange dependencies. The direct proof dependency
`lem-weil-pbc-continuous-coefficient-realizations` is replaced by the two proved chart
lemmas. Its Type-0 chart naturality theorem does not apply directly to the field-universe
charts here; the section helper proves the needed universe-general equation from the
existing chart normalizations. This does not withdraw that module from any other consumer.

The existing scheme-pullback theorem `realizationCoefficientSquare` is not used: it has a
different source square and additional realization data. No unit statement or unit proof
step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The existing normalized charts suffice;
the remaining square is proved without strengthening their records. Their finite quotient
equivalences are chosen by normalization rather than definitionally equal to quotient maps,
so the proof explicitly uses their representative equations. Similarly the section-ring map
is chosen uniquely, so its specified section-function equation is used explicitly.

The current source is present in lean/ and already includes the later B2 flatness proofs.
The historical quarantine copy is older and was not substituted for the live module.

## New nodes

`lem-pur-normalized-realization-integral-scalar`, in
`Sheaf.Paper.NormalizedRealizationIntegralScalar`, records the completely proved integral
pointwise coefficient formula. It is the finite-residue part of the original Step 12,
not another formulation of the full coefficient-square obligation.

`lem-pur-normalized-realization-section-scalar`, in
`Sheaf.Paper.NormalizedRealizationSectionScalar`, records the completely proved section
pointwise formula. It uses the profinite-test adjunction independently of the integral
scalar lemma. The item combines the two results with the original inclusion normalizations.

No change record is necessary: no existing interface or non-theorem body is changed.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
