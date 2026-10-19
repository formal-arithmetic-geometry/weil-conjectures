## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientHeart_filtration` with its statement
unchanged. The argument proves the open counits monic, the empty and full endpoints,
and nesting by composition of adjunctions. Condensed localization identifies the
successive cokernels with closed-then-open extensions. A proved mixed-factorization
comparison identifies these with the specified scheme-theoretic-image extensions.
Common stratification supplies the lisse restrictions.

Added the proved module `Sheaf.Paper.CoefficientHeartFiltrationCore`. It compares
internal condensed-module operations with sectionwise module operations, proves
composition of the uniquely normalized coefficient identifications by transposing
under the composite adjunction, applies the stated locally closed extension
coherence theorem, and cancels the fully faithful section-module equivalence.
Its proof imports are private to the module; its public imports supply its statement.
No existing definition or statement changes, and no consumer adaptation is needed.

Retained the earlier sandbox work and repaired its remaining proof. The slow
sectionwise composition calculation is now proved for arbitrary sheaves before
specializing to reconstructed condensed coefficients. This avoids the expensive
unfolding that caused the earlier 60-second timeout, without splitting the proof
into additional modules or changing the compiler limit. Diagnostic prefix files
are retained only in the scratchpad and are excluded from delivery.

Validation: `lcompile.py --all` compiled the core in 10.4 seconds and the parent
in 14.4 seconds, both without diagnostics. The core has no unfinished proof.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.coefficientHeart_filtration`
(node `det-lem-coefficient-heart-filtration`).

Also proved the previously unfinished sandbox helper:
`AlgebraicGeometry.ProEtale.coefficientHeart_filtration_core`
(node `new-det-lem-coefficient-heart-filtration-core`).

Original item holes: 1. Holes closed: 1. Holes added: 0. Holes left in the delivered
modules: 0. No unfinished result is split off. These proofs use the project's
already stated dependency theorems, including locally closed extension coherence
and the normalized cartesian coefficient comparison; this delivery does not
claim to close their existing proof holes.

## No longer needed

Removed the parent's proof-only imports `Sheaf.Paper.CartesianCoefficients`,
`Sheaf.Paper.CoefficientHeartClosure`,
`Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`, and
`Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`. The parent uses the
proved condensed localization API in `ContinuousConstructibleIntegralGluing` and
imports the proved factorization comparison. Coherence remains needed in the
new comparison module, so it is not globally pruned.

The original DAG dependencies `sk-prop-sfb-cartesian-coefficients`,
`det-lem-coefficient-heart-closure`,
`lem-weil-pbc-noetherian-open-subscheme-noetherian`,
`lem-weil-pbc-locally-noetherian-quasi-separated`, and
`det-sf-open-closed-sequence-ring-sheaf` are not applied by this proof.
Noetherian facts are supplied by Mathlib instances. The finite constant local
models are lisse by the refinement clause of common stratification, using the
original stratification as its own refinement. The obsolete parent `tool_uses`
entries for localization, the two Noetherian facts, and cartesian coefficients
are removed; the coherence approval is retained.

Removed the experimental core import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`;
Mathlib supplies the image-factorization facts used here. No blueprint unit
statement or proof step is bypassed.

The item also stops transitively importing the following modules (and their attached
nodes). Other target branches still import them, so no module leaves the entire
target import closure in this delivery.

| Module | Attached node |
|---|---|
| `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization` | `lem-sfb-coefficient-sections-localization` |
| `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel` | `det-def-sfb-constructible-local-model` |
| `Sheaf.CategoryTheory.ModuleObjects.LiftExact` | `det-prop-sfb-module-pullback-exact-lifted` |
| `Sheaf.CategoryTheory.SheafTensorClosed` | `det-def-sfb-sheaf-tensor-closed` |
| `Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis` | `lem-sfb-local-field-integral-basis` |
| `Sheaf.NumberTheory.Padics.PadicIntegersIntegralClosure` | `lem-sfb-padic-integers-integral-closure` |
| `Sheaf.Paper.CartesianCoefficients` | `sk-prop-sfb-cartesian-coefficients` |
| `Sheaf.Paper.CartesianCoefficientsFiniteFree` | `det-prop-sfb-cartesian-coefficients-finite-free` |
| `Sheaf.Paper.CoefficientHeartClosure` | `det-lem-coefficient-heart-closure` |
| `Sheaf.Paper.CondensedPointBasis` | `det-pe-condensed-point-basis` |
| `Sheaf.Paper.CondensedPointCoefficients` | `det-pe-condensed-point-coefficients` |
| `Sheaf.Paper.CondensedPointDiscreteConstantComparison` | `lem-pe-condensed-point-discrete-constant-comparisons` |
| `WeilConjectures.NumberTheory.Padics.IntegersFinite` | no attached node |

## Where the brief, the DAG or earlier work was wrong

The preserved report described an unfinished core and a net-zero decomposition.
The core is now fully proved, so that description no longer applies. Its
coefficient composition previously encountered universe constraints; explicit
universe choices and the fixed ring-sheafification instance resolve those.
The direct application of the ringed-site coherence theorem to internal `Mod`
functors was ill-typed. The proved operation comparisons and uniqueness of
adjoints now supply the required transport explicitly.

The original localization dependency uses arbitrary ring-module sheaves, whereas
the parent uses internal condensed modules. The existing condensed localization
API already proves the needed local cokernel facts, so no new localization theorem
is necessary. The remaining comparison is independent of stratifications,
constructibility, lisseness, cokernels, nesting, and endpoints.

## New nodes

`new-det-lem-coefficient-heart-filtration-core` records the proved mixed-factorization
comparison in `Sheaf.Paper.CoefficientHeartFiltrationCore`. Its source is the
localization/factorization paragraph of the filtration proof. Its node records the
actual coefficient-composition calculation, normalized factorization comparison,
and transport through section-module equivalences, with the existing dependency
nodes and the searches retained from the earlier attempt. The proof works for an
arbitrary commutative condensed ring, including the zero ring, empty sources, and
zero modules. No change record is needed because every existing signature and
public import remains unchanged.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
