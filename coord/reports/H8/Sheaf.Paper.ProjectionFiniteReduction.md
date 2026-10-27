## What changed

Retained the earlier H8 proof attempt and checked it against current sources. The public
statements and definitions of `Sheaf.Paper.ProjectionFiniteReduction` are unchanged.
The factor-coordinate obligation prepares fixed etale-origin witnesses from the existing
witnessed-flat-domain lemma, applies the proper/open identities and transports their
presentations. The main proof pastes these separate equations using a proved categorical lemma. The single-level invertibility obligation
transports the proved finite-ring compact-support projection theorem to the normalized
models. The main proof uses it at both levels, with finite-Tor stability under quotient.
New helper modules are `ProjectionFactorCoordinates`, `ProjectionScalarSquare`, and
`FiniteProjectionPresentation`. All four modules compile. The completed main proof takes 12.9 seconds in the
server compile result before final warning cleanup.

## Proved and sorry left

Closed the original item's one hole, `WeilConjectures.projectionFiniteReduction`, by
a complete Lean combination of the smaller obligations. Two strictly smaller obligations remain:
`WeilConjectures.PurCompactSupport.projection_factor_coordinates`
(node `lem-sf-projection-factor-coordinates`) and
`WeilConjectures.PurCompactSupport.finiteProjectionPresentation_isIso`
(node `lem-sf-finite-projection-presentation`). The scalar-square pasting theorem `WeilConjectures.PurCompactSupport.projection_scalar_square`
compiles without sorry (node `lem-sf-projection-scalar-square`).
This is a decomposition, not a net hole reduction.

## No longer needed

The retained proof removes the direct private imports of
`Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`,
`Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`,
`Sheaf.Paper.ComparisonTorAmplitude`, `Sheaf.Paper.FiniteCoefficientFlatModel`,
`Sheaf.SixFunctors.OpenTensorNormalization`, `Sheaf.Paper.ProEtaleConstructibleOrigin`,
`Sheaf.Paper.OpenExtensionFiniteTor`,
`Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`,
`Sheaf.Paper.RingedExchangeTensorCoherence`,
`WeilConjectures.Compactification.NagataCompactification`, and
`Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula`.
Also removed the attempt's direct proof imports of
`Sheaf.Paper.FiniteRingCompactSupportProjection`, `Sheaf.Paper.FiniteMateDomain`, and
`Sheaf.SixFunctors.OpenScalarTensorNormalization`; the relevant finite-ring and
normalization arguments are recorded inside the two remaining helper obligations.
Their arguments remain available through the existing witnessed-domain/proper-open
children or the proved finite-ring compact-support projection theorem. No source-library
declaration or unit realization is withdrawn. No whole-module pruning is asserted.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped on a server disk-space error, leaving no report or node
records for its three helper modules. The server now compiles all four modules.
The retained factor-coordinate file had a broken line break before field notation and
an unwanted competing IntegralHom derived-category instance; these are repaired. The retained `rfl` projection-factor equalities were invalid:
`projectionComparisons_existsUnique` chooses data whose components are fixed by fields,
not definitionally. The proof now uses `openProjection_eq`, and explicitly presents
compact support as proper pushforward after open extension. Final naturality and
tensor functoriality complete the pasting proof.
The latest blueprint changes the general statement to same-ring ideal reduction, whereas
the existing item and unit still state coefficient-ring reduction. The item's signature
is preserved; the proof uses the same proper-counit/open-unit route.

## New nodes

`lem-sf-projection-factor-coordinates`: prepare the existing witnessed domains and proper/open
identities, then transport the two equations to the given intrinsic finite-Tor inputs and
normalized tensor presentations. It asserts neither the compactification square nor invertibility.

`lem-sf-finite-projection-presentation`: single-level invertibility in normalized intrinsic
models, obtained from the existing finite-ring theorem and a counit/open-unit presentation
comparison. It contains no reduction compatibility or equivalence between two levels.

`lem-sf-projection-scalar-square`: categorical pasting of separate proper/open identities.
Its proof uses naturality, functoriality and the existing scalar-mate factorization.

Searches: LeanFinder, Loogle and Mathlib grep found no matching projection presentation
lemma; LeanSearch returned general naturality statements rather than the required
constant-ring derived projection comparison. All searches are recorded in the sandbox.

Edge cases checked: m=n uses the identity quotient; zero objects and empty schemes
use the same naturality and equivalence equations; no scalar-flatness assumption is
used, so a quotient from length two to length one is covered. Arbitrary normalized
tensor models may differ by a presentation automorphism: all tensorators are transported
with that same model, so both sides are conjugated coherently.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
