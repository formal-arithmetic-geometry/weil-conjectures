## What changed

Filled the coefficient and normalization theorems in
`Sheaf.Paper.SupportedCupFunctoriality`, without changing any existing public
signature or definition. The private helpers establish the monoidal unit
normalizations, finite closed base change, transport through site comparison,
and the kernel comparison between short exact sequences. The pro-etale source
sequence is the exact comparison image of the etale open-closed sequence; the
open comparison is normalized by the recorded adjunction unit equation and the
triangle identities. No quasi-compactness assumption on the complement is added.

Added private proof imports for the existing finite base-change theorem,
pro-etale disjoint-support vanishing, the monoidal constant-pullback normalization,
etale inverse-image coherence, closed-source site comparison, and
`Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization`:

- `WeilConjectures.SixFunctors.Finite.BaseChange`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`
- `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`
- `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar`
- `Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization`

Recorded `sk-lem-pbc-finite`, `lem-sfb-proetale-open-disjoint-direct-image`, and
`lem-sf-open-comparison-unit-normalization` in the relevant proof steps of
`lem-pur-supported-cup-functoriality`. Local reducibility
annotations are confined to proof sections; the public instances and definitions
retain their original bodies and attributes.

The visible-command checker requires the elaboration context to be recorded in
`coord/changes/P9-supported-cup-functoriality-proof-context.md`. Its consumer table
lists all sixteen transitive importers; none requires adaptation.

## Proved and sorry left

Closed 12 of the 13 original holes, all in namespace
`WeilConjectures.PurityFiniteSetting`:

- `functorialCupCoefficient_isIso`
- `functorialCupExchange_existsUnique`
- `functorialCupSupportMap_existsUnique`
- `functorialCupFrameTwistEtale_eq`
- `functorialCupFrameTwist_eq`
- `functorialCupSequence_zero`
- `functorialCupSequence_shortExact`
- `functorialCupOpenExchange_existsUnique`
- `functorialCupComparisonSource_existsUnique`
- `functorialCupComparisonTwist_eq`
- `functorialCupComparisonConstant_eq`
- `functorialCupComparisonOpen_existsUnique`

One original hole remains unchanged:
`WeilConjectures.PurityFiniteSetting.supportedCupFunctoriality`, node
`lem-pur-supported-cup-functoriality`. Its graded algebra, Kummer, localization,
and comparison-law assembly is not claimed proved here. Added holes: zero.
Split-off statements: zero. Every new private helper is proved.

## No longer needed

None. No imports, modules, or DAG dependencies are withdrawn. The remaining
assembly theorem still needs the tensor-calculus and Kummer parts of its plan.
The closed-source comparison subproof uses the existing finite base-change
isomorphism directly instead of reconstructing it on sections, but this does
not prune the section-comparison dependencies of the remaining theorem.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The selected derived monoidal instance obtains its
braiding through `functorialCupSymmetric`; the coefficient proof must use that
same instance. Specializing the Boolean parameter also makes instance search
choose a site-specific localization lax structure, whereas the public statement
uses the generic structure. The proved generic helper is instantiated with a
private alias selected before specialization, so both sides use the identical
localization structure. No public definition is changed.

The stated shifted tensor-calculus dependency is expressed for intrinsic
`SheafOfModules`, whereas this module uses fixed-scalar `ModuleCat`-valued
sheaves. The remaining assembly needs a compatible monoidal and derived
comparison between these presentations, including the prescribed shift sign.
No unproved bridge or renamed assembly theorem is introduced in this packet.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
