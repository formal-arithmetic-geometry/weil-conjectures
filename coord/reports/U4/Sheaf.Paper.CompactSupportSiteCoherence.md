## What changed

Filled `AlgebraicGeometry.ProEtale.compactSupportSiteCoherence` in
`Sheaf.Paper.CompactSupportSiteCoherence`. The proof uses the existing exchange transport
square for restriction, proves refinement compatibility by expanding the actual proper/open
construction on bounded-below objects, and identifies the recorded origin compositor with
its specified étale model using the fully faithful descent equations. The common-refinement
formula and the composition square follow by cancellation and naturality. Induction on
`CompactSupportSiteDiagram` then handles arbitrary finite diagrams and route equality.

The existing public declarations, definitions, signatures, public imports and docstrings
are preserved. All added helpers are private and proved. Local transparency controls and
abstract category cancellation lemmas avoid unfolding large derived functors during
simplification. No source-library file is changed, and no consumer adaptation is needed.
The coherence node's proof and proof dependencies now describe this route.
The complete module compiled cleanly through `lcompile.py` in 23.4 seconds;
the original public construction block and final theorem signature were compared verbatim.
The preflight-requested record for the added local transparency controls is
`coord/changes/compact-support-site-coherence-proof-elaboration.md`; it lists all 86
downstream modules and explains why no consumer adaptation is necessary.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProEtale.compactSupportSiteCoherence`
(node `lem-pur-compact-support-site-coherence`). Original item holes: 1. Item holes left: 0.
Added holes: 0. Split-off statements: 0. This is a proof from the library's named
comparison and exchange results; it introduces no new assumed statement.

## No longer needed

Removed these direct private imports:

- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`
- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.CategoryTheory.Adjunction.CoefficientExchange`
- `Sheaf.Paper.ComparisonPullbackExact`
- `WeilConjectures.Compactification.BaseChange`
- `WeilConjectures.Compactification.Refinement`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`

The refinement proof uses the existing canonical direct-image composition and the
explicit proper/open comparison; the composition proof uses the definition of the
recorded origin compositor. Thus the strict-tower normalization and compatible-tower
construction are not needed for this item's argument. The restriction proof uses the
already proved exchange transport square, so its internal coefficient mate and open
exchange calculations need not be repeated here. Comparison exactness and ordinary
compactification/base-change interfaces are available through the retained imports.

Removed these direct proof-dependency edges (not the nodes or their declarations):

- `cor-cbc-derived-extension-zero-base-change`
- `def-amb-etale-compact-support`
- `def-cbc-compact-support-square`
- `def-cbc-exchange-map`
- `def-cbc-finite-constant-coefficient-transport`
- `def-compact-support-direct-image-detailed`
- `def-weil-compactifications-refinements`
- `def-weil-finite-type-morphism`
- `lem-cbc-compactifiable-compatible-tower`
- `lem-cbc-extension-zero-base-change`
- `lem-cbc-extension-zero-composition`
- `lem-cbc-proetale-extension-zero-base-change`
- `lem-cbc-proetale-extension-zero-comparison`
- `lem-cbc-proper-open-interchange-coherence`
- `lem-cbc-strict-tower-proper-open-calculus`
- `lem-sf-comparison-pullback-exact`
- `lem-sf-proper-open-comparison-site-normalization`
- `lem-weil-pbc-coefficient-exchange-mates`
- `lem-weil-pbc-exchange-forget-coefficients`
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`

Withdrawn obsolete top-level `tool_uses` approvals, in their original order:

- `cor-cbc-derived-extension-zero-base-change`
- `lem-cbc-compactifiable-compatible-tower`
- `lem-cbc-extension-zero-base-change`
- `lem-cbc-extension-zero-composition`
- `lem-cbc-proetale-extension-zero-base-change`
- `lem-cbc-proetale-extension-zero-comparison`
- `lem-cbc-proper-open-interchange-coherence`
- `lem-cbc-strict-tower-proper-open-calculus`
- `lem-sf-comparison-pullback-exact`
- `lem-sf-proper-open-comparison-site-normalization`
- `lem-weil-pbc-coefficient-exchange-mates`
- `lem-weil-pbc-exchange-forget-coefficients`
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`

No module is physically withdrawn. These are dependencies no longer needed directly by
this proof; retained public imports and other consumers may still need their modules.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The former ten-step plan was longer than necessary for the definitions now in the
library. In particular, the canonical origin compositor is already defined by unique
fully faithful descent of the specified étale model. Its value on an étale witness
therefore follows from the two map-preimage identities, rather than requiring a fresh
strict-tower normalization argument. Likewise, the bounded-below refinement factors
reduce directly to the existing direct-image composition and naturality laws. This is
a change of proof route only, not a change of statement or of the actual pro-étale maps.

The old theorem docstring still records the original plan, preserved under the skill's
docstring rule; the updated DAG proof and the Lean proof give the route used here.

Server preflight conservatively classifies the new local transparency attributes as
interface commands and required the change record named above. These attributes remain
local; no public signature, definition body, or exported attribute is changed.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
