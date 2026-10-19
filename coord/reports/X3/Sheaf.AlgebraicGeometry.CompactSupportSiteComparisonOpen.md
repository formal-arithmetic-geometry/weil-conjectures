## What changed

Proved both original theorems in
`Sheaf.AlgebraicGeometry.CompactSupportSiteComparisonOpen` without changing their
signatures or the two existing exchange definitions. The private `paste_exchange`
calculation combines the proper and open factor equations using naturality and
functoriality. It never cancels an exchange.

Three new modules expose the factor equations, all proved in this delivery:
`CompactSupportProperFactor`, `CompactSupportOpenFactor`, and
`OpenSiteEvaluationCounit`. The proper factor restricts the existing
`comparison_square` and its exact-derived normalization to D+, then applies a
proved generic adjunction cube calculation and the existing canonical mate counit
equations. The proof imports the normalization module with `import all` to use its
existing, fully proved private `square_exact` calculation; it does not copy or
change that module. The open factor identifies the underived pushforward-square mate with
the pullback-square mate and restricts `fixSiteOpenExchange` to D+. The evaluation
counit follows from `openComparison_unit_normalization`, exact derivation and the
adjunction triangle identities.

All four modules compiled successfully through lcompile.py against the current
published build in this session (2026-10-19): open factor 8.7 s, proper factor
16.1 s, evaluation counit 11.6 s, and original item 1.6 s. No existing signature, visibility,
public import, target statement or definition changes. Only proof imports change
in the original module. New modules use private, proved helpers; no definition or
helper contains a hole. The required delivery preflight also checks their axioms.

## Proved and sorry left

Original holes closed: 2 of 2:

- `AlgebraicGeometry.ProEtale.compactSupportSiteComparison_open`.
- `AlgebraicGeometry.ProEtale.compactSupportSiteComparison_open_counits`.

Holes added: 0. Sorries remaining in all four delivery modules: 0.

The three new public theorems are also proved:
`AlgebraicGeometry.ProEtale.compactSupportProperFactor`,
`AlgebraicGeometry.ProEtale.compactSupportOpenFactor`, and
`AlgebraicGeometry.ProEtale.openSiteEvaluationCounit`. They use existing named
library declarations, including the canonical direct-image counit normalization;
this is a proof relative to those existing declarations, not a claim that their
transitive dependencies are all sorry-free.

The two factor equations concern independent proper and open squares; their
combination is a real naturality calculation. The proper cube proof uses no
invertibility of either exchange. Identity squares, empty opens, zero inputs and
the zero ring satisfy the same adjunction identities.

## No longer needed

Removed these direct proof imports from the item module:

- `Sheaf.AlgebraicGeometry.FixSiteOpenExchange`: used inside the proved open factor.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`: its API is already
  public through `CanonicalCompactSupportSiteComparison`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`: the proper factor
  uses the existing derived `comparison_square` instead.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: already
  available through the existing public imports.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: already public through
  `CanonicalCompactSupportSiteComparison`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: already
  available through the existing public imports.
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`: the proper
  factor uses the pullback-only `ComparisonSquare` and its normalization, followed
  by the proved generic mate cube; no proper/smooth base-change theorem is needed.

No module is withdrawn; no transitive module pruning is claimed. No public import
is removed. The original node's direct proof dependencies now name the proved
factor equations and the direct-image normalization. Its obsolete direct
`tool_uses` entries removed are `lem-weil-pbc-transport-identifies-exchange`,
`lem-fix-site-open-exchange`, `lem-sf-comparison-pullback-exact`,
`lem-weil-pbc-exact-functor-bounded-below`,
`lem-weil-pbc-extension-by-zero-exact`, and
`lem-weil-pbc-comparison-pullback`. Open exchange and exactness remain used where
required in the factor proofs; the unbounded proper-exchange transport statement
is replaced by the direct D+ mate calculation.

## Where the brief, the DAG or earlier work was wrong

The retained report said `FixSiteOpenExchange` and
`OpenComparisonUnitNormalization` were absent. Both exist in the current sources
and are used. The ambient proper-exchange transport theorem uses total derived
functors and does not directly match this D+ equation. Restricting the existing
pullback-only comparison square, then proving compatibility of its mates, resolves
that presentation mismatch. No statement is disputed or weakened. The blueprint
unit route through proper and open factors and their counit normalization is kept.

## New nodes

`lem-amb-compact-support-proper-factor`, module
`Sheaf.AlgebraicGeometry.CompactSupportProperFactor`, is proved. Its proof first
normalizes the pullback square on D+ and then uses the generic mate cube and the
canonical direct-image counit equations.

`lem-amb-compact-support-open-factor`, module
`Sheaf.AlgebraicGeometry.CompactSupportOpenFactor`, is proved from the existing
site/open exchange and canonical mate identities.

`lem-amb-open-site-evaluation-counit`, module
`Sheaf.AlgebraicGeometry.OpenSiteEvaluationCounit`, is proved from the existing
unit normalization, exact derived compatibility and adjunction triangle identities.

All nodes have sources, complete proofs in words, recorded searches and matching
Lean signatures. This session repeated LeanFinder, Loogle and grep searches; no
site-specific replacement was found. Retained unsupported LeanSearch records were replaced with actual LeanSearch
queries from 2026-10-19; the hits include the generic mate identities used above. No definition or statement change record is needed.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
