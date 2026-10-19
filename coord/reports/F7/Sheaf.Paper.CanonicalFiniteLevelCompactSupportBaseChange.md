## What changed

Replaced the sole hole in `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`
with the direct proper/open argument. The fixed witness gives `plusEtaleOrigin`.
The existing proved source lemma
`isIso_derivedBaseChangeMap_app_openImmersionLowerShriek_of_compactification`
handles the proper factor after extension by zero. The abstract proved lemma
`NatTrans.isIso_app_comp_whiskerLeft_comp` combines it with the two isomorphisms
already present in the definition of the actual canonical exchange.
The three public imports and the existing theorem signature are unchanged.
Added the proof-only import
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange`.
The node's new last proof step records the fixed-module argument; its original
steps still describe the reexported global interface.

Validation: the resumed `deliver3.py --no-push` run passed compilation and
preflight at dry-run commit `b4b5972b9b` (2026-10-19), with no compiler warning.
The review class is CODEX because the existing DAG proof plan changes and a
redundant direct import of a unit-route module is removed. In particular,
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel` remains imported by
the publicly imported `Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange`;
its unit route is retained. The theorem signature is unchanged; every Lean line
is at most 100 characters. Import-direction checking passed. LeanFinder returned
no relevant Mathlib result; source search found the exact proper-factor lemma.

## Proved and sorry left

Closed `AlgebraicGeometry.ProEtale.isIso_csAuxiliaryExchange`
(node `thm-cbc-finite-level-proetale`) from the existing proper-factor theorem.
Original holes: 1. Holes closed: 1. Holes remaining in the item: 0. Holes added: 0.
No new theorem or split-off is added.
The imported source proper-factor lemma is proved, and the argument does not
use that module's still-holed compact-support theorem.

## No longer needed

Removed these direct proof imports from the current shared module:

- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.Compactification.BaseChange`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`

The proof does not use the coherence theorem for compositions of etale open
extension, the pro-etale extension-zero scalar/stalk theorem, or coherence of
upper/lower star beyond the existing proper-factor theorem. The global exchange,
its witness-independence proof and its compactification-independence proof are
unneeded for the auxiliary clause. Their modules and original DAG dependencies
remain needed by the unchanged reexported global interface, so no entire node or
module is claimed pruned. No public import is removed.

## Where the brief, the DAG or earlier work was wrong

The docstring suggests identifying the entire transported global exchange.
For the actual auxiliary component this is unnecessary: its definition already
exhibits the proper/open composite and the existing source proper-factor theorem
applies directly to the retained fixed-module witness. The DAG lacked a separate
step recording this auxiliary proof, which is now appended without changing the
global interface's plan. No statement or definition repair is made.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
