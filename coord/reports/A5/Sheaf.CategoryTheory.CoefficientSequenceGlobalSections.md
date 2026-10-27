## What changed

Proved `SheafOfModules.coefficientSequenceGlobalSectionsEvaluation` by constructing the
actual termwise restriction, deriving additive sections on coefficient modules and
constant-coefficient towers, descending the normalized evaluation and scalar comparisons,
and proving their compatibility with the actual strict-system transitions. Existing
public declarations, definitions, and public imports are unchanged. Private proof
helpers, including abstract localization and categorical cancellation calculations,
use the comparison-descent argument already proved in `TowerRightDerivedEvaluation`
and the exact-square factorization proved in `DerivedExactSquareComposition`.

Added `Sheaf.CategoryTheory.CoefficientRestrictionSectionsAcyclic`, proving scalar
restriction acyclicity on an essentially small site by transport to its small model.
Updated the item's DAG proof to match this argument. No source-library module is changed.

## Proved and sorry left

Closed 1 original hole and added 0 holes:
`SheafOfModules.coefficientSequenceGlobalSectionsEvaluation`
(`lem-coef-sequence-global-sections-evaluation`).

Added the proved theorem `SheafOfModules.coefficientRestrictionSections_quasiIso`
(`lem-coef-restriction-sections-acyclic`). No new holes. No `sorry` remains in either
sandbox module, including definitions and private helpers. The complete item compiled
cleanly in 58.7 seconds; the acyclicity module compiled in 44.3 seconds. The proof uses the existing
stated theorem `CategoryTheory.CoefficientDerivedSections.derivedSectionsScalarCoherence`
through its resolution-acyclicity clause; its pre-existing hole is unchanged.

## No longer needed

Removed these private imports from the item:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Sheaf.CategoryTheory.RingedToposMorphism`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.RestrictionRingedToposModuleDirectImage`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.ProperBaseChange.SingletonSiteModuleComparison`
- `Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`

The direct proof dependencies `lem-weil-pbc-small-module-diagrams-grothendieck` and
`prop-pur-kinjective-resolutions-exist` are replaced by the coefficient-universe
Grothendieck theorem, a separator argument for towers, and the existing Grothendieck
K-injective resolution theorem. The item no longer constructs a singleton-site
ringed-topos morphism or invokes general ringed-topos composition directly. Therefore
its obsolete `tool_uses` entries for the two preceding nodes and for
`lem-weil-pbc-restriction-ringed-topos-module-direct-image`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, and
`lem-weil-pbc-singleton-site-module-comparison` were removed. The existing scalar
coherence dependency still uses ringed-topos machinery; those modules are not withdrawn.
`KInjectiveTotalDerived` remains available through the tower-comparison dependency.
No module is withdrawn and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item permits independent presentation and coefficient universes and only assumes
that the site is essentially small in the coefficient universe. The stated scalar
coherence theorem uses a small site whose universe equals its coefficient universe;
it cannot be instantiated directly at the item's general site. The new proved lemma
transports precisely its needed acyclicity clause along a small-model site equivalence.
The original module-diagram Grothendieck and resolution lemmas likewise do not directly
supply the coefficient-universe instances at this generality. No statement is disputed
or weakened.

The launcher paused and resumed the session for compile-queue management; the resumed
reference metadata has start `1792769015.3129885`. This metadata was not edited by the
worker. Earlier timeouts were investigated by profiling and explicit comparison APIs.

## New nodes

`lem-coef-restriction-sections-acyclic` records the proved theorem
`SheafOfModules.coefficientRestrictionSections_quasiIso` in
`Sheaf.CategoryTheory.CoefficientRestrictionSectionsAcyclic`. It is the strictly smaller
resolution-acyclicity clause used to construct scalar comparisons, generalized to an
essentially small site. The proof transports module sheaves, scalar restriction,
K-injectivity, quasi-isomorphisms, and presheaf limits along a site equivalence, then
applies the existing small-site scalar-coherence theorem. Empty sites and zero rings
require no extra hypotheses. Change record: `coord/changes/coefficient-sequence-global-sections-proof-api.md`,
covering the private proof-interface commands; existing interfaces and non-theorem
bodies are unchanged.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
