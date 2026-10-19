## What changed

Added the proof-only import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension.
Proved AlgebraicGeometry.Etale.ExceptionalCoefficients.compactSupportMap_isIso
without changing its signature or any definition. Its proper scalarMate component
is invertible by properFiniteCoefficientExtension; the other factor is direct
image of openIso. The compactification scheme is Noetherian by finite type and
quasi-compactness over Y. Updated the owning node's proof and proof dependencies
for this auxiliary theorem. The existing unit route is retained. The new auxiliary proof step is appended
after the original ten steps so their numbered cross-references remain correct.

Validation: on resumption, the retained file compiled through lcompile.py in 10.2 seconds,
with no warnings or errors. The import-direction check confirms that the added dependency
does not create an import cycle. It has no lines over 100 characters. No new modules,
definitions, assumptions, or holes. The required delivery dry run is separate.

## Proved and sorry left

Closed one of the original five holes:
AlgebraicGeometry.Etale.ExceptionalCoefficients.compactSupportMap_isIso.
Added zero holes; this is a proof from an existing declared dependency, not a
new decomposition. The dependency properFiniteCoefficientExtension still has
its own existing sorry.

Four existing holes remain unchanged, all attached to
lem-pur-exceptional-coefficient-comparison:

- AlgebraicGeometry.Etale.ExceptionalCoefficients.tensorIso_existsUnique
- AlgebraicGeometry.Etale.ExceptionalCoefficients.siteTensorIso_existsUnique
- AlgebraicGeometry.Etale.ExceptionalCoefficients.unitIso_existsUnique
- AlgebraicGeometry.Etale.exceptional_coefficient_comparison

## No longer needed

Removed these unused proof imports from the item (their nodes remain in the
unfinished main theorem's proof plan; no claim that these nodes are globally pruned):

- Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullback
- Sheaf.AlgebraicGeometry.ConstructibleSurjectivePullback
- Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint
- Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
- Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
- Sheaf.AlgebraicGeometry.ProperProjectionFormula
- Sheaf.AlgebraicGeometry.SmoothTensorDuality
- Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
- Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
- Sheaf.Paper.KFlatRingedToposPullback
- Sheaf.Paper.RingedExchangeTensorCoherence
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
- WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
- WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

Public imports are unchanged. No entire node or module is proved unnecessary:
the main theorem remains open. The auxiliary
compactSupportMap_isIso no longer needs a new bounded-flat-model calculation or
finite totalization argument: the existing stronger proper coefficient theorem
already handles all inputs and nonflat coefficient maps. The main theorem still
needs its stated domain and coherence dependencies.

## Where the brief, the DAG or earlier work was wrong

The auxiliary compactSupportMap_isIso docstring planned to rederive proper
coefficient change on bounded flat models. The existing
lem-asd-proper-finite-coefficient-extension already states invertibility of exactly
its proper scalarMate factor, with no boundedness assumption. It is used as a
tool from the existing smooth-purity development; the maintainer may record the
corresponding tool-use approval if required.

Attempts to prove siteTensorIso_existsUnique by reflexive transport of the
representative-normalized tensor isomorphism exceeded the file timeout; those
attempts and diagnostic options have been removed. The unchanged module and the
completed compact-support proof both compile within the limit.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
