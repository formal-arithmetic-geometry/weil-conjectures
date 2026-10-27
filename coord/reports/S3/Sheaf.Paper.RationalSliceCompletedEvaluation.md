## What changed

Partial proof delivery for Sheaf.Paper.RationalSliceCompletedEvaluation.
Preserved every existing declaration signature, public import, definition and docstring.
Proved exactness by the four option-index cases, specializing the existing
independent-universe slice/relocalization API. Derived additivity follows from
preservation of binary products. Three proved private helpers identify the scalar
endomorphisms on complexes and after localization; their sectionwise formulas and
fully faithful localization prove derived linearity. Tensor induction in both Hom
inputs proves the scalar-localized identity and composition laws.

Added the private proof import Sheaf.Algebra.Homology.SitePerfectModelRestriction.
Scoped transparency options apply only to individual proof declarations. Updated
step 1 and step 10 of the existing node to record the implemented arguments and
their dependencies; kept all outstanding steps and the unit route.

Validation: the complete delivered module compiled through lcompile.py, exit 0,
45.0 seconds, after removal of unused direct proof imports. The delivery preflight
also compiles its axiom probe.

## Proved and sorry left

Closed four of eight existing holes (names in WeilConjectures.IntegralOnSlice):

- restrictionModules_exact
- restrictionDerived_additive
- restrictionDerived_linear
- restrictionRationalHom_laws

Added zero holes. Four existing holes remain, each attached to
lem-sf-rational-slice-completed-evaluation and retaining its source and full proof
docstring:

- restrictionCompletion_bijective
- restrictionHom_complete
- restrictionComplete
- rationalSliceCompletedEvaluation

The final comparison theorem is still unproved. In particular the quotient
completion/reflector identification, the normalized comparison family and its
coherence are not supplied by this delivery. The four closed declarations may
still depend transitively on earlier library holes; this is not a claim of
axiom-free completion of the full target.

## No longer needed

Removed unused direct private proof imports:

- Sheaf.CategoryTheory.LocalizedModuleExactIndependent
- Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
- WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
- Sheaf.Paper.IntegralOperationsWellDefined
- Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Sheaf.Paper.CompletedConstantSheafReduction
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
- Sheaf.CategoryTheory.RingedCechKoszulDualLimit
- Sheaf.Paper.ExtendedCechCompletionModel
- Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
- Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
- Sheaf.CategoryTheory.LocalizedModuleExactForSystems
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

These imports were unused by the definitions and the four implemented proofs.
This is direct-import cleanup only: the corresponding completion and comparison
nodes remain in the final theorem's proof plan, and some modules remain reachable
through public/transitive imports. No module is withdrawn, no dependency needed
by an unfinished proof is declared obsolete, and no unit step is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The generic derived linearity
instance cannot directly establish the desired action: RationalThickEvaluation
selects its linear structure from the constant-section scalar endomorphisms.
The proof therefore compares those specific endomorphisms before applying the
chosen linear structure's specification.

The existing DAG exactness step can use the already proved independent-universe
slice and relocalization lemmas directly. Its additional product-preservation
argument remains needed for the unfinished completeness/comparison proofs.

Searches performed through msearch.py: LeanFinder on exact additive slice
restriction (eight hits, including over); Loogle on Functor.mapDerivedCategory
(unknown identifier); grep on overMap_exact_ofUniverses and
mapDerivedCategory.Linear (the Mathlib linearity instance). Local rg located
SitePerfectModelRestriction and verified its declarations and universe parameters.
The generic Cech reflector uses a SmallCategory and does not itself identify the
specified quotient-completion functor and unit on these independent-universe
slice sites; that comparison is still outstanding.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
