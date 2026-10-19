## What changed

Replaced the sorry in AlgebraicGeometry.ProEtale.classicalModule_weakSerre by the
blueprint argument. Private categorical helpers prove essential-image closure under
kernels and cokernels, degree-one derived vanishing, and extension closure using
the long exact sequence and the counit short five lemma. The existing
Scheme.proEtaleModuleEncoding identifies intrinsic constant-ring modules with
ModuleCat-valued sheaves, preserving underlying additive sheaves.

## Proved and sorry left

Closed: AlgebraicGeometry.ProEtale.classicalModule_weakSerre
(det-pe-classical-derived-weak-serre), one of one original holes.
Added: none. Remaining in delivered modules: none. No decomposition.
The resumed proof compiled cleanly through lcompile.py (9.2 seconds, exit 0).
Delivery and axiom-probe checks are run by deliver3.py.

## No longer needed

No new module or split is needed for the constant-ring encoding: the retained
attempt's ProEtaleModuleSheafConstantRingEquivalence is replaced by the already
proved Sheaf.Paper.ProEtaleConstantModuleEncoding. The retained candidate was never
in the shared repository and is not part of this delivery.
Removed direct imports:

- WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
- Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
- Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
- Sheaf.CategoryTheory.RingedSiteModules
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
- Mathlib.Algebra.Homology.DerivedCategory.Basic
- Mathlib.CategoryTheory.Abelian.RightDerived
- Mathlib.Algebra.Homology.ShortComplex.ShortExact

The finite-derived comparison, enough-injectives, derived-category, and site-comparison
APIs remain available through boundedBelowComparison. The direct
ProEtaleSiteComparison import is retained because the unit-route check requires it. Short-exact and right-derived
APIs come through FullLongExactSequence. RingedSiteModules is already a public
dependency of ClassicalContinuityMap. ProEtaleSmallModelComparison and its ringed-site
infrastructure are unnecessary: we use the fixed-module comparison and encoding.
The node lem-pur-ringed-site-grothendieck-abelian and its tool approval are removed
from the proof dependencies. Enough injectives comes from the fixed-coefficient sheaf
Grothendieck instance (lem-sfb-proetale-sheaves-grothendieck) and the Mathlib module
Grothendieck instance (lem-weil-pbc-ring-modules-grothendieck-abelian).
The proof no longer cites def-weil-sheaf-of-modules-category as a separate proof
dependency: extension closure is proved in the fixed-coefficient sheaf category
and transported through proEtaleModuleEncoding. The intrinsic module category
remains part of the statement, through ClassicalContinuityMap.
The main blueprint route is retained, including boundedBelowComparison.

## Where the brief, the DAG or earlier work was wrong

The stated module-category comparison uses ModuleCat-valued sheaves, whereas the
assigned conclusion uses intrinsic SheafOfModules over the constant ring sheaf.
The existing proEtaleModuleEncoding bridges these encodings. No statement or
definition is changed. The original seven-step mathematical argument is valid.
The proof docstring now describes the fixed-coefficient Grothendieck instance
and the encoding transport used by the Lean proof.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
