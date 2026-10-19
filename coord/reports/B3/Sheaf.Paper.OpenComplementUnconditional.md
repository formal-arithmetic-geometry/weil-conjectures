## What changed

Completed all four existing proofs in Sheaf.Paper.OpenComplementUnconditional without changing their signatures. The general assertion combines the published direct-image constructibility input with the published torsion direct-image dimension bound. The proof explicitly transports constructibility along the bounded-below/unbounded derived-functor compatibility, and handles negative degrees using left t-exactness. The finite-stage proof checks the characteristic and proves ell^n kills the actual coefficient quotient using its chosen uniformizer. The affine-chart proof uses Mathlib's Noetherian polynomial dimension formula; the empty-chart proof specializes the finite-stage theorem at dimension bound zero. Updated the existing node to match these proofs.

The item compiles without errors or warnings (20.8 seconds). Validation: the delivered module compiled without warnings. The direct consumers Sheaf.Paper.FiniteCoefficientHomChange (10.0 seconds) and Sheaf.Paper.PurityAffineChartBounds (5.5 seconds) compiled against the delivered module. Sheaf.Paper.FiniteTorStability could not be checked: three attempts (including the resumed-session retry) stopped at its imports with missing shared artifact WeilConjectures.Compactification.RefinementCategory.olean, before elaborating any declaration. No consumer source was changed. Public-import pruning is recorded in coord/changes/B3-open-complement-import-pruning.md; no definitions or declaration signatures change.

## Proved and sorry left

Closed all 4 original holes, by declaration name:

- AlgebraicGeometry.Scheme.hasOpenComplementCondition_of_isSepClosed
- AlgebraicGeometry.Scheme.hasOpenComplementCondition_finiteStage
- AlgebraicGeometry.Scheme.hasOpenComplementCondition_affineChart
- AlgebraicGeometry.Scheme.hasOpenComplementCondition_emptyChart

There are zero sorry occurrences left in the item, zero new holes, zero split-off statements, and no new declarations. This proves the item from its named dependencies; it does not claim those dependencies are themselves sorry-free. In particular the existing hasDirectImageFinitenessInput_of_isSepClosed remains a separate stage-3 item.

## No longer needed

Removed imports (the constructibility import was duplicated in the original header, and both occurrences are removed):

- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
- Mathlib.Algebra.Homology.DerivedCategory.TStructure
- Mathlib.RingTheory.Spectrum.Prime.Noetherian
- Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
- Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral
- Sheaf.AlgebraicGeometry.DerivedCategories
- Sheaf.AlgebraicGeometry.DirectImageFinitenessInput
- Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
- Sheaf.AlgebraicGeometry.OpenComplementKnown
- Sheaf.Paper.FiniteFieldFiber
- WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
- WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
- WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
- WeilConjectures.SixFunctors.Etale.Derived.Coefficients
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

Mathlib.AlgebraicGeometry.Noetherian is retained as a proof-only import instead of a public import. All newly added imports are proof-only.

Former proof dependencies not needed as separate inputs:

- def-weil-open-immersion
- def-weil-pbc-direct-image
- lem-exc-open-complement-known
- lem-kun-dimension-finite-type
- lem-pqf-finite-affine-cover-qc-open
- lem-weil-pbc-lft-affine-pairs
- lem-weil-pbc-module-sheaves-grothendieck-abelian

Finite affine covers and the affine-pairs criterion are replaced by existing finite-type composition/Noetherian instances. Existence of a natural dimension bound is unnecessary because all four statements already receive the required bound or prove it directly. The source-library module-sheaf instances suffice for negative-degree vanishing, so the separately stated ringed-site Grothendieck result is unused. OpenComplementKnown and CurveOpenDimensionGeneral are independent low-dimensional computations, not inputs. No whole-library pruning count is claimed: other parents may still reach these modules. Obsolete tool_uses entries corresponding to these removed dependencies are deleted in their original order.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. The planned proof omitted the explicit bounded-below/unbounded derived-functor comparison and constructibility-predicate comparison needed for the published Lean interfaces; the existing source-library results fill both gaps. The empty-chart case follows from the general finite-stage theorem at d = 0, so no separate theorem about sheaves on the empty site is needed. The preserved unit route still goes through open-complement constructibility and vanishing and its affine-chart specialization.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
