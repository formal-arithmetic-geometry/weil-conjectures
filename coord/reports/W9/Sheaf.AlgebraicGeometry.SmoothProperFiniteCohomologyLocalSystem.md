## What changed

Proved `AlgebraicGeometry.Etale.finite_localSystem_higherDirectImage_smooth_proper` with its statement and public imports unchanged. The private affine helper applies compact-support constructibility, proper lower-shriek/direct-image comparison, and the existing module-valued smooth proper cospecialization theorem. Proper base change transfers the affine result to an arbitrary affine cover, where finite local constancy glues. The finite-module chart API converts both the input and output without losing linear structure.

Added `Sheaf.AlgebraicGeometry.ConstructibleCospecializationLocalSystem`, with a proved arbitrary-base constructible cospecialization criterion. Its proof generalizes the adopted source criterion by dropping an unused locally Noetherian base instance. The adopted source library is unchanged. Updated the item DAG proof and dependencies to match this route.

Validation: both sandbox modules compiled successfully through `lcompile.py --all`. The criterion uses affine spectral neighborhoods, constructible kernel/cokernel vanishing loci, and strict-localization lifting. Empty schemes, zero modules, disconnected bases and non-Noetherian affine bases require no additional assumptions. The proof even works for negative degrees, while the original nonnegative-degree signature is preserved.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Etale.finite_localSystem_higherDirectImage_smooth_proper` (node `lem-sfb-smooth-proper-finite-cohomology-local-system`).

Added 0 holes. The new public theorem `AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_of_constructible_bijective_cospecialization` (node `lem-sfb-constructible-cospecialization-local-system`) and its private neighborhood helper are proved. The private affine helper in the item is proved. No `sorry` remains in either delivered module. No decomposition into unfinished lemmas.

## No longer needed

The following private imports are removed from the item:

- `Sheaf.AlgebraicGeometry.PullbackConstantModule`.
- `Sheaf.SixFunctors.ProperBaseChangeModules`.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyConventions`.
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`.
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`.
- `Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteStalkSpecializationCriterion`.
- `WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
- `WeilConjectures.AlgebraicGeometry.ProperNoetherianStage`.
- `Sheaf.AlgebraicGeometry.DescendSmoothQcqs`.
- `Sheaf.AlgebraicGeometry.FiniteLocalSystemAffineLimitDescent`.

The following original proof dependencies are unused by this route. These are removals from this item, not assertions that no other target or preserved upstream proof needs them:

- `lem-kun-pullback-constant` (`Sheaf.AlgebraicGeometry.PullbackConstantModule`).
- `lem-pe-constant-left-module-inverse-image` (`Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`).
- `def-weil-proper-morphism` (`Mathlib.AlgebraicGeometry.Morphisms.Proper`).
- `def-sbc-smooth-morphisms` (`Mathlib.AlgebraicGeometry.Morphisms.Smooth`).
- `def-weil-pbc-scheme-conventions`.
- `det-pbc-conventions-module-cohomology` (`Sheaf.AlgebraicGeometry.ModuleCohomologyConventions`).
- `lem-weil-pbc-inverse-image-stalk-germ` (`WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`).
- `lem-weil-pbc-constant-sheaf-geometric-stalk` (`WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`).
- `lem-weil-pbc-etale-finite-stalk-specialization-criterion` (`Sheaf.AlgebraicGeometry.EtaleFiniteStalkSpecializationCriterion`).
- `lemma-nagata-ring-finite-type-subalgebras` (`WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`).
- `lemma-nagata-noetherian-inverse-system-affine` (`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`).
- `def-nagata-noetherian-inverse-system` (`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`).
- `lem-weil-pbc-proper-noetherian-stage` (`WeilConjectures.AlgebraicGeometry.ProperNoetherianStage`).
- `lem-weil-pbc-descend-smooth-qcqs` (`Sheaf.AlgebraicGeometry.DescendSmoothQcqs`).
- `lem-weil-pbc-scheme-over-limit` (`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`).
- `lem-sfb-finite-local-system-affine-limit-descent` (`Sheaf.AlgebraicGeometry.FiniteLocalSystemAffineLimitDescent`).

The Noetherian approximation, eventual smoothness and finite-local-system descent chain is unnecessary because constructibility is already available over arbitrary affine bases and the proved constructible criterion works there. Explicit finite-stalk and underlying-abelian-sheaf comparisons are replaced by the intrinsic constructible and module-valued cospecialization APIs. Properness and smoothness remain statement assumptions; their definition nodes remain in statement dependencies. No modules or upstream declarations are deleted.

Removed obsolete top-level `tool_uses` approvals (the surviving entries retain their order):

- `lem-kun-pullback-constant`.
- `lem-pe-constant-left-module-inverse-image`.
- `lem-weil-pbc-inverse-image-stalk-germ`.
- `lem-weil-pbc-constant-sheaf-geometric-stalk`.
- `lem-weil-pbc-etale-finite-stalk-specialization-criterion`.
- `lemma-nagata-ring-finite-type-subalgebras`.
- `lemma-nagata-noetherian-inverse-system-affine`.
- `lem-weil-pbc-proper-noetherian-stage`.
- `lem-weil-pbc-descend-smooth-qcqs`.
- `lem-weil-pbc-scheme-over-limit`.

## Where the brief, the DAG or earlier work was wrong

The nine-step DAG plan imposed a Noetherian base only to invoke the finite-stalk specialization criterion, then introduced a Noetherian approximation and descent argument to remove it. The existing source specialization proof actually uses constructibility to shrink through affine spectral neighborhoods. Its locally Noetherian base instance is unused after omitting the unused local Noetherian instance. This gives the shorter proved criterion under the stronger constructibility hypothesis already established for the higher direct image. This is a proof-route simplification below the blueprint unit, not a false-statement repair. The item statement, all definitions, and the unit route remain unchanged.

The direct source module `SmoothProperLocallyConstant` supplies a module-valued specialization API without the finite-type-over-a-field hypotheses of its final corollary. Using that API avoids the abelian/module comparison detour.

## New nodes

`lem-sfb-constructible-cospecialization-local-system` records the arbitrary-base criterion proved in `Sheaf.AlgebraicGeometry.ConstructibleCospecializationLocalSystem`. It is strictly an independent local-constancy criterion for a constructible sheaf, not a restatement of smooth proper cohomology. The proof spreads a finitely presented stalk, identifies the resulting stalk maps with cospecialization, shrinks using constructible kernel/cokernel vanishing loci on an affine neighborhood, then forms an etale cover. LeanSearch, LeanFinder and Mathlib grep found no existing Mathlib theorem; the blueprint search found no duplicate. The existing Noetherian finite-stalk criterion remains untouched. No change records are required: no existing signature or definition is changed.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
