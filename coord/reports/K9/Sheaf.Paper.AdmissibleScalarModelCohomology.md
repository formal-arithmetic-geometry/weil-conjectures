## What changed

Proved the assembly of `AlgebraicGeometry.ProEtale.AdmissibleScalarModel.admissible_scalar_model_cohomology` from one strictly smaller geometric flatness bridge. The statement and all existing definitions are unchanged.

Private proof-local caches reuse the existing monoidal structures on the profinite and scheme sheaf categories, avoiding repeated expensive instance reconstruction without changing public definitions. The private helpers construct an exact equivalence from internal scalar modules to ordinary modules over the existing reconstructed scalar ring. Noetherian kernels and quotients give finite presentation of cohomology. Finite presentations are transported back as actual finite-free cokernels. The exact-functor natural homology isomorphism and identity cover give the finite constant local models.

For finite coefficients the proof reuses the proved normalized canonical scalar-map isomorphism in `FiniteDiscreteScalarConstantModels`, then uses the extension equivalence for the unit. Integral exactness uses the proved point-counit exactness and composition comparison in `PadicConstantLocalModelTor`. Field exactness is proved by splitting every short exact sequence of vector spaces, including for the actual finite-subextension-valued algebraic closure. Scalar ring isomorphisms transfer Noetherianity. The ring-of-integers PID instance already exists in the adopted source library.

Added `Sheaf.Paper.ScalarCounitFlatPullback`, which isolates the inverse-image flatness comparison for the canonical scalar counit. It includes the actual counit and proved monoidal/commutative instances. Its single theorem remains to be proved from the existing generic flat pullback and section-module equivalence APIs. This theorem concerns one flat algebra module under inverse image, with no cohomology, finiteness, field, or admissibility conclusion.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.AdmissibleScalarModel.admissible_scalar_model_cohomology` (node `lem-sfb-admissible-scalar-model-cohomology`). There are zero holes in the assigned module.

Added one hole: `AlgebraicGeometry.ProEtale.scalarCounit_flat_pullback`, node `lem-sfb-scalar-counit-flat-pullback`, in `Sheaf.Paper.ScalarCounitFlatPullback`. Its docstring and node contain the complete proof in words and exact canonical-module comparison required. This is a decomposition, not a net hole reduction: one original hole closed, one strictly smaller hole added. No definition contains a hole. Every private helper is proved. Both modules compiled with `lcompile.py`; the assigned file compiled in 37.8 seconds after caching the existing monoidal structures, and the new module in 37.0 seconds. The delivery tool performs the final compile and axiom/preflight checks.

## No longer needed

Removed proof imports:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Mathlib.RingTheory.PrincipalIdealDomain` (available through the reused proved coefficient argument)
- `Sheaf.Paper.TotallyDisconnectedCoefficientRealization`
- `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`
- `Sheaf.Paper.ConstantToContinuousScalarFlat`
- `Sheaf.CategoryTheory.InternalSectionModuleFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat`
- `Sheaf.Algebra.Homology.FlatScalarRealization`
- `Sheaf.Algebra.Homology.FlatScalarRealizationExact`
- `Sheaf.CategoryTheory.DerivedCategory.ScalarPerfectCohomologyAndPidModels`

The assigned proof does not use `lem-weil-l-adic-extension-integers-dvr`: the existing source-library `PadicAlgCl.isPrincipalIdealRing_integers` supplies the exact integral PID instance. It does not use `lem-exc-constant-field-module-flat`, `def-sfb-flat-scalar-realization`, `lem-sfb-flat-scalar-realization-exact`, or `lem-weil-pbc-scalar-perfect-cohomology-and-pid-models`: splitting over fields, exactness on the point, and Noetherian kernels/quotients replace these routes. It does not directly need the separate site-derived constant-functor node or totally-disconnected realization node: the normalized canonical finite scalar-map comparison already proves the needed map is invertible.

The generic flat-pullback, internal/section flatness, point pullback and constant inverse-image nodes remain dependencies of the new geometric bridge; they are not claimed globally pruned. The constant-to-continuous PID flatness mathematics is reused through the proved helpers in `PadicConstantLocalModelTor`; the separate `lem-sfb-constant-to-continuous-scalar-flat` node is no longer a direct dependency of the assigned node. All old `tool_uses` approvals are removed from the assigned node because its proof no longer directly uses them; the generic flat-pullback dependencies remain in the new bridge. Existing public imports are retained verbatim, so this delivery does not alter downstream visibility. No source-library declaration or module is withdrawn. No global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan used more machinery than the cohomology conclusion needs: finite generation of terms over a Noetherian ring suffices, and split exact sequences suffice for all field coefficients. The finite canonical scalar-map normalization and integral point-counit exactness have already been proved in other modules, so rebuilding them is unnecessary. The remaining difficulty is constructing the explicit algebraic inverse-image/section-module comparison needed to apply the general flat pullback theorem to the actual canonical scalar action. This is stated separately rather than hidden in the cohomology proof.

Edge cases checked: finite zero ring, empty scheme and identity cover, zero and torsion cohomology, degrees outside the bounded interval, zero-dimensional vector spaces, and the finite-subextension condition in the algebraic-closure coefficient. The unit record's realized fields impose no additional bypassed statement or step; the blueprint local-model cohomology route is preserved.

## New nodes

`lem-sfb-scalar-counit-flat-pullback` records the flatness bridge for the actual counit and scalar map, with source Stacks Tag 05VD, its full proof plan, the existing generic dependencies, the Lean statement, and recorded LeanSearch/LeanFinder/Loogle/source searches. A whole-blueprint search found no duplicate. No existing statement or definition was changed; no change record is required.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
