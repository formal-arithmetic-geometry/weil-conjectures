## What changed

Replaced the single anonymous hole of `AlgebraicGeometry.ProEtale.integralTensorProduct`
by a complete assembly without changing its signature or its existing point-adjunction instance.
The chart proof uses finite sums of units, the source-library theorem for bounded complexes of
dualizable objects, and pro-etale descent of dualizability. The tensor adjunction proves
preservation of products of arbitrary index universe. The native triangulated tensor and
`IsHomotopyLimit.map` prove preservation of the complete Milnor cone.

Separated the original constructibility clause into `Sheaf.Paper.IntegralTensorConstructibility`
and the concrete completion bridge into `Sheaf.SixFunctors.DualizableIntegralCompletion`.
These are strict parts of the conjunction, not another name for the original theorem.
The constructibility node retains the unit's shriek-stratum, projection and residue route.
The completion node concerns the actual augmentation in the recorded predicate.
Server compilation succeeded for all three modules (38.8 s, 46.2 s, and 43.3 s).
The sole style suggestion in the parent was fixed by replacing proof-local `letI` with `let`;
the delivery command recompiles the changed parent and runs the required checks.
Only sandbox files are changed. No existing public signature, definition, target, adopted
source-library declaration, or public import changes.

## Proved and sorry left

Closed the original body hole in `AlgebraicGeometry.ProEtale.integralTensorProduct`
(node `det-lem-int-tensor-product`) by decomposition, not as a net proof closure.
Proved private helpers `localModel_dualizable` and `dualizable_preserves_products`, and the
homotopy-limit clause in the public assembly.

Original item: 1 hole. Item after this delivery: 0 holes. Added: 2 named theorem holes:

- `AlgebraicGeometry.ProEtale.integralTensorConstructibility`
  (`lem-sfb-integral-tensor-constructibility`). Its complete source argument is in the
  docstring and node. It has no duality or limit-preservation conclusion.
- `AlgebraicGeometry.ProEtale.dualizableIntegralCompletion`
  (`lem-sfb-dualizable-integral-completion`). It only connects dualizability with the
  concrete continuous-coefficient completion predicate; it has no local-model,
  constructibility, characteristic, product or homotopy-limit conclusion.

Thus this delivery closes 1 upper hole, adds 2 lower holes, and is a decomposition.
Both new bodies are exactly `:= by sorry`; no definition or private helper has a hole.

## No longer needed

No Lean module is withdrawn. The constructibility split retains the dependencies of the
prescribed stratum/residue proof. The direct local-duality assembly uses the already stated
pro-etale dualizability descent theorem and the proved bounded-complex duality theorem,
so it does not need to reconstruct signed internal-Hom comparisons in this file.
`IntegralTensorShriek` is imported with `import all` solely for its proved private
`freeFromPoint` finite-biproduct comparison; its public generation theorem is still needed
by the separate constructibility node. This is proof visibility only.

Removed direct proof imports from the item:

- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`
- `WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`
- `Sheaf.CategoryTheory.RingedSiteDualityMaps`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `WeilConjectures.CategoryTheory.TruncationTriangle`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.SixFunctors.IntTensorProjection`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.IntegralTensorPullback`
- `Sheaf.Paper.IntegralConstructibleHeart`
- `Sheaf.Paper.IntegralModels`

These removals do not assert that the modules have no other consumers. In particular
`InternalDerivedClosedLocalization`, `FiniteFreeDualChainComparison` and
`EvaluationDualityCompletion` are not direct assembly dependencies; the completion split
still explicitly cites the latter, and the constructibility split retains finite-free
comparison and all original stratum/residue dependencies.

Removed obsolete direct `tool_uses` approvals from the parent node (the parent retains
`lem-pc-homotopy-limit-map`; lower nodes cite what their arguments need):

- `lem-pc-kflat-resolution`
- `lem-sc-source-kflat-tensor-left-triangulated`
- `lem-sc-finite-free-internal-hom-exact`
- `lem-pc-bounded-exact-term-hom-quasi-iso`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-pbc-unbounded-derived-iso-cohomology`
- `lem-pc-sites-modules-sheafification-flat`
- `lem-pc-sites-module-sheafification-interface`
- `lem-pc-sheaf-modules-tensor-closed`
- `lem-weil-pbc-truncation-triangle`
- `sk-lem-int-integral-heart`
- `sk-lem-integral-models`
- `sk-thm-pe-constructible-comparison`
- `lem-weil-pbc-sheaf-tensor-closed`
- `lem-weil-proetale-weakly-etale-localization`
- `sk-prop-sfb-cartesian-coefficients`

## Where the brief, the DAG or earlier work was wrong

The available integral-shriek and integral-heart APIs use coefficient presentations different
from `DerivedNakayama.integerRing`. The former uses the spectral-norm condensed ring;
the latter uses a small shrink of the extension. They are mathematically isomorphic but are
not definitionally equal to the constant-model predicate in this statement. Naive applications
fail at the coefficient object before reaching the mathematical stratum argument. No interface
or statement was weakened to hide this issue; the remaining constructibility item records
exactly the original coefficient convention.

The generic evaluation/completion theorem is stated for section-ring modules with a chosen
native closed structure and augmented tower model. Applying it to the actual internal-module
`IsDerivedComplete` requires transport of the entire augmentation, not only an objectwise
completion isomorphism. That precise bridge is the second remaining item.

Edge cases checked mathematically: rank zero; zero complex; empty scheme and empty cover;
chart-dependent bounds and ranks; arbitrary index universes; non-Noetherian S in the moreover
clause. None requires an extra hypothesis. Existing public declarations and the target
statement were compared with the repository originals.

## New nodes

`lem-sfb-integral-tensor-constructibility`, in
`Sheaf.Paper.IntegralTensorConstructibility`, carries the two final blueprint proof paragraphs,
including shriek devissage, projection, local perfectness, residue tensor and the integral
criterion. Its source, complete proof in words and three actual Mathlib searches are recorded.

`lem-sfb-dualizable-integral-completion`, in
`Sheaf.SixFunctors.DualizableIntegralCompletion`, carries the completion part of the first
blueprint paragraph, with the canonical quotient-unit normalization. It is a concrete
coefficient transport/application of the abstract augmented evaluation-duality theorem.
Its source, complete proof in words and three actual Mathlib searches are recorded.

Both inherit chapter `sec-six-functors-basics` and unit `sk-lem-int-tensor`.
Blueprint/DAG searches for integral tensor, bounded constructible tensor, derived complete,
and dualizable completion found the parent and general abstract results, but no separate node
with either exact recorded statement. No change record is needed: existing statements and
definitions were preserved.

The generic pro-etale dualizability descent result
`lem-zl-condensed-lisse-proetale-locality` is used as a tool: it supplies exactly the
covering criterion, with no substitute coefficient or characteristic assumptions.
The source theorem `DerivedCategory.isDualizable_Q_obj` and
`isDualizable_biproduct_unit` are proved library tools, not new unfinished dependencies.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
