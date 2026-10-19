## What changed

Proved `AlgebraicGeometry.Scheme.integral_cohomological_adic_criterion` with its original
signature, definitions and public imports unchanged. The item composes the proved comparison
with stratified perfect models and the proved integral specialization of the general adic
criterion. Both added imports are proof-only.

The retained sandbox contained five modules and a decomposition into two local-model holes.
Both holes are now proved. `IntegralCompletedConstantPerfect` constructs a finite free
surjection onto each scalar module. Its kernel is finite and torsion-free over the PID, hence
finite free. The rotated short-exact-sequence triangle and existing perfect triangle closure
supply the bounded projective model. Exact constant realization and completed scalar extension
carry its derived isomorphism to the completed module category. Explicit single-functor and
restriction comparisons then compose it with the given local module isomorphisms.

`IntegralPerfectCohomology` proves `completedConstantChange_exact` by identifying underlying
additive sheaves of scalar extension and tensor by the flat completed ring. The comparison is
natural by tensor induction, and exact conservative forgetful functors transfer exactness.
It then takes homology of each actual local derived isomorphism. Cycles are finite submodules,
homology is a finite quotient, and Noetherianity gives finite presentation.

The two bridges retain the earlier proved coefficient specialization and finite truncation
induction. The latter handles zero-length and inverted cohomological bounds explicitly.
All five modules compile together through the required `lcompile.py --all` workflow. Empty
schemes and zero modules require no nonemptiness assumption; torsion scalar modules are allowed.
No existing definition or signature changes, no arbitrary witness is chosen from an unproved
existence theorem, and no consumer adaptation is required.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Scheme.integral_cohomological_adic_criterion`
(`lem-sfb-integral-cohomological-adic-criterion`).

All new public theorems are proved:

- `AlgebraicGeometry.Scheme.integral_coefficient_hypotheses` and
  `AlgebraicGeometry.Scheme.integral_stratified_perfect_iff_adic_constructible`
  (`lem-sfb-integral-cohomological-adic-criterion-adic-bridge`).
- `AlgebraicGeometry.Scheme.integral_completed_constant_iff_stratified_perfect`
  (`lem-sfb-integral-cohomological-adic-criterion-bridge`).
- `AlgebraicGeometry.Scheme.integral_completed_constant_single_perfect`
  (`lem-sfb-integral-completed-constant-single-perfect`).
- `AlgebraicGeometry.Scheme.completedConstantChange_exact` and
  `AlgebraicGeometry.Scheme.integral_perfect_cohomology_completed_constant`
  (`lem-sfb-integral-perfect-cohomology-completed-constant`).

Holes closed relative to the repository: 1. Holes added: 0. Holes left in the five delivered
modules: 0. The two retained local-model split-offs are proved in this session, so this is a
proof delivery rather than a decomposition. Existing stated dependencies, including the general
adic criterion, remain dependencies as intended by stage 3; this report does not claim they or
the project targets are proved without `sorryAx`.

## No longer needed

Removed these unused proof imports from the original item module:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `WeilConjectures.CategoryTheory.TruncationTriangle`
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`
- `Mathlib.LinearAlgebra.FreeModule.PID`
- `Mathlib.Algebra.Module.FinitePresentation`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.Paper.ConstantModuleSectionProperties`

The original node now directly depends on the two proved bridge nodes. Their local-model nodes
record the declarations actually used. The finite-resolution, DVR and finite-module facts remain
needed below these bridges; they are not claimed globally unnecessary.

`lem-weil-pbc-truncation-triangle` is replaced by the canonical t-structure truncation triangle
and homology comparison API in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
The nodes `lem-weil-l-adic-extension-absolute-value` and
`lem-weil-l-adic-extension-complete` are not used directly: the existing proved finite-module
adic-completeness theorem supplies the coefficient argument.

`lem-weil-pbc-proetale-immersion-limit-preservation` is unnecessary for both local-model proofs:
the two sides use the same actual inverse-image coefficient ring, and exact module inverse image
and slice restriction already compare their singles and cohomology.
`lem-weil-pbc-constant-module-section-properties` is replaced here by the existing exact
commutative-site constant-module realization. Flatness is obtained directly from
`lem-weil-pbc-completed-constant-sheaf-reduction`, rather than a second integral specialization.
The integral-coefficient-limit and condensed-constructibility nodes supply no additional proof
step here: the statement already uses the actual completed ring and its local-model predicate.
Their original public interfaces remain imported.

Removed the unused `SiteTensorFunctoriality` proof import from the local-cohomology development,
using `TensorProductOfUniverses` directly, and the unused explicit `FinitePresentation` proof
import from the degree-zero development. The original node's obsolete top-level `tool_uses`
entries are withdrawn. No library module is withdrawn, and no whole module is claimed removed
from the targets' transitive import closure.

## Where the brief, the DAG or earlier work was wrong

The retained node had incorrectly added the two bridge results to statement dependencies;
they are proof dependencies only, so the original statement dependencies are restored.
The retained report described two geometric steps as unfinished. Both can be proved from existing
interfaces. In particular, the scalar finite free resolution is efficiently expressed using the
already proved perfect-triangle closure, and the actual inverse-image coefficients avoid an
unnecessary completion-on-stratum identification. The DAG proof steps are updated accordingly.
The new module and instance docstrings carry their blueprint tags, and the four new node
statements explicitly introduce the coefficient and scheme data. The four new nodes identify the
nearest blueprint ancestor, `det-lem-integral-models-stacks`, and the precise local-model or coefficient
step of its integral-criterion invocation. Preflight also found the retained search records
missing LeanSearch; each new node now records its actual LeanSearch query and an additional
grep of the relevant Mathlib source, alongside its retained semantic/type searches.

The older `integralStratifiedPerfectCharacterization` has a different coefficient presentation
and extra dimension and invertibility hypotheses. It is not used and no such hypotheses are
added. The integral-models unit route is retained: completed coefficients, the general adic
criterion, finite projective dimension over the DVR, finite cohomological devissage and perfect
local-model cohomology all occur in the proof.

## New nodes

`lem-sfb-integral-cohomological-adic-criterion-adic-bridge`: proved coefficient hypotheses and
specialization of the existing general criterion.

`lem-sfb-integral-cohomological-adic-criterion-bridge`: proved comparison using bounded finite
truncation devissage and the two proved local-model results.

`lem-sfb-integral-completed-constant-single-perfect`: proved degree-zero local finite-projective
model construction over the integral coefficient DVR.

`lem-sfb-integral-perfect-cohomology-completed-constant`: proved exactness of completed scalar
extension and constructible completed-constant cohomology of perfect local models.

No change records are needed: all four nodes and their modules are new, and no existing signature,
definition or public import changes.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
