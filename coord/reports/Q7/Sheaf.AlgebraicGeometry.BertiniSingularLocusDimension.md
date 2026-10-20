## What changed

The original theorem `AlgebraicGeometry.bertini_singularLocus_dimension_lt` now has a complete
Lean proof. It constructs the reduced singular scheme, proves finite-type and Noetherian
properties, applies fibre dimension bounds on an open cover, handles zero coefficients using
empty projective space, and bounds the closure of the coefficient image. Its statement and
all four existing definition bodies are unchanged.

`BertiniUniversalFamily` holds those four definitions to avoid an import cycle and adds proved
closedness, the explicit reduced singular scheme, its source projection and homeomorphism,
and the finite-type coefficient-space lemma. `BertiniSingularFibreCharts` proves the chart
bounds from `BertiniSingularFirstOrderModel`. Its private `firstOrderKernel_dimension` proves
rank-nullity and the symmetric-algebra dimension formula directly from Mathlib. `BertiniSingularFirstOrderModel` now chooses smooth charts and applies the proved
`bertini_singular_fibre_kernel`. The latter constructs its closed immersion from the
coordinate quotient using `symmetricAlgebra_factor_through_dual_kernel`, proved from
Mathlib dual restriction and the universal property of the symmetric algebra.

The remaining geometric equations are the separate local calculation in the final
paragraph of Stacks 0FD6. They are stated in `BertiniSingularFibreEquations`, with the
actual coefficient quotient and its compatibility with the universal projection.
No dimension estimate, global cover or proper-image conclusion is assumed there.

Change record: `coord/changes/q7-bertini-universal-family-extraction.md`.

## Proved and sorry left

Original hole closed syntactically: `AlgebraicGeometry.bertini_singularLocus_dimension_lt`
(node `lem-zl-bertini-singular-locus-dimension`). Its complete proof uses Mathlib, the
existing finite-type fibre/image dimension theorem, and the proved fibre-chart theorem.

New proved declarations:

- `AlgebraicGeometry.isClosed_bertiniUniversalSingularLocus`
- `AlgebraicGeometry.bertiniCoefficient_locallyOfFiniteType`
- `AlgebraicGeometry.bertini_singular_affine_fibre_charts`
- `AlgebraicGeometry.bertini_singular_first_order_model`
- `AlgebraicGeometry.bertini_singular_fibre_kernel`
- `symmetricAlgebra_factor_through_dual_kernel`
- private `AlgebraicGeometry.firstOrderKernel_dimension`

One sorry is added and remains:
`AlgebraicGeometry.bertini_singular_fibre_equations`
(node `lem-zl-bertini-singular-fibre-equations`). It supplies surjective first-order
evaluation and its vanishing in the concrete affine coordinate quotient of a singular
fibre, with coefficient compatibility. It is strictly the local differential calculation;
it asserts no dimension estimate, no open cover and no proper-image conclusion.

This is a decomposition: one original hole closed and one local hole added, net zero
holes closed. The full Bertini theorem still depends on that local theorem and existing
imported theorems with sorry; no axiom-free proof is claimed. There are no other sorries
in this packet and no proof hole inside any definition. All seven retained modules
compiled together on the required compiler service. The discarded affine helper was an
unsubmitted experiment, not a
library module being withdrawn.
The current source of the direct consumer `BertiniSmoothMember` also compiles unchanged
against the delivered definitions and theorem. The resumed single-file axiom probe passes:
all seven universal-family definitions use only `propext`, `Classical.choice` and `Quot.sound`;
the main theorem and the local equations theorem additionally use the reported `sorryAx`.
The source signature and the four extracted definition bodies were compared directly and
are textually identical.

## No longer needed

Removed direct imports from the original module:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Mathlib.RingTheory.FiniteType`
- `Mathlib.RingTheory.Spectrum.Prime.Noetherian`
- `Mathlib.Topology.NoetherianSpace`
- `Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion`
- `Sheaf.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints`
- `Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSections`
- `WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre`
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`
- `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`

The conormal/hypersurface imports move to the local fibre-equations calculation;
they remain dependencies of that calculation and are not globally pruned. The dedicated
smooth differential rank theorem is no longer applied by the global argument: its charts
use `Smooth.exists_smoothOfRelativeDimension_resLE` and the source library's proved
constant-relative-dimension bound. It remains cited in the local equations proof plan. The tensor and zero-scheme imports
move to the public support module. Several other statement imports are already supplied
by the two public support imports. `ProjectiveSpaceFunctorOfPoints`,
`InvertibleGeneratingSectionsFibre`, and `PullbackFreeGenerator` have no direct use in the
global proof. No existing module is withdrawn.

The global node no longer directly needs
`lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension`,
`lem-pur-conormal-sequence-smooth-immersion`,
`lem-zl-hypersurface-nonzero-relative-differential`,
`def-sc-relative-differential-sheaf`, or `lem-pc-proper-base-change`:
they belong to the isolated local first-order theorem. Its former off-unit tool approvals
for the smooth-differential and conormal lemmas are removed from the global node because
its proof does not apply them directly; these tools are still cited by the new local node.
The global proof also no longer directly needs
`lem-wf-affine-noetherian-components`, `lem-kun-finite-union-noetherian`, and
`lem-sfb-noetherian-space-compact-subsets`: existing Noetherian/projective-space and
quasi-compactness instances prove that step. The generation and invertibility definitions
remain in the statements, so these are not claimed as pruned from the full closure.

## Where the brief, the DAG or earlier work was wrong

Earlier retained work had proved the global argument and the rank/dimension argument.
Its report became stale when work continued through the local kernel factorization:
the remaining sorry is now `bertini_singular_fibre_equations`, not the first-order
model theorem. The retained kernel proof had a dual-restriction elaboration mismatch;
explicit pointwise equality of the linear maps repairs it and the full packet compiles.
The experimental affine-fibre helper was discarded after unsuccessful pullback-square
elaboration; no declaration from it is used by the retained proof.

The current source library moved `EtaleTensorSections` from `Sheaf.AlgebraicGeometry`
to `WeilConjectures.AlgebraicGeometry`; the support module now imports the current path.

Delivery infrastructure failure: the first completed server preflight requested LeanSearch
records for the fibre-equations and fibre-kernel nodes. Both actual searches were run and
their returned results added. The corrected dry run then crashed in
`sharedrepo.worktree`: `git checkout --detach origin/sheaf-dag` timed out after 600 seconds
(`dry-run-search-fixed.log`). Its single retry was killed with exit code 137 after waiting
for a shared resource (`dry-run-checkout-retry.log`; the exec result records the kill).
No delivery push ran in that attempt. The complete compiling packet was retained.

The initial required dry run returned the split-off policy diagnostic. The sandbox's
reference clock has reset across dispatcher resumptions: the observed start value was
1792426892.9122016, later 1792437873.389844. The `.brief2` through `.brief5` markers are
present. No budget metadata or launcher script was changed. Those earlier attempts reached only dry-run checks.

The existing proof plan correctly avoids a flatness inference at the zero parameter. The
local model retains the one-way hypersurface criterion for exactly this reason. Edge cases
checked: the empty source, zero coefficients in the global theorem, zero-dimensional smooth
charts, zero-dimensional linear kernel, disconnected sources and arbitrary residue fields.
No unit statement or unit proof step is bypassed. There is no change to the paper statement.

Resumed validation (2026-10-20): all seven retained modules compile against the current
server build. The required initial dry run now passes (`8da378c6cf`, nothing pushed).
It reported a timed-out axiom probe for the local equations theorem; a separate probe
subsequently completed in six seconds with exactly the axioms reported above. The consumer
closure was rechecked and now contains 26 modules, still with no textual uses of the four
moved definitions outside their original module. Further affine-coordinate experiments
remain outside the delivery: their combined elaboration exceeds the file limit, even with
local irreducibility attributes, and no incomplete experiment is imported by this packet.
The remaining first-order equations are the separate local calculation of Stacks 0FD6;
the packet does not count the one-hole decomposition as a net proof.

## New nodes

`def-zl-bertini-universal-family`: support definitions extracted verbatim and proved topology
and coefficient-space facts. No sorry.

`lem-zl-bertini-singular-first-order-model`: proved local smooth-chart construction,
using the fixed-chart kernel theorem. No sorry.

`lem-zl-bertini-singular-affine-fibre-charts`: proved complementary dimension bounds from
the model, rank-nullity and symmetric-algebra polynomial dimension. No sorry.

`lem-zl-bertini-singular-fibre-kernel`: proved closed immersion from the first-order
coordinate quotient and the algebraic factorization, including coefficient compatibility.
No sorry. Also attaches the concrete `bertiniLinearKernelCoefficientMap` definition.

`lem-zl-symmetric-algebra-kernel-factor`: proved algebraic factorization of a surjective
symmetric-algebra quotient killing dual equations through the dual of the kernel. No sorry.

`lem-zl-bertini-singular-fibre-equations`: the local first-order equations and actual
coordinate quotient, from the final paragraph of Stacks 0FD6. One sorry, with complete
proof in words and source in its docstring. Tested conceptually on empty fibres, d=0,
zero kernel, nonclosed residue fields and the zero coefficient parameter. Its construction
uses only the one-way hypersurface smoothness criterion and does not assume flatness.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
