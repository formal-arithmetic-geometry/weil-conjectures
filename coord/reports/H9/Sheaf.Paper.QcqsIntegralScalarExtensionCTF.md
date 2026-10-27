## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.qcqs_integral_scalar_extension_ctf`
in `Sheaf.Paper.QcqsIntegralScalarExtensionCTF` with its statement, public imports,
coefficient maps, and all existing definitions unchanged. Added proved private helpers
for preservation of finite presentations, the point-pullback/scalar-extension
isomorphism, extension and transport of local models, and assembly of the CTF clauses.
Updated the item node's proof, proof dependencies and proof origin to match the proof.

The finite-field exactness theorem and exact finite-subfield inclusion give both
coefficient cases. Canonical exact-derived-functor isomorphisms give the counit,
triangulated structure, cohomology comparison and boundedness. Scalar extension maps
finite-free presentations to finite-free presentations and commutes with the actual
pullbacks. Thus every original finite constant local model extends on its original
cover. The proved `lattice_scalar_free`, `finite_point_scalars`, and
`closure_point_scalars` helpers from `QcqsConstructibleIntegralLatticeTree` identify
finite scalar presentations over the target field as free; `models_free_cover` from
`FiniteConstantLocalModel` transports this to the cover. The lattice-existence theorem
itself is not used. `Mod.extendScalars_preservesFlat` and the proved source-library
`DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj` preserve the given interval
by mapping a bounded flat model termwise. No new public interface is needed.

Validation: the whole item compiled through `lcompile.py`; the final delivery runs
its compile and axiom preflight. All Lean lines have at most 100 characters. Rank zero,
the zero complex, and empty covers require no exclusions: the presentation/cokernel
and model arguments are uniform, and interval endpoints are never enlarged. The unit
route is unchanged; this helper is below compactification coherence, not a replacement
for that unit's statement or proof steps.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.qcqs_integral_scalar_extension_ctf`
(node `lem-sfb-qcqs-integral-scalar-extension-ctf`).

Proved 1 of 1 original sorries; 0 sorries remain in the item, 0 are added elsewhere,
and 0 statements are split off. Every added private helper is proved. No definitions
or existing declaration signatures are changed. This is a proof, not a decomposition.

## No longer needed

Removed these direct proof imports from the item:

- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Mathlib.LinearAlgebra.Basis.VectorSpace`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison`
- `Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients`

The generic exact-functor API remains available through existing public imports;
`pullIso` is used directly from `ChangeOfCoefficients`. The scalar-field linear algebra
is reused through the proved lattice-module helpers. No whole-library unreachability
or module withdrawal is claimed; other consumers and transitive imports may still
need these modules, and no source-library declaration is removed.

The item node no longer needs these direct proof dependencies:

- `lem-sfb-internal-section-scalar-adjunction`
- `sk-def-sfb-derived-tensor-hom`
- `lem-pe-internal-section-tensor-comparison`
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`
- `lem-weil-pbc-vector-space-free`
- `lem-pc-kflat-resolution`
- `lem-pur-kflat-change-of-rings-independent`
- `lem-sf-ringed-kflat-single-tensor-comparison`
- `lem-pur-change-of-rings-tensor-cancellation-independent`
- `sk-prop-sfb-cartesian-coefficients` (reviewer correction: the Lean proof uses only
  `CondensedRing.pullIso` of `def-sfb-pull-iso`, now cited in step 3 instead; the
  cartesian-coefficients theorem was a generic tool use, not a step of the unit's route,
  so its obsolete `tool_uses` entry is removed as well)

The internal exact-functor/flat-model route avoids section-module realization and
section K-flat tensor cancellation. The standalone vector-space leaf is replaced by
the existing finite scalar-presentation helpers. Removed the corresponding seven
obsolete top-level `tool_uses` entries (the section adjunction, section tensor
comparison, pullback tensor theorem, K-flat resolution, K-flat change of rings,
single-tensor comparison and tensor cancellation), and the reviewer removed the
cartesian-coefficients entry; the other two approvals remain in their original order. No new approvals are added.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The DAG's seven-step section-module
route is longer than necessary because the existing internal scalar-extension
flat-preservation theorem and exact-functor Tor-amplitude theorem already cover the
Tor interval. The new proof retains the original constructibility and local-freeness
clauses, including arbitrary specified strata. The point pullback/scalar-extension
square follows directly from uniqueness of left adjoints, avoiding a separate
ringed-topos tensor comparison. Mathlib searches found no packaged theorem for this
whole CTF assertion; the reduction uses the existing library APIs instead.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
