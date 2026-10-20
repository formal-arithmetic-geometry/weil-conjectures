## What changed

Repair of returned head `a6dddc24a`: the comparison change record now lists
`Sheaf.Paper.OpenRestrictionScalarExchange` in `## Users`, including its use of
`openRestrictScalarsIso`, `openDerivedRestrictScalarsIso`, and
`openScalarRestriction`. Their qualified names, defining data and public reexport
are preserved, so this consumer requires no adaptation.

The repair's delivery check exposed a K-flat compile timeout. Two proved private
general lemmas now handle functor-equality transport and the complex-level
acyclicity argument before specializing to the concrete sheaf categories. This
keeps the same proof route, public signatures, constructions and hole count.
The profiled complete proof took 26.7 seconds; the final concrete application's
kernel check fell from 30.7 seconds to 7.4 seconds. The profiling module and its
options are absent from the delivery. The complete final sandbox pass compiles
all five modules cleanly: totalization cached (0.0 seconds), definitions 1.2,
K-flat preservation 42.6, scalar coherence 8.2, and the main module 23.7 seconds.

`Sheaf.SixFunctors.EtaleOpenTensor` now assembles all 13 fields of its original
comparison structure. The structure and primary theorem signature are preserved.
The ordinary projection isomorphism and flatness preservation use the published
étale extension results. Projection associativity follows from the abstract
adjunction projection identity after transporting the existing monoidal pullback
structure. The restriction-unit and counit laws are the actual mate identities.

The 18 canonical definitions/declarations move, with their qualified names and
defining data preserved, to `Sheaf.SixFunctors.EtaleOpenTensorDefs`. A public import
preserves the original interface. Its scalar restriction map is proved invertible
by identifying its sectionwise coefficient square, descending that identification,
and transporting the published scalar/pullback inverse mate. The independent coefficient-model subproblem has its own module.
Unbounded K-flat preservation is proved in a separate module, from exactness,
the constant-module tensor comparison and unbounded totalization.

`Sheaf.Paper.EtaleSumTensorTotalization` now exposes the proved
`AlgebraicGeometry.etale_sum_tensor_comparison`: the isomorphism family obtained
from its generic canonical construction without quasi-compactness. K-flatness
needs only this family. All five existing public signatures and all defining
bodies are preserved verbatim, including the quasi-compact full totalization
theorem and all its normalization, naturality, homotopy and descent clauses. A
proved private abstract existence lemma groups that theorem's unchanged
construction and five clauses before specializing.

A private named `totalTensor` functor and general acyclicity transport lemmas
keep the concrete K-flat application from repeatedly expanding total-complex
and homology data. The realization comparison is proved directly for this
abstract tensor interface, and a proved equality of the existing realization
functors transports it explicitly. This removes an observed 18-second kernel
conversion in the concrete comparison. They are proved/constructed in the same file. No file is split
to avoid the compile limit.

The existing flat and tensor-test realization definitions remain unchanged.
No source-library file or target statement is edited.

The previous delivery's complete sandbox pass succeeded with K-flat preservation
in 53.8 seconds. The current repair improves its compile margin as described above.
A fresh compile of the added totalization API previously succeeded in 55.2 seconds.
All private helpers are proved in their own module, with no profiling options
or temporary diagnostic declarations retained. Edge cases checked mathematically:
identity and empty open immersions, zero coefficient rings, unbounded complexes,
and non-quasi-compact open immersions. Neither the acyclic tensor test nor sum
totalization uses a boundedness or quasi-compactness assumption.

Downstream compilation succeeded for `EtaleLocallyClosedShriek` (48.7 seconds),
`FiniteCoefficientHomChange` (24.2), `InternalAdjunctionPairingChange` (42.4),
`EtaleSumPreservesKFlat` (8.0), and `EtaleConstantModuleFlat` (17.7), and the held
`EtaleSupportMapCompatibility` (9.7).
The unchanged held module `ProperOpenCoefficientMate` reached the 60-second
limit without a Lean diagnostic; no edit to it is included. The unchanged
`EtaleConstantModuleTensor` and `EtaleSumTensorTestProjection` also reached
that limit. These timeouts are reported
as incomplete consumer checks, not successful checks. The original comparison
structure and the five original totalization signatures were checked verbatim.

## Proved and sorry left

Original holes closed:

- `AlgebraicGeometry.Etale.openScalarRestrictionMap_isIso`
  (`lem-coef-etale-open-comparison-data`): proved from the published fixed scalar
  mate, with the ordinary square and exact/left-derived transport proved here.
- `AlgebraicGeometry.Etale.etaleOpenTensorComparisons`
  (`lem-coef-etale-open-tensor`): complete Lean assembly from proved fields and
  the proved K-flat result and the independent coefficient-model subproblem below.

Additional proved theorems:

- `AlgebraicGeometry.Etale.etaleOpenKFlat`
  (`lem-coef-etale-open-kflat`): preservation of arbitrary unbounded acyclic
  tensor tests, including for a non-quasi-compact open immersion. The proof
  constructs the total tensor comparison and signed symmetry, transports tests
  through the realization equivalence, and applies exact restriction and extension.

- `AlgebraicGeometry.etale_sum_tensor_comparison`
  (`lem-coef-etale-open-total-tensor`): the canonical unbounded total-tensor
  isomorphism family without quasi-compactness, using the actual generic
  coproduct and total-complex construction.

New hole retained:

- `AlgebraicGeometry.Etale.etaleOpenScalarComparisons`
  (`lem-coef-etale-open-scalar-coherence`): precisely the four scalar model
  normalization/uniqueness fields, successive coefficient composition, and mixed
  tensor/scalar compatibility. It omits the seven other fields of the original
  package and is a strict independent part of its argument.

No hole is inside a definition or a private lemma. Both original holes are closed
and one lower hole is added. The scalar portion is a genuine decomposition, and
the packet's declaration count has a net decrease of one hole; it does not claim
that the full coefficient coherence argument has been proved.

## No longer needed

The original module's following private proof imports are removed. They are not
needed by the new complete field assembly or the proved scalar inverse mate:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.OpenClosed.Complex`

Obsolete top-level tool approvals removed (remaining entries retain their order):

- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-pbc-ringed-slice-extension-tensor`
- `lem-sfb-localized-site-tensor-restriction`
- `lem-weil-pbc-slice-restriction-flat`

The original seven-step node route is replaced with the actual projection, mate,
flatness and independent scalar-model arguments. Its old general ringed-slice and
localized-site tensor proof dependencies are not direct dependencies of the field
assembly. The scalar normalization subproblem still has its own needed resolving
and derived-change-of-rings dependencies. No claim is made that these modules
are globally unreachable, and no upstream declaration or module is withdrawn.
The unit's own statements and realized proof steps remain. The acyclic-test proof
uses the comparison family alone; it does not need the homotopy and localization
clauses of the full finite-type totalization theorem.

## Where the brief, the DAG or earlier work was wrong

The existing general étale K-flat preservation theorem assumes quasi-compactness.
An arbitrary open immersion does not supply that instance. The underlying
canonical total-complex construction does not use quasi-compactness. A new proved
comparison-family theorem exposes exactly what the acyclic-test argument needs,
while every existing totalization signature, definition and clause is preserved.
Its proof and its new DAG node record the actual generic construction.

The concrete total tensor and acyclicity interfaces expand large sheaf and
homology data during conversion. A private named total-tensor bifunctor, general
acyclicity transport lemmas, explicit additive and adjunction instances, and the
standard backward definitional-equality option make the complete argument compile.
A final packet check exposed insufficient timing margin in the first K-flat
implementation. Profiling identified its concrete tensor-realization conversion;
stating the generic comparison in the named tensor interface and rewriting with
a proved realization equality reduced a clean full proof probe to 44.0 seconds; the delivered module
then compiled in 53.8 seconds in the complete packet pass.
The original realization definitions do not need to change. The abstract
projection-associativity and mate arguments similarly avoid concrete unfolding.

## New nodes

`lem-coef-etale-open-comparison-data` attaches the 18 preserved canonical
constructions and the now-proved fixed scalar inverse-mate theorem to their
independent public module. Its proof records the sectionwise adjunction square,
exact derived transport, and the published inverse mate.

`lem-coef-etale-open-kflat` is the proved independent unbounded K-flat preservation
argument by acyclic tests, exact restriction and extension, and the canonical
signed total-tensor projection isomorphism. It applies to arbitrary open
immersions, including non-quasi-compact ones.

`lem-coef-etale-open-total-tensor` is the proved comparison-family API extracted
from the generic total-complex construction. It requires no quasi-compactness
and preserves the published extension and inverse-image functors. The original
full finite-type theorem and its unit route remain unchanged.

`lem-coef-etale-open-scalar-coherence` is the remaining coefficient-model result:
normalization and uniqueness of the fixed q and r, coefficient tower composition,
and mixed tensor/scalar compatibility. Its statement lists the actual equations,
its docstring gives the resolving-model proof, and its dependencies are the
existing derived-change, K-flat resolution and tensor-descent interfaces.

Change records:

- `coord/changes/K3-etale-open-comparisons.md`
- `coord/changes/K3-etale-totalization-nonquasicompact.md`

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
