## What changed

Proved `DerivedRepresentativeSquare.section_derived_representative_square` by
conjugating the actual internal derived tensor arrow, applying the proved native
cochain component formula, transporting through the resolution-conjugation
identities, and cancelling the invertible input identification. Exactness and the
resolving tensor comparison give input invertibility; the square and actual tensor
isomorphism give output invertibility. The composite natural transformation gives
naturality, and cancellation gives inverse naturality. The unit component formula
and resolving constraint diagrams give the unit, associator and unitor conclusions.
No arbitrary choice of data or new postponed proof is introduced.

Repair C-25a68 A1: rebuilt the tensor-data, total-comparison and oplax-consumer files
from the current G6 source, preserving every G6 change. In particular the retained
cochain functors, cochainTensorComparison, totalSectionPullMonoidal, all naturality
APIs, the shared cochain import and both explicit total-tensor localization binders
remain. Every D7 declaration and its current G6 construction remains. Only the U3
TensorFunctorTransport sharing, transportedDerivedMonoidal and four projection
APIs are reapplied. The earlier generic flat-cover, chosen-total-comparison and lax
localization proof optimizations are dropped. The existing tensorUnit and
localizedTotalComparison definitions remain verbatim.

The resolving constraint data aliases the shared transported structure. The square's
generic ConstraintData expresses exactly the original public paths. The theorem
signature is verbatim; separate private reflexivity checks compare all four full
predicates with the current original definitions. The proof uses G6's retained
component interfaces when normalizing the binary, unit and regular-unit equations.
The tensor and pullback comparison projections are first identified with the
whole native typed path, before associativity is applied. The retained localization
map is exposed before substituting the native unit formula. These are proof
conversions, without data changes.
The current G6 representative-component and conjugation-identity modules are
validated unchanged.

The total-comparison data retains all current definitions verbatim and adds
actualInternalTotalIso_hom, sectionTotalIso_hom, sectionTotalIso_δ and
sectionTotalUnit_η. Their proofs are reflexivity after unfolding their specified
constructors. The oplax importer uses them in its two summand proofs and native
oplax laws, preserving G6's cochainTensorComparison unfolding. The normalization
consumer changes only its private totalPullComparison_eq proof to the projection
API plus reflexive transport simplification. The data, resolving constraint-data, representative-square and realization files
select synchronous elaboration; every realization declaration and proof body is unchanged. The
constraint-data profile measured 7.29 seconds of kernel checking and 1.99 seconds of
elaboration; the synchronous compile passed, and profiling flags are removed.
The private proof caches the canonical derived-category instance and the data fields
of its monoidal structure, avoiding repeated conversion through compact instance
wrappers. These caches occur after all public predicates and do not change their
statements. The accepted profile measured 22.6 seconds of kernel checking,
3.67 seconds of elaboration and 6.77 seconds of instance inference. Profiling
options are removed.
All adapted dependency modules are unclaimed; no adopted source file is edited.

The six existing node copies preserve the current G6 proof steps and Lean
attachments. Both requested proof_origin records remain objects with their current
document/place and an added U3_note. Both change records and their Users tables
are refreshed from current sources and claims:
`coord/changes/section-derived-tensor-projection-sharing-U3.md` and
`coord/changes/section-cochain-structure-projections-U3.md`.
The broad tensor query intentionally includes unrelated short-name matches; it is
not a claim to have rebuilt the complete downstream library.

Validation completed through lcompile.py with the server compiler. All seven edited
modules compile, including the clean representative-square proof without profiling
options. All six requested consumers compile: SectionDerivedRealization,
SectionOplaxTotalComparison, SectionKFlatTensorComparison,
SectionDerivedTensorNormalization, SectionTensorRightComputation and
BoundedFlatTensorContinuity. The current G6 SectionCochainTensorComparison,
SectionRepresentativeTensorArrow and SectionResolutionConjugationIdentities, and
SectionResolvingOplaxConstraintDiagrams, also compile unchanged. A temporary private
module proved by rfl the equality of each of Naturality, InverseNaturality,
AssociatorNormalization and UnitorNormalization with the current original full
definition; it is not part of the delivery. The public theorem signature is
byte-for-byte identical to current source. Existing unused-section-variable warnings
in unchanged K-flat and right-computation consumers remain. All final Lean files
have zero literal sorry occurrences, no profiling options and lines at most
100 characters. Current source hashes were rechecked immediately before delivery;
no further source changes occurred. Unchanged validation copies are excluded.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.DerivedRepresentativeSquare.section_derived_representative_square`
(lem-pd-section-derived-representative-square). The assigned module has zero
remaining holes. Every adapted dependency module has zero holes. Added zero holes;
split off zero statements. Existing named dependencies remain the prescribed route.

## No longer needed

Removed the direct proof imports
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.Paper.DerivedPullbackRepresentativeComputation`,
`Sheaf.Algebra.Homology.KFlatTotalTensorModel`, and
`Mathlib.CategoryTheory.Localization.Predicate`.

No direct use remains of lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-weil-pbc-kflat-tensor-pullback-computation-universes, or
lem-pur-kflat-total-tensor-model. Exactness supplies invertible epsilon everywhere;
the representative equation and the invertible actual conjugate supply output
invertibility. The binary component uses the proved source-library
`Functor.leftDerivedTensorComparison_app_app_comp_tensorHom` directly.
`InternalOplaxResolvingComponents` remains needed for the unit component.
The constraints theorem retains its nested resolving closure. Site tensor descent
remains a statement dependency through the fixed qTensor maps; the proof does not
separately use its transformation-extension clause.

Removed the corresponding obsolete top-level tool approvals for
lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-weil-pbc-site-derived-tensor-descent,
lem-weil-pbc-kflat-tensor-pullback-computation-universes, and
lem-pur-kflat-total-tensor-model. These are removals of direct uses in this proof;
existing dependencies of imported declarations and all source-library declarations
remain. No module or unit route is withdrawn.

## Where the brief, the DAG or earlier work was wrong

Returned packet 25a68f8915b preceded G6's landed b4e6cc1b458 and would have reverted
its retained functors, naturality APIs and explicit binders. This repair starts from
those current sources, preserves them, and adapts the square proof to their actual
interfaces. The earlier packet also replaced two object-form proof_origin records;
those are restored from current source with additive U3 notes.

The original module docstring described an older seven-step plan. The current node
has a five-step assembly using the subsequently stated conjugation and constraint
lemmas; the proof follows that assembly. Inverse naturality follows from ordinary
naturality and the specified inverse equations. Exactness makes the former general
preservation and computation calls unnecessary for the section pullback.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
