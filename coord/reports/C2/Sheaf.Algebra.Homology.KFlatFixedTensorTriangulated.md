## What changed

Completed the cone, signed-shift and localization argument for
`SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated`, preserving its
statement. The proof uses the existing generic homotopy tensor, cone-triangle exactness,
and coherent two-variable shift localization. It extends the actual resolving comparison
through localization and proves its normalization to `representativeIso` in both orders.

The only delivered Lean module is the item. Added proved private proof helpers and
private proof imports. Added public structures packaging the existing descent data,
public projections of their membership and comparison fields, and named proofs of the
existing tensor instances, registered locally while the ordinary tensor is sealed. The
ordinary and derived tensor definitions are protected locally from repeated unfolding
and exported as reducible for importers. The proved equations
`ordinaryTensor_eq_published` and `derivedTensor_eq_published` identify them with the
published tensors by unfolding. The representative formula uses exactly the same
selected comparisons as before. See the definition change record
`coord/changes/C2-kflat-fixed-tensor-presentation.md`. A separate diagnostic checked
that the representative formula is definitionally the original nested-choice expression.
The normalization is checked generically against `TensorPresentation` before specializing
to sheaves, keeping the dependent comparison expressions shared.

The final generic assembly compiled without warnings in 47.3 seconds; its exact delivery
axiom probe compiled in 50.5 seconds (`SHEAF-PROBED 50`), with no extra axioms or local
admissions reported. A three-file check compiled the item (49.7 s) and unchanged
`DerivedTensorAdditiveConstraints` (24.0 s) and `FlatScalarCyclicResolution` (13.7 s).
Removed the now-unused private `derivedTensorUncurryIso` after the generic assembly;
the inverse currying counit is included directly in that assembly. The delivered source
has no lines over 100 characters. Earlier scoped-export checks also compiled
`ProEtaleTorIntervalTriangle` (6.8 s), `KoszulFibreLinearDescent` (5.8 s), and
`SiteOneSidedTensorNormalization` (6.4 s). Other checks returned server busy or timed
out before reaching consumers; the change record distinguishes these cases.

The live closure grew to nineteen downstream modules during this session. Preflight
identified three newly added consumers absent from the earlier change record:
`ExactPullbackSignedComparison`, `BoundaryBoundedTensorComparison`, and
`ScalarModelFiniteFlatResolution`. The record now includes them and all current
transitive consumers. The final item compiled in 46.3 seconds together with unchanged
`BoundaryBoundedTensorComparison` (20.9 s) and `ScalarModelFiniteFlatResolution`
(33.4 s). `ExactPullbackSignedComparison` compiled in the same batch (39.4 s),
but preceded the replacement item; its direct final-overlay recheck then passed
in 28.2 seconds. Thus all three newly identified consumers pass unchanged.
A further newly landed consumer, `SignedLineDerivedBaseChange`, uses the same preserved
interfaces; its final-overlay check returned server busy. Five further unchanged consumers pass against the final overlay:
`LineUnboundedDerivedTensor` (9.3 s), `RingedKFlatSingleTensorComparison` (33.3 s),
`ProEtaleTorIntervalShift` (10.7 s), `PullbackTensorCanonicalShiftUnit` (14.6 s), and
`PeriodicTensorNormalForm` (32.7 s). No consumer is adapted. The public tensors and representative maps are definitionally
unchanged, and the main theorem signature and all original public imports stay verbatim.

The consumer overlay also encountered an independent failure in
`Sheaf.Paper.WeilTensorProduct`: its `wfTensorRepresentative_exists` declaration
has unresolved `EssentiallySmall` universe constraints, followed by a missing-name
error. That module has no import path to this item. It prevented earlier checks of
`FiniteFreeResolutionTensor` and the former consumer `WeilTensorWeil` through that
overlay. No unrelated module is adapted.

Repair of the returned head 17c0184b980: the landing passed independent review
but lacked three consumer rows under the change record's `## Users`. The repaired
record explicitly lists `Sheaf.Paper.IntegralModels`,
`Sheaf.Paper.IntegralStratumHomFormula`, and
`Sheaf.SixFunctors.IntegralTensorInverseImage`, and covers all 59 current downstream
modules returned by the first fresh `tools/downstream.py` check on 2026-10-22.
A second refresh during the delivery wait lists 227 downstream modules. Added the
newly found consumers, with current claim holders, to the same change record;
all 227 are now covered. No consumer source changes are required because the
public tensors and representative maps are definitionally unchanged. Re-read all
three sources: `IntegralModels` explicitly uses `CondensedRing.derivedTensor`;
the other two use `derivedTensor` inside the namespace
`AlgebraicGeometry.ProEtale.CondensedRing`. Their tensor is defined in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`, so their
statements do not change. No consumer adaptation is necessary.

The reviewed mathematical proof and public objects are retained. A later delivery
compile exceeded the 60-second file limit. Profiling found substantial cost in
the sheaf-specific definitions: the generic declarations compiled in 21.8 seconds,
and the prefix through the sheaf definitions in 42.0 seconds. A focused full-file
profile passed in 38.1 seconds and measured 11.1 seconds of type checking for the
final theorem. These timings are separate diagnostic runs.

The completed performance repair gives `selectedTensorPresentation` its explicit
`TensorPresentation` type and protects it locally from unfolding, then restores
its original reducible interface for importers. The private
`tensorPresentationComparison` definition stores the original composed natural
isomorphism once; its component equation is proved by the existing calculation.
The public tensors and representative isomorphisms still use exactly the original
selected data, and `derivedTensor_eq_published` still compiles by unfolding and
reflexivity. No statement or hypothesis changes.

The complete repaired module passed without warnings in 51.7 seconds. In the same
server batch, all twelve unchanged current consumers passed, including the three
reported by the return: `IntegralModels` (31.4 s), `IntegralStratumHomFormula`
(19.2 s), and `IntegralTensorInverseImage` (36.2 s). The other successful checks
were `DerivedTensorAdditiveConstraints`, `FlatScalarCyclicResolution`,
`LineUnboundedDerivedTensor`, `RingedKFlatSingleTensorComparison`,
`SiteOneSidedTensorNormalization`, `ProEtaleTorIntervalShift`,
`PullbackTensorCanonicalShiftUnit`, `ExactPullbackSignedComparison`, and
`PeriodicTensorNormalForm`. No consumer source is adapted. Experimental variants
are retained only under `scratch/` and are not delivered.

Before that performance repair, fresh validation on 2026-10-22 passed without
warnings in 56.7 seconds through
`lcompile.py`, followed by an explicitly remote server compilation in 57.7 seconds
(`LCOMPILE_NO_LOCAL=1`). There are zero holes in the delivered module. The item
on the current shared branch still has the original one-hole statement, and the
sandbox node differs only in the proof route, its Lean attachment and removal of
an obsolete tool dependency. The mathematical statement, statement dependencies,
blueprint and unit fields agree with current main. `deliver3.py` rebases this
retained proof and the corrected records on the freshly fetched `sheaf-dag` and
runs the axiom probe and preflight before pushing.

Earlier repair attempts were interrupted while waiting for a delivery slot; they
produced no delivery commit. Their busy-server consumer checks are not treated as
successful validation. The unchanged definitions and the namespace checks above
establish that these three consumers need no source adaptation.

Four delivery attempts in the current repair session each ended before preflight
because the compile server returned no answer within 645 seconds. The first two
explicitly requested remote compilation; the next two used the delivery tool's
default routing. These are transport/capacity failures, not Lean compiler errors;
all attempts pushed nothing. A fifth attempt reached Lean but exceeded the file limit; the performance repair
and successful thirteen-file batch above address that failure. The 227-consumer
refresh is retained for the next submission.

The final pre-submission refresh lists 229 downstream modules; every one is included in the table.
No current consumer was missing from `## Users` at that refresh.
A queue-time refresh lists 230 downstream modules; the new direct consumer
`Sheaf.CategoryTheory.KoszulTensorDerivedTower` is now included as well. Its
uses of `derivedTensor` and the fixed-tensor theorem retain their interfaces,
so no source adaptation is needed.

The node's proof, dependency list and Lean attachment follow the implemented route.
Its mathematical statement and unit route are unchanged.

The queue-time new consumer `KoszulTensorDerivedTower` compiled unchanged
in 4.0 seconds against the submitted item, which recompiled in 40.8 seconds.
The next delivery attempt received no compile-server answer within 645 seconds
and pushed nothing. The next submission refresh covers 230 current downstream modules.

Reviewer correction (2026-10-22): `selectedTensorPresentation` now carries the published
`siteDerivedTensorIndependentCoefficients J R` literally as its `derivedTensor` field.
This makes the exported `derivedTensor` reducibly equal to the original abbreviation.
Before the correction, `Sheaf.Paper.DerivedCompletedTensorBilinearity` failed against
this module. See the change record.

## Proved and sorry left

Closed the original hole in
`SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated`
(node `lem-weil-pbc-kflat-fixed-tensor-triangulated`): one original hole closed.
No hole is added, no `sorry` remains in the delivered module, and no statement is split off.
All definition fields are constructed, not admitted. Existing lower dependencies retain
their own proof obligations.

## No longer needed

Removed direct proof imports of
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, and
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`.
The first is unnecessary because the existing totalization and additive instances suffice;
the second is unnecessary because site tensor descent already gives the resolving
localization equivalence. The third is reexported by the used
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated`.

Consequently the node no longer directly uses
`lem-weil-pbc-independent-sheaf-tensor-colimits` or `lem-pc-kflat-resolution`.
Removed the obsolete top-level `lem-pc-kflat-resolution` tool-use entry, preserving
the remaining current approvals and their order. These two modules remain dependencies of site tensor
descent and other library declarations, so no existing module is withdrawn or claimed
as globally pruned. The tensor cone, acyclic cone, shift and homotopy triangulation tools
remain in use. Also removed redundant direct proof imports of
`Mathlib.CategoryTheory.ObjectProperty.Shift`,
`Mathlib.CategoryTheory.Localization.Prod`,
`Mathlib.CategoryTheory.Localization.Predicate`,
`Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`, and
`Mathlib.CategoryTheory.Triangulated.Pretriangulated`: their APIs are already publicly
reexported by the retained imports.

The current shared DAG was re-split during this session into
`lem-weil-pbc-total-tensor-homotopy-cone-signs`,
`lem-weil-pbc-fixed-tensor-localization-comparison`, and
`lem-weil-pbc-derived-tensor-shift-descent`, with modules
`Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns`,
`Sheaf.Algebra.Homology.FixedTensorLocalizationComparison`, and
`Sheaf.Algebra.Homology.DerivedTensorShiftDescent`.
This proof does not import them: the existing generic triangulated bifunctor and
localization APIs already prove the needed conclusions, and the private generic
assembly simultaneously fixes their shift structures and representative normalization.
In particular it does not need the additional componentwise sign formulas and
resolution formulas exposed by those larger interfaces. No child module is withdrawn;
their other consumers and any independent work remain intact.

The earlier unpublished module
`Sheaf.Algebra.Homology.KFlatFixedTensorDerivedStructure` and proposed node
`lem-weil-pbc-kflat-fixed-tensor-derived-structure` are not delivered. That earlier packet
is retained only under `scratch/earlier`; neither was a landed library declaration.

## Where the brief, the DAG or earlier work was wrong

The earlier unpublished split tried to normalize to an arbitrary family of representative
isomorphisms without its naturality. The proof instead uses the natural bifunctor
comparisons actually selected by the published descent theorem, and adds no intermediate
hole. The existing generic source library already supplies signed cone-triangle exactness
and two-variable shift descent.

Currying followed by uncurrying is naturally isomorphic to the original functor, rather
than definitionally identical. The proof explicitly appends the inverse currying counit;
its components are identities, preserving the exact representative normalization.

The comparison of homotopy tensors is constructed directly on underlying representatives.
Fullness of the quotient proves naturality, so no additional localization choice is needed.

The original nested existential projections caused repeated expansion of dependent
category and tensor types. The shared presentation keeps the original choices and their
checked types together. This is a definition repair without a mathematical statement
change; it is recorded for the independent reader's definition/target review.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
