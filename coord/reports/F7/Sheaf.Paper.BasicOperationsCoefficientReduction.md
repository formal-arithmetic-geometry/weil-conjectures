## What changed

Reduced `WeilConjectures.basicOperationsCoefficientReduction` to two separate mathematical
parts of its recorded argument, and proved the combining implication using their conclusions,
the existing unique representative specifications, and `derivedPullbackTensorIso`.
The theorem statement is unchanged. The existing coefficient-law definitions move verbatim
into `Sheaf.Paper.OperationCoefficientActionData`, publicly re-exported by the item.
No adopted source-library file changes. All four modules passed the sandbox compile in import order. The original theorem
signature was checked byte-for-byte against the shared source.

Repair of the returned head `28abdf8a8d5` (reviewer `C-28abd`): the independent review
passed; landing rejected a report fix named only
`Sheaf.Paper.BasicOperationsCoefficientReduction.md`. The report is supplied here as
sandbox `report.md`; the delivery tool installs it at
`coord/reports/F7/Sheaf.Paper.BasicOperationsCoefficientReduction.md`. For a reviewer fix directory, the supported report alias is
`Sheaf.Paper.BasicOperationsCoefficientReduction.report.md`; the landing tool maps
that alias to the complete report path.
The retained Lean and DAG packet has been compared with current `sheaf-dag`; the
existing declaration signatures and definition bodies remain those of current source.
The delivery tool rebuilds the commit on the freshly fetched `sheaf-dag` tip.

Repair of returned head `b270ea00522` (reviewer `C-b270e`): the two new nodes no
longer carry an identical inherited proof-dependency list. Each now records only
the earlier results used by its own argument, with the same list in the proof
step's `uses`. The parent still assembles their unchanged Lean conclusions.
The complete current DAG plus this packet was checked for a path from either
new node back to `lem-fix-operation-reduction`, including every transitive
statement and proof dependency. Neither path exists.

Change record: `coord/changes/F7-operation-coefficient-interface-dependency.md`.

## Proved and sorry left

Closed the one original hole in `WeilConjectures.basicOperationsCoefficientReduction`.
The item has zero remaining sorries. Added two holes:

- `WeilConjectures.basicOperationReductionAndEvaluation`
  (`lem-fix-basic-operation-reduction-and-evaluation`).
- `WeilConjectures.basicOperationCoefficientCoherence`
  (`lem-fix-basic-operation-coefficient-coherence`).

This is a decomposition: one hole closed and two added, net -1. Each lower statement
contains a strict part of the original conclusion and has the source and complete
argument in words in its docstring. The rational/common-stage representative and
pullback-coherence clauses are supplied directly by existing declarations.


Reviewer FIX (2026-10-25, re-applied a third time; the reviewers of `28abdf8a8d5` and
`b270ea00522` made the same correction, and this re-delivery dropped it again): eight of
the twelve clauses first placed in `basicOperationReductionAndEvaluation` were already
stated in the library and are now applied directly in the item:
`integralOperations_preserve_constructible` (integral pullback/tensor),
`sfIntegralDirectImage_constructible` (direct image, first two parts),
`Scheme.finiteCompactSupportConstructibility` (finite-level compact support; finite-Tor
constructibility contains intrinsic constructibility), `integralHomReduction` (integral Hom),
`integralOperationsScalarExtension` (scalar comparisons; the stalk-unit hypothesis follows
from invertibility in the residue field), the quotient condition of `derivedPullbackTensorIso`,
and the two `IsIso` clauses on the isomorphisms `canonicalFinitePullbackTensor` and
`pullbackTensorQuotient` (instances). `basicOperationReductionAndEvaluation` now states only
integral compact-support reduction, finite quotient evaluation, site-perfect finite Hom
reduction and integral scalar Hom evaluation; it no longer takes `Ω` or the residue-field
instances. The item's `proof_deps` gain the five library nodes used directly; two of them
(`lem-sf-integral-direct-image-constructible`, `prop-finite-compact-support-constructibility`)
already lie on a base-DAG cycle with the item, which the landing check permits. The
new node keeps the worker's cycle-free dependency list, without
`lem-pur-integral-operations-preserve-constructible` and `lem-coef-integral-hom-reduction`
(their clauses moved to the item), and without the `Ω` definitions in its `stmt_deps`.

## No longer needed

Removed direct proof imports from the item (after the reviewer FIX the item imports
`Sheaf.Paper.IntegralOperationsPreserveConstructible` again, for
`integralOperations_preserve_constructible`):

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`.
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`.
- `Sheaf.CategoryTheory.FlatRingedDiagramRestriction`.
- `Sheaf.CategoryTheory.RingedSitePerfectDuality`.
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.Paper.CompletedConstantSheafReduction`.
- `Sheaf.Paper.CompletedDirectImageLimits`.
- `Sheaf.Paper.CompletedOpenExchangeTransport`.
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`.
- `Sheaf.Paper.PerfectProjectionFormula`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.Paper.QcqsCompactSupportRealization`.
- `Sheaf.Paper.RingedProjectionRestriction`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Paper.ScalarExtensionExactIntrinsic`.
- `Sheaf.Paper.SfCommonStageDirectImage`.
- `Sheaf.Paper.SfRationalizationKaroubi`.
- `Sheaf.Paper.SitePerfectComplex`.
- `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange`.

These imports are not required by the combining proof; relevant declarations remain
dependencies of the two retained mathematical parts. No existing module or DAG node
is withdrawn. The parent's obsolete direct `tool_uses` approvals are removed; the retained
parts record their separate ambient proof dependencies. The blueprint unit and its realized argument remain in place.

Further dependency pruning in the repair:

From `lem-fix-basic-operation-reduction-and-evaluation`, remove dependencies belonging to the other part:

- `def-weil-algebraically-closed-coefficients`.
- `def-weil-rationalization-karoubi`.
- `lem-amb-mate-unit-counit`.
- `lem-fix-scalar-completion-associator`.
- `lem-pur-mate-unit-compatibility`.
- `lem-pur-semilinear-scalar-localization`.
- `lem-sp-categorical-projection-mate-square`.
- `lem-sp-finite-free-direct-image-coherence`.
- `lem-weil-pbc-coefficient-exchange-mates`.
- `lem-weil-scalar-extension-composition`.
- `lem-weil-scalar-extension-exact-triangulated`.

From `lem-fix-basic-operation-coefficient-coherence`, remove dependencies belonging to the other part:

- `lem-coef-integral-hom-reduction`.
- `lem-fix-internal-hom-comparison-composition`.
- `lem-fix-site-perfect-scalar-hom`.
- `lem-pur-completed-operation-tower-substitution`.
- `lem-pur-integral-coherence-tower`.
- `lem-pur-integral-operations-preserve-constructible`.
- `lem-pur-integral-operations-scalar-extension`.
- `lem-sf-ringed-finite-free-hom-base-change`.
- `lem-sfb-ringed-derived-monoidal-comparisons`.
- `lem-sfb-ringed-site-perfect-duality`.
- `lem-weil-l-adic-extension-integers-dvr`.
- `lem-weil-pbc-standard-quotients-perfect`.
- `lemma-weil-pbc-perfect-projection-formula`.
- `prop-weil-pbc-direct-image-limits`.

The excluded downstream route is
`def-weil-derived-direct-image` → `lem-sf-integral-pullback-linear-adjunction` →
`def-weil-system-operation-exchange-realization` → `lem-fix-operation-reduction`.
The compact-support package and aggregate coefficient-law node also reach that
route. They must not be reintroduced as proof dependencies of the new lemmas:
their arguments use the earlier ambient tensor, projection, finite-free and
limit results named in their own dependency lists. Existing downstream nodes and
all their Lean declarations remain in the library.

## Where the brief, the DAG or earlier work was wrong

The attempted general representative-normalization route required additional control
of the chosen monoidal associator. That interface repair is not included in this
packet. The retained finite-reduction/evaluation part states the specific canonical
operation laws, whose natural-language argument uses the intended normalized structures.
The integral action cocycle must be established before rationalization; localization
is not generally faithful on torsion Hom groups.

The repair dispatch reset the reference clock after the completed delivery
`28abdf8a8d5`; no clock metadata was edited by this worker. That retry repaired the report handoff. The present repair dispatch again reset
the reference clock after `b270ea00522`; it is not mathematical progress.

## New nodes

`lem-fix-basic-operation-reduction-and-evaluation` groups the finite and integral
reduction, constructibility, and evaluation argument (steps 1--7 and scalar evaluation).

`lem-fix-basic-operation-coefficient-coherence` groups completed direct-image and
compact-support coefficient actions, scalar towers, and mate equations (steps 8--10).

The new nodes avoid dependency edges through the downstream exchange-realization
package, which itself cites operation reduction. Their proofs use the earlier ambient
operation and coefficient-comparison declarations instead. The unit-route import
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` is retained.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
