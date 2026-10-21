## What changed

Proved AlgebraicGeometry.Scheme.CompletedScalar.completedScalarUnitAdjunction by
assembling the existing quotient reflector and coefficient equivalence, normalized
scalar-limit comparison, strict balancing, ordinary derived adjunctions and
categorical mate identities. All original public signatures and definitions are
unchanged. The main proof constructs the unique unit-normalized pullback comparison,
its reconstruction equation, completed Hom bijections, units, counits, conjugation
compatibility and change-of-input equation.

Added three proved auxiliary modules: StrictScalarCompletionUnit computes the actual
quotient-unit square on flat-term K-flat representatives and extends it by localization;
StrictScalarOrdinaryAdjointsExist constructs ordinary unbounded derived adjunctions
and proves their scalar mate invertible; StrictScalarOrdinaryAdjunction establishes
completeness preservation and transports it to arbitrary stipulated pullback models.
The main node and three new node records describe this proof route. No existing definition,
statement, source-library declaration or consumer was changed. The change record
coord/changes/A9-completed-scalar-unit-proof-environment.md documents the added local
namespace opening and backward-defeq elaboration option required by preflight.

Validation: all four modules passed the prescribed lcompile.py checks without errors
or warnings. The helper modules took 58.6, 34.7 and 5.6 seconds in the full sandbox
check; after the final reconstruction rewrite repair, the main module compiled cleanly
in 18.0 seconds. The original public definitions, structure fields and theorem
signature were compared directly with the shared source and are unchanged.

## Proved and sorry left

Closed the original one hole:
AlgebraicGeometry.Scheme.CompletedScalar.completedScalarUnitAdjunction.
Added zero holes. No sorry remains in any delivered module. The new proved declarations
are AlgebraicGeometry.Scheme.CompletedScalarUnitProof.strictScalarCompletionUnit,
AlgebraicGeometry.Scheme.StrictScalarBalancing.strictScalarOrdinaryAdjointsExist and
AlgebraicGeometry.Scheme.StrictScalarBalancing.strictScalarOrdinaryAdjunction.
They are fully proved results, not unfinished split-offs. Existing imported statements
retain their own proof obligations; this delivery proves the assigned theorem from
the published declarations, as required by stage 3.

## No longer needed

Removed the main module's eight old proof-only imports:
Sheaf.Paper.PbcQbarCompletedPullback,
Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations,
Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage,
Sheaf.CategoryTheory.DiagramSiteRealization,
Sheaf.CategoryTheory.FlatRingedDiagramRestriction,
Sheaf.Paper.CompletedDirectImageLimits,
Sheaf.Paper.KoszulReconstruction and
Sheaf.CategoryTheory.RingedKoszulCompletionReflector.

Also removed unused candidate imports of KFlatResolutionIndependentCoefficients and
TensorColimitsIndependentCoefficients from the completion-unit helper and
ExactPullbackDerivedAdjunction from the ordinary-adjoint existence helper. Replaced
SmallModuleDiagramsGrothendieck there by the actual generic module-sheaf
K-injective-resolution module.

The actual proof uses the published strict small-site constructions directly. It
needs neither the generic diagram-site realization nor the generic flat-ringed
comparison theorem as an additional input; the ordinary mate is proved for the
stipulated normalized pullback models. The reflector API already published in
ConstantCompletionEquivalence supplies the quotient criterion and universal property,
so no second invocation of the ringed reflector or reconstruction theorem is needed.
Completeness preservation is proved using the constant direct-image theorem and
scalar restriction, rather than importing CompletedDirectImageLimits. The chosen
normalized limit comparison is the derivedLimitRestriction API already exported by
ConstantCompletionEquivalence; no separate application of FlatScalarTowerLimitSquare
is needed.

Accordingly the main node no longer has direct proof edges to
def-weil-pbc-adjunction-conjugate, def-weil-pbc-completed-pullback,
def-weil-pbc-proetale-operations,
lem-weil-pbc-flat-ringed-diagram-restriction,
lem-weil-pbc-flat-scalar-tower-limit-square,
lem-weil-pbc-profinite-coefficient-inverse-image,
lem-weil-pbc-ringed-koszul-completion-reflector,
prop-weil-pbc-direct-image-limits or prop-weil-pbc-koszul-reconstruction.
Statement dependencies are preserved. No module is withdrawn and no whole-library
pruning is claimed: some of these inputs remain dependencies of the published
constructions and reflector theorem. The unit's own realized statements and steps
are untouched.

## Where the brief, the DAG or earlier work was wrong

The retained candidate had an unfinished ordinary-adjunction theorem and unverified
assembly. Those proofs have now been completed. The ordinary scalar mate argument
uses the underlying additive sheaf adjunction, then K-injective resolutions and the
representative normalization of the stipulated pullback. This avoids assuming that
an arbitrary invertible left comparison automatically has an invertible mate.

The old prose's constant-tower calculation is implemented using the published
quotientPresentation laws, which directly normalize the actual quotient completion
units. The generic categorical square in StrictScalarCompletionUnit avoids repeated
unfolding of derived constructions. Its hypotheses mirror the normalized equations
directly, so no large concrete scalar/limit identity is rewritten inside the specialization.
The zero ideal, unit ideal and empty generating family require no exclusions.

The earlier missing mirrored StrictQuotientScalarBalancing artifact no longer blocks
compilation. No launcher scripts, shared source files, environment compile switches
or build outputs were modified. The required initial delivery check rejected the
then-retained single new sorry; it has been proved in this session.

The delivery preflight requested a change record for the added proof-elaboration
commands; that record and its consumer check are now included. No Lean edit was
needed for this preflight diagnostic.

A read-only dependency audit also found a pre-existing two-node cycle in the shared
DAG: lem-pc-ring-hom-extension-differential cites
lem-pc-ring-hom-extension-differential-adjacent, which cites it back. Neither node is
changed by this packet. The new dependency edges were separately checked and do not
introduce a cycle.

## New nodes

lem-weil-pbc-strict-scalar-completion-unit: the ambient quotient completion-unit
identity, with its actual ordinary-limit normalization. Its proof uses the strict
quotient laws and scalar preservation of flat-term K-flat representatives.

lem-weil-pbc-strict-scalar-ordinary-adjoints-exist: the separate ordinary geometric
unbounded derived adjunction and normalized invertible scalar mate. Its proof computes
the ordinary mate on underlying sheaves and the derived mate on K-injective targets.

lem-weil-pbc-strict-scalar-ordinary-adjunction: completeness preservation for those
right adjoints. Constant direct image supplies the generic complete-object theorem;
restriction reflects completeness and the normalized mate transports the assertion.
The off-unit adjunction and constant direct-image theorems are declared as generic
tool uses for independent review; they replace no proper-base-change unit step.

All three nodes have proved Lean attachments and search records. Blueprint searches
for completion-unit scalar, ordinary scalar adjunction and right-adjoint completeness
found no separate matching blueprint nodes. Their dependency edges introduce no cycle.
Change record: coord/changes/A9-completed-scalar-unit-proof-environment.md. It documents
proof elaboration commands, identical existing public API and the consumer check.
No forced adaptations.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
