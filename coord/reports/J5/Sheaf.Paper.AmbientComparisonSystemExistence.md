## What changed

Restored and reduced `Sheaf.Paper.AmbientComparisonSystemExistence` without changing
`WeilConjectures.ambientComparisonSystem_exists` or withdrawing its quarantined
archive, Lean attachment or parent dependencies. The proof constructs normalized
Roos models over arbitrary schemes from fixed-calculus completion models. It
constructs and descends the primitive pullback comparison over arbitrary schemes,
checks its whole-system coherent normalization, proves scalar normalization of
transported reduction systems without the unused residue-unit hypothesis, and
obtains the actual scalar and pullback counits and completion unit from normalized
reconstruction. It combines these with a single remaining scalar-model step.

Corrected the auxiliary scalar normalization predicate in
`IntegralComparisonRealizationModels`: representative tests now require the same
existing whole-system adjunction coherence as pullback tests. The strict generator
formula, realization and Roos equation stay identical. The completed scalar
uniqueness proof in `PrimitiveQuotientRealizationsUnique` now chooses a coherent
presentation and supplies its coherence proof. Existing public names, signatures,
imports and target statements remain unchanged. No source-library file changes.

Optimized the unclaimed direct consumer `CoherentQuotientOrdinaryLift` after its
original source exceeded the 60-second compile limit. Its existing local
irreducibility list now also protects the completed and sequence coefficient-ring
constructions. Profiling reduced the compile from 64 seconds to 34.4 seconds;
the final source compiles in 36.3 seconds. All profiling options are removed
from the submitted file. Its proof, public
signature, global attributes and imports are unchanged.

Returned delivery C-ff1d2: reverted the complete IntegralTowerInverseImageUnit
extraction and all associated local attributes. The published module, its imports,
proofs and original DAG node are left untouched. The proposed private support
module and its proposed attachment are absent from the repaired packet. The
reviewer's published-original compile of 48.0 seconds supersedes the earlier
local timing rationale; no timing-based justification is claimed for that change.

The direct consumer `OrdinaryQuotientPullbackTowerComparison` exceeded the limit
at 66 seconds; local unfolding experiments still exceeded it or hid essential
generator types. Its existing proved private construction is extracted verbatim
into the proof-only modules `OrdinaryQuotientPullbackTowerLevels` and
`OrdinaryQuotientPullbackTowerConstruction`, connected with `import all`. The public theorem, assembly proof and public imports remain
in their original file. This adds no mathematical statement or hole.

Change record: `coord/changes/J5-scalar-presentation-coherence.md`. The interface
node records the correction and all 65 DAG citers; the item, uniqueness and
associativity nodes record their actual proof routes. The item compiles in 47.7 seconds. The original pullback-counit projection
consumer passed in 55.6 seconds after its timing profile; it needs no source change.
The original direct-import scan missed transitive users of the scalar model's
normalization field. The repaired consumer audit includes the model structure's
18 textual users, the forced transport and associativity adaptations, and a fresh
check of ExplicitScalarConeWordCoordinates. The earlier statement that two named
predicate mentions exhausted the consumers was wrong. All 32 direct importers
were checked against the correction; the final
three-file pullback-tower construction split also passes its compile check. All unchanged consumer
copies are removed before submission. The concurrently updated
ExplicitScalarConeWordCoordinates was refreshed and rechecked in 47.6 seconds. The repaired transport and the current published ExplicitScalarConeWordCoordinates
both pass the server compile check (exit 0); the unchanged cone source is removed
from the delivery packet. The returned transport and associativity consumers are
now included as forced
adaptations; their exact changes and original diagnostics are recorded below.
No second worker was started, as required by this dispatch brief.

Landing return af4aa4783 repaired: included the newly proved
ScalarModelIteratedStrictCalculation and ScalarModelUnit. Unit supplies its existing
coherence witness. The iterated calculation's former arbitrary-presentation
statement needs the same explicit correction as the scalar normalization predicate:
it now requires whole-system coherence, and associativity passes its existing
witness. This is an intermediate statement correction, not a proof of its old
arbitrary-presentation form. No target or parent associativity/unit statement changes.
See coord/changes/J5-iterated-scalar-presentation-coherence.md for old/new signatures,
edge cases, the one caller and one DAG citer. Neither module is claimed in the
current local mirror; E9 delivered the calculation proof and D2 its statement.

The repaired current modules compile together with their direct importer:
ScalarModelIteratedStrictCalculation 58.0 s, ScalarModelUnit 37.6 s,
ScalarModelAssociativity 16.3 s and CounitRealizationSubstitution 41.3 s
(server check exit 0). The unchanged last module is removed from the packet.
The new calculation proof initially took 61.3 s; profiling showed type checking
and linting dominate. Its existing local irreducibility list now also protects
coefficientConstantTowerLimit and completedOrdinaryScalarComplex. These local
annotations export no attribute and change no public definition. No profiling
options remain. Protecting coefficientSequenceLimit itself hid a required bridge
conversion and was reverted before the successful check.

## Proved and sorry left

Closed the original body of `WeilConjectures.ambientComparisonSystem_exists`
(node `lem-trf-ambient-comparison-system-existence`) by a complete assembly from
existing declarations and the single scalar-model step. Its module has zero
remaining holes. Its private Roos, ambient pullback, scalar normalization and
constructible completion-unit proofs are complete.

Added one named hole:
`WeilConjectures.ambientQuotientScalarModel_exists`, node
`lem-trf-ambient-quotient-scalar-model-existence`, in the new module
`Sheaf.Paper.AmbientQuotientScalarModelExistence`. It concerns only one scalar
embedding at one arbitrary scheme, with a fixed source calculus and target Roos
model; it asserts no pullback, effectivity, simultaneous choice or coherence law.
Its complete proof in words describes the strict balanced tensor comparison and
descent. Canonical coherent presentations include every flat-term K-flat input.

This is a decomposition: one original hole closed and one strictly smaller hole
added, net zero holes. It is not claimed as a sorry-free proof of the entire
construction. The repaired model definition and adapted uniqueness proof have
zero holes; the extracted private construction is also fully proved. No existing
proved body is replaced by a hole.

## No longer needed

No original public import is removed, and no module is withdrawn. The three
original proof dependencies remain in use through their published interfaces:
`def-trf-integral-comparison-realization-models`,
`def-trf-integral-comparison-sequence-systems`, and
`lem-coef-derived-system-evaluation-calculus`.

The proof does not need the global ell-invertible package
`EffectiveComparisonRealizationModels`, the simultaneous-choice theorem
`effectiveQuotientModelsSimultaneous`, the disputed monolithic
`effectiveQuotientModelDescent`, or the disputed arbitrary-realization scalar
normalization theorem. It instead constructs ambient pullback directly from
fixed-calculus models and coherent strict comparison. No global pruning of these
modules is claimed: other parents still use them. No unit statement or unit route
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The return identified two omitted forced adaptations: scalar transport and scalar
associativity. Both consume the normalization projection through the model
structure rather than mentioning the predicate by name. The original change
record's two-textual-user claim was therefore insufficient and is corrected.

The original one-step proof plan cited definitions but did not provide the ambient
primitive constructions. The available primitive existence packages mostly
required ell invertible on the base, whereas this item asks for primitive models
on every scheme. The ordinary/derived fixed-calculus model theorem and coherent
strict quotient comparison actually suffice for the ambient Roos and pullback
construction. The existing scalar normalization proof does not use its
residue-unit argument, and its strict representative construction applies
without it.

The old scalar normalization has the same invisible-presentation-twist defect
already documented for pullback in the T6 and S9 reports. Finite derived
evaluation is conservative, but not faithful. The correction reuses the existing
whole-system coherence predicate; its two adjunction Hom bijections determine e
before taking a limit. The change record includes the explicit derived-complete
nonclosed-image test and the consumer audit. Canonical coherent presentations
exist for every good complex, including zero and empty-scheme cases, exponent one
and identity coefficient embeddings. No bound or geometric restriction is added.

STATEMENT-DISPUTED: the old arbitrary-presentation form of
scalarModelIteratedStrictCalculation has the same invisible-twist defect. The
landing repair adds the missing coherent-presentation hypothesis explicitly;
canonical coherent inputs already used by its only caller meet it. No new hole.

STATEMENT-DISPUTED: the existing `primitiveQuotientScalarModelNormalization` is stated
for an arbitrary natural realization, which does not select its normalization.
Negating a realization already violates the fixed generator equation. This is a
pre-existing Lean/node mismatch: its node describes the constructed realization.
It remains an independent disputed obligation and is not used here. This packet
introduces only existence of the correctly normalized scalar comparison.

The rework row's quarantine archive was read and retained. Its absence from a
previous live build is not treated as a withdrawal. The ancestor helper reports
None for the module-named creation chain; the existing item's explicit nearest
blueprint ancestor `prop-trf-karoubi-independence` is preserved for the new node.
The latest blueprint has reorganized trace transport; its integral transport
proof still requires scalar extension to commute with the actual pullback maps,
units and composition. The same canonical quotient construction serves that
step.

Tool uses from other units retained for review: unrestricted normalized
reconstruction (`lem-pod-unrestricted-normalized-reconstruction`) and the
intrinsic/legacy completeness bridge (`lem-sf-derived-complete-legacy-comparison`)
are the existing precise APIs for the actual unit and counits. The finite scalar
association and strict representative lemmas supply the quotient tensor
normalization. No same-unit theorem supplies these general reconstruction and
scalar representative facts; no maintainer tool approval was edited.

## Forced adaptations

Fresh compiles of both published originals against the corrected interface
reproduce `Tactic rcases failed ... IsIntegralComparisonPresentationCoherent ... →
∃ q, ... is not an inductive datatype`, at transport 130:11 and associativity
124:11. Their full diagnostics are retained in scratch. These are type errors,
independent of the previous timing-based adaptation rationale.

`Sheaf.Paper.PrimitiveQuotientRealizationsTransport` (unclaimed in the local mirror):
the returned original fails at its old line 130, where `rcases` tries to destruct
`M.normalization P C (a.app _ ≪≫ e) κ hpT`, now an implication requiring whole-system
coherence. In `transportedScalarModel.normalization`, the proof now introduces
`hc`, transports its strict augmentation witness to `hcT` using the same
left-adjoint-unit equation as the existing pullback proof, and supplies `hcT` to
`M.normalization`. Only that private proof body changes. All public signatures,
visibility, imports and the pullback proof are identical to current main.

`Sheaf.TraceFormula.ScalarModelAssociativity` (D2, per return C-ff1d2): the original
fails at old line 124, where `bEF.normalization P C₀ e κ hC` is now an implication
rather than the expected existential. A private import of
`CoherentPrimitiveReductionPresentation` replaces the old arbitrary reduction
presentation by its coherent presentation, and the extra witness `hcoh` is passed
to normalization. The repaired module passes the server compile check (exit 0). These are the only
three changed source lines; the complete
public theorem statement and remaining proof stay identical. Its node's second
proof step records the coherent-presentation dependency.

`Sheaf.Paper.ExplicitScalarConeWordCoordinates` (M8) is a verification consumer:
its original source is compiled against the repaired transport and removed from
the delivery afterwards. No proof or signature in that module is changed.

`Sheaf.TraceFormula.ScalarModelUnit` (unclaimed in current local mirror) now has a
completed proof; its original fails at 90:9 because normalization returns a
coherence implication. The sole source edit passes the existing `hc` from its
coherentPrimitiveReductionPresentation before the proof destructs that witness.
All statements, imports, attributes and remaining proof lines are identical.

`Sheaf.TraceFormula.ScalarModelIteratedStrictCalculation` (unclaimed in current
local mirror; E9 proof/D2 statement) now has a completed proof. Its original fails
at 187:9 on `bEL.normalization P C e κ hC`. The given arbitrary e has no coherence
witness; finite evaluation equations cannot provide one. Its explicit statement
correction adds hcoh and passes it to normalization. The public conclusion and
remaining proof stay identical. The only caller is ScalarModelAssociativity,
which supplies its existing hcoh; its public statement is unchanged. This
statement correction is separately recorded for independent review and is not
claimed as a signature-preserving forced proof adaptation.

The calculation's two added local irreducibility annotations are needed for the
standalone timing gate after the current proved source replaced the stub. They
are local to that proof module and preserve the public interface of every
unchanged consumer. The original 61.3 s failure and the final 58.0 s passing
compile are recorded in the launcher result files and copied into scratch.

## New nodes

`lem-trf-ambient-quotient-scalar-model-existence` isolates the single-scheme scalar
part of the parent construction. Its fixed source calculus and target Roos model
are arbitrary. Its source, complete strict-system proof plan, actual three-kind
searches, edge cases and Lean attachment are recorded in its module and node.
It is strictly smaller than the simultaneous ambient system: all Roos and
pullback construction, effectivity and final assembly are proved in the item.

The proof-only modules `OrdinaryQuotientPullbackTowerLevels` and
`OrdinaryQuotientPullbackTowerConstruction` contain the existing private
construction verbatim, with no new public statement. Their two DAG nodes record the existing private
canonical_exists theorem and comparison definition, as preflight requires each
new module to have an attachment. A first
single-module extraction still exceeded the limit, so finite-level evaluation
and tower assembly are separated.

`lem-trf-ordinary-quotient-pullback-tower-levels` records the existing proved
private direct-image/evaluation comparison in the extracted Levels module.
`def-trf-ordinary-quotient-pullback-tower-construction` records the existing private
natural tower isomorphism definition in the Construction module. Neither adds
a hole or a new public declaration. The original public theorem node now records
these exact proof dependencies. These are file-extraction attachments, not new
mathematical obligations.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
