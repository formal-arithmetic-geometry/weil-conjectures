## What changed

Proved the three clauses of
AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.twoSubstitutions from the
existing exchangeSubstitution theorem, naturality, and the strictly smaller single-square
completedExchange_reduction obligation. The first clause uses naturality of the strict
exchange. The second uses naturality of mu and then applies the strict second-support
functor and Rlim to the reduction square. The endpoint equality is map_comp and
associativity. No equality is inferred from Rlim or finite evaluations.

Relocated the ambient prefix, through exchangeSubstitution, verbatim to
Sheaf.Paper.CompletedSupportIntermediateTowerCore so that both the original module and
Sheaf.Paper.CompletedSupportExchangeReduction can use it without a cycle. The original
public import preserves the API, names, types and definition bodies. This refactor is for
dependency sharing, not compile time. The finite/origin definitions and assertions remain
in the original module. Launcher compiles passed: Core 56.4 s, reduction-square module
46.1 s, and the final original module 50.5 s; no debug options remain. Source comparisons
verify the relocated prefix and unchanged finite/origin code and public theorem signature. Restored the three private `import all` proof imports there. Three proved private generic
transport lemmas keep kernel checking from expanding the concrete coefficient constructions.

## Proved and sorry left

Original holes: 7. Closed: twoSubstitutions. Added: completedExchange_reduction, node
lem-cbc-completed-support-exchange-reduction. This is a decomposition, with net hole change
zero, not a completed independent proof of the exchange compatibility. Total remaining: 7.
All names below have namespace AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.

The original module retains these 3 holes:

- finiteOpenTensor_isIso: lem-cbc-completed-support-finite-open-tensor-iso.
- finiteRingUnit_isIso: lem-cbc-completed-support-finite-ring-unit-iso.
- strictFiniteCoherence: lem-cbc-completed-support-intermediate-tower.

The Core module preserves these 3 existing holes, unchanged and neither closed nor added:

- strictUnits: lem-cbc-completed-support-ambient-comparisons.
- completionUnits: lem-cbc-completed-support-ambient-comparisons.
- exchangeSubstitution: lem-cbc-completed-support-ambient-comparisons.

The reduction module has the 1 new hole:

- completedExchange_reduction: lem-cbc-completed-support-exchange-reduction.

The new square is strictly part of the argument: it concerns one exchange on strict
reduction towers, with no successive support operation, finite origins or limit transport.
Identity squares reduce to the unit-normalized square; empty opens and zero complexes give
the unique zero morphisms. No common lower bound or completeness of the input is assumed.

## No longer needed

No mathematical node or module is withdrawn. Every original public import is now exported
through Core; none is pruned from the library. SupportProperUnitNormalization stays a
private proof import of Core, where reconstructionNormalization uses it. The original
module needs only the public Core import, the private proof imports `import all` of
FiniteConstantCoefficientTransport and ProEtaleOperations, plus the new reduction-square
proof import. Reviewer correction: `import all Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows`
is removed from the original module, which compiles without it (Core keeps its own copy); the finite part's
private helpers (inverseMate_isIso_of_equivalences, finiteScalarMap_unit) come from
`import all` of FiniteConstantCoefficientTransport. The ambient proof dependencies move to the
ambient node; the original node records its actual finite and substitution argument.
No claim of faithfulness of Rlim, or of derived evaluation on arbitrary morphisms, is needed.

## Where the brief, the DAG or earlier work was wrong

The node's old last substitution step compresses a strict reduction compatibility into
naturality after the limit exchange formula. The actual second calculation needs that
strict square; it cannot be obtained merely by cancelling Rlim. The new node makes this
precise and the Lean proof exhibits how it is used. No target statement or unit route
changes. The untouched finiteOpenTensor_isIso proof sketch calls the open adjunctions
equivalences; that explanation is inaccurate for a nontrivial open immersion. Its statement
needs the localized support/tensor argument instead. The latest blueprint proof now presents the proper-then-open composite and
naturality, rather than the older detailed final compatibility paragraph named by the
reviewed node. The detailed normalization followed here is the reviewed node Steps 9--11,
with Stacks 099M/099N and the ringed tensor/mate prerequisites.

## New nodes

lem-cbc-completed-support-ambient-comparisons attaches the relocated ambient definitions
and assertions, with their original proofs and original three remaining holes. Its proof
steps are the corresponding existing steps, so it introduces no additional obligation.

lem-cbc-completed-support-exchange-reduction states the one-exchange reduction square,
strictly before Rlim and evaluation. Its first step is proper/open tensor-mate coherence;
its second cancels the reduced completion units. This is the only newly postponed theorem.

Change record: coord/changes/completed-support-exchange-reduction-W3.md.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
