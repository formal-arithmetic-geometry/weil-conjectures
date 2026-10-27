## What changed

Replaced the hole in `WeilConjectures.OpenFactorCoherence.openFactorOpenRealization`
with an assembly proof, preserving its complete signature and the existing public imports.
The proof imports three new comparison modules, the published equivalence between the
completeness predicates, integral constructibility as an object property, and the existing
ordinary open coefficient data. A proof-only `import all` of that coefficient data
makes its proved slice-presentation helper available locally. Both `respectTransparency`
options stay enabled, and instance exclusions are scoped to individual proof declarations.
No other existing Lean module is changed.

The completed-open commutation is proved directly from the actual-unit reflector Hom
bijections and the ordinary open adjunction. Transported completeness preservation makes
both units universal into complete objects. Factoring each through the other proves the
isomorphism, its naturality, its actual-unit equation, and uniqueness. A private generic
lemma contains this argument in full. Separate private proofs establish the equivalence
of completeness predicates, full faithfulness of the fixed open extension, and preservation
of each individual reduction interval. The latter uses exact intrinsic finite-coefficient
extension and homology; it also handles empty intervals. The remaining structure fields
are filled using the existing comparison and constructibility assertions, with their
specified functor presentations transported by ordinary natural isomorphisms.

Three strictly smaller normalization steps remain as new theorem modules. They concern
ordinary coefficient transport, the strict augmented extension tower, and the strict
completed-pullback model. Each has its source, proof in words, edge-case discussion, and
DAG attachment. The original node now records the argument actually written. The
blueprint unit and its realized statement/steps are unchanged.

Validation: `lcompile.py --all` accepted all three new statement modules. The final,
unprofiled assigned module passed `lcompile.py` without warnings in 5.0 seconds; the
delivery also runs its own compile and preflight. The given finite-field characteristic
and `hl` construct the universe-zero datum used to compare the completeness predicates,
preserving the original signature.
All new Lean lines are within 100 characters. No profiling or trace options remain.

## Proved and sorry left

Original holes: 1. Original holes replaced by a complete Lean proof: 1,
`WeilConjectures.OpenFactorCoherence.openFactorOpenRealization`
(node `lem-sf-open-factor-open-realization`). The assigned module has zero remaining holes.

Added holes: 3, exactly one in each new module:

- `WeilConjectures.OpenFactorCoherence.openFactorOrdinaryTransport`,
  node `lem-sf-open-factor-ordinary-transport`.
- `WeilConjectures.OpenFactorCoherence.openFactorQuotientRealization`,
  node `lem-sf-open-factor-quotient-realization`.
- `WeilConjectures.OpenFactorCoherence.openFactorPullRealization`,
  node `lem-sf-open-factor-pull-realization`.

This is a decomposition of the original obligation, not a claim of net hole reduction:
one original hole is removed and three smaller holes are added. No hole occurs in a
definition, private helper, or the assembly proof. Existing imported theorem holes are
not changed by this packet.

## No longer needed

No original public import was removed, and no module is withdrawn.

The assembly no longer uses `lem-cbc-exact-product-functor-strict-limit`
(`Sheaf.Paper.ExactProductFunctorStrictLimit`): reflector uniqueness and the
open adjunction construct the completion comparison without a new product/Roos comparison.
It no longer uses `lem-sf-open-finite-constructibility-interval`
(`Sheaf.Paper.OpenFiniteConstructibilityInterval`) or the `q.finiteGeometry` field
for its individual-interval conclusion: exact finite extension transports vanishing at
each degree directly. These two nodes are removed from this node's proof dependencies.
This is local dependency pruning; existing retained imports can still use those nodes
transitively, so this packet makes no global withdrawal claim.

The new tower statement asserts no completion commutation. Neither new realization
statement asserts constructibility, complete Hom equivalence, scalar-mate invertibility,
or interval preservation: these conclusions are proved or transported in the parent.

## Where the brief, the DAG or earlier work was wrong

The old interval proof text proposed applying `q.finiteGeometry` even for empty intervals.
That assertion takes an ordering hypothesis `a ≤ b`, whereas the assigned conclusion
has no such hypothesis. The exact finite extension argument proves the unchanged
conclusion for all endpoints, including `a > b`.

The old planned exact-product comparison is unnecessary for completion commutation once
both fixed open functors preserve complete objects and the actual-unit reflector
assertions are available. The adjunction identifies the two universal arrows instead.

The ordinary comparison supplied by slice normalization has a genuine coefficient/site
identification to prove; it is not definitional equality between the two presentations.
The new ordinary transport statement isolates this issue before derived localization.
The strict tower and pullback statements retain the augmentation/generator equations and
are not inferred from isomorphisms of separate derived evaluations. Empty and identity
opens and zero complexes require no extra hypotheses in these statements.

## New nodes

`lem-sf-open-factor-ordinary-transport`: identifies ordinary slice extension and
restriction with the published fixed coefficient functors. Its proof first determines
finite maps by constant sections, then the completed map by its jointly monic quotient
projections, then uses the concrete site equivalence and adjoint uniqueness. It is
strictly before, and contains none of, the completion/tower/geometry conclusions.

`lem-sf-open-factor-quotient-realization`: the three extension-tower fields only, before
derived localization. Scalar comparison and strict transitions produce the tower;
the quotient augmentation gives its normalization and epi cancellation its uniqueness.
It contains no completed comparison or complete-object hypotheses/conclusions.

`lem-sf-open-factor-pull-realization`: the fixed strict quotient-generator model of
completed open pullback only, including good representatives and its Roos localization
normalization. The parent separately proves invertibility of its unit on complete
inputs and all extension, completeness and geometry conclusions.

No change records are needed: no existing definition, statement, public import,
instance, attribute, or other module interface is changed.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
