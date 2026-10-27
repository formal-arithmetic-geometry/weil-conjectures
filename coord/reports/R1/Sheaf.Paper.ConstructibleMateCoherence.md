## What changed

Proved the abstract mate and lifted-adjunction assertion directly from the existing
invertible-mate and IsoAlgebra adjunction API. The same specified mate supplies the
right lift, original unit and counit, and both triangles. The covariant lift
specification is proved from the concrete IsoAlgebra functor, without invoking the
unfinished general field-lift theorem.

Reduced the two normalized Hom-first evaluation assertions to evaluation naturality
and the existing evaluation-defined Hom-comparison laws. A private, fully proved
categorical calculation cancels the inverse first-variable Weil structure and moves
the second-variable structure to the output. The rational naturality theorem already
exists. The missing common-stage naturality statement is split off with a source,
proof in words, and a new node. No public signature or definition changes.

Validation: the new common-stage statement compiled in 56.2 seconds and the
complete item compiled in 37.5 seconds using the sandbox overlay. The item
reports no errors. The two evaluation declarations locally disable the
unused-variable linter: their named instance binders occur only implicitly,
and their existing public signatures are preserved verbatim. The final delivery command performs
the independent preflight and compile checks.

## Proved and sorry left

Original holes closed (three of six):

- WeilConjectures.PodConstructibleMate.adjunction_coherent.
- WeilConjectures.PodConstructibleMate.rational_evaluation_equivariant, using the
  existing normalizedRationalEvaluation_naturality and Hom-comparison laws.
- WeilConjectures.PodConstructibleMate.common_evaluation_equivariant, decomposed
  using the new normalizedCommonEvaluation_naturality and existing Hom laws.

Original holes left unchanged (three), all owned by
lem-pod-constructible-mate-coherence:

- WeilConjectures.PodConstructibleMate.rational_comparisons_coherent.
- WeilConjectures.PodConstructibleMate.common_comparisons_coherent.
- WeilConjectures.PodConstructibleMate.frobenius_exchanges_isIso.

One hole added:

- WeilConjectures.normalizedCommonEvaluation_naturality, owned by
  lem-pod-normalized-common-evaluation-naturality.

The checked adjunction proof has exactly the permitted axioms propext,
Classical.choice, and Quot.sound, as confirmed by #print axioms. Evaluation
assertions retain sorryAx through their coefficient-specific dependencies.

The delivery has four explicit sorry bodies, closing three original bodies and
adding one. This includes a decomposition, not a claim that all three closed
bodies are axiom-free proofs. The coefficient-specific laws used by the evaluation
proofs are existing dependencies whose proofs remain separate work.

## No longer needed

Removed the private import Sheaf.Paper.FrobeniusCompactSupportExchange: none of
the completed proofs uses it. Its mathematical assertion remains in the DAG route
for the three untouched geometric assertions; no module or node is withdrawn.

The abstract adjunction clause does not need any geometric Frobenius exchange,
coefficient descent, or the unfinished pod_covariant_field_operation_lift theorem:
its input already contains an invertible left comparison, and the lift specification
follows directly from IsoAlgebra.mapOfNatIso.

The two evaluation clauses do not need projection-formula coherence or the
argument-first evaluation theorem. They use the actual Hom-first evaluation and
its two-variable naturality. Projection coherence remains needed by the untouched
comparison packages; it is not pruned globally.

## Where the brief, the DAG or earlier work was wrong

PodPartialClosed records parameter naturality for its transpose but does not state
naturality in both entries of its internal-Hom functor. Therefore naturality of the
actual Hom-first evaluation is a genuine additional input, rather than an instance
field that simp can extract. The rational input already has a stated module;
there was no matching common-stage statement for arbitrary schemes.

Nearby common-stage transpose/descent statements impose separated finite-type
bases. The evaluation theorem here quantifies over Models without separatedness,
so importing those statements would not justify its full domain. The new lemma
states exactly the needed coefficient identity without adding those hypotheses.

The planned semilinear-cube Laws interface also requires separatedness of square
arrows in its direct-exchange and direct-composition clauses, whereas
RationalCoherence and CommonCoherence quantify these clauses without those
instances. Merely applying the stated cube theorem does not close those clauses.
They remain unchanged holes, rather than silently narrowing their domains.

The normalized rational naturality lemma is used as a black box for a coefficient
identity on arbitrary schemes. Its existing node belongs to sk-thm-sf-package;
this packet records the dependency but does not alter maintainer-owned tool_uses
approvals. The independent reader can assess that generic use.

The latest blueprint location is used for the new node. No target, source-library
signature, existing public import, or public definition has changed.

## New nodes

lem-pod-normalized-common-evaluation-naturality, implemented by the single public
theorem WeilConjectures.normalizedCommonEvaluation_naturality in
Sheaf.Paper.NormalizedCommonEvaluationNaturality. It states ordinary two-variable
evaluation naturality, without Frobenius, Weil structures, tensor/Hom comparison
isomorphisms, or the conclusion of EvaluationEquivariant. It is strictly one step
of the common evaluation argument. The parent node records the explicit
naturality-and-cancellation assembly and its dependencies.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
