## What changed

Proved `WeilConjectures.FixProjectionCompactification.finiteProjectionFromDescent`
with its signature and existing public imports preserved. Proved private categorical
helpers cancel identity presentations and common-source witness transports, and
combine the two assumed refinement squares by cancellation of comparison
isomorphisms. The main proof packages the supplied constructibility hypotheses,
instantiates the refinement law twice with the retained origin presentations, and
cancels the common witness transports. A proved private equality exposes theta in
the finite comparison coordinates. The scalar assembly lemma uses the native
functors in its statement to avoid expensive kernel conversion after coefficient
specialization. A private memoized congruence helper converts the generic coefficient
presentation to the native presentation one argument at a time; it produces ordinary
kernel-checked equality and heterogeneous-equality proofs, with proof irrelevance
for proposition-valued instance arguments. No projection morphism is inverted.

Local irreducibility attributes keep the large derived-functor and witnessed
comparison definitions folded during the generic transport rewrites. These
attributes affect only this proof module. Transparency checking stays enabled.
The complete proof compiled in 15.2 seconds during profiling (main kernel check
0.741 seconds); profiling and the reduced diagnostic heartbeat limit were removed
before delivery. The delivery script performs the final compile and preflight.

Updated the item's node proof to describe the actual argument and its definition
dependencies. All edits are confined to the item module, its node, and this report.

## Proved and sorry left

Closed one hole:
`WeilConjectures.FixProjectionCompactification.finiteProjectionFromDescent`
(node `lem-sf-finite-projection-compactification-square-specialization`).
Added zero holes. No `sorry` remains in the item or any new declaration.
This is a proof, not a decomposition: every private categorical
assembly helper has a complete Lean proof.

## No longer needed

The proof does not invoke `ProjectionRefinementDescent.finite_descent`
(node `lem-sf-projection-refinement-descent`): the refinement-law clause is already
an explicit hypothesis. The item node's proof dependencies now name the actual
fixed-scalar domain, compactification-law, and witnessed-comparison definitions
instead. The existing
public imports remain to preserve the interface; no module is withdrawn or claimed
to leave the targets' import closure. Added the proof-only import
`Mathlib.Lean.Meta.CongrTheorems`; no public import was changed or removed.

Searches through the required msearch wrapper found Mathlib's commutative-square
inverse lemmas and functor laws; local search found a private common-refinement
cancellation proof in ProjectionRefinementDescent. A private proved version supplies
the elementary cancellation here without any new public API or new node.

## Where the brief, the DAG or earlier work was wrong

The original node cited the whole finite-descent theorem even though this assembly
uses only its assumed refinement-law clause and the existing definitions. Its proof
plan otherwise applies unchanged. In particular the arbitrary tensor presentation
e is retained, the common refinement is supplied by the goal, and no finite Tor
condition is imposed on K. The unit record has no realized proof steps to bypass.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
