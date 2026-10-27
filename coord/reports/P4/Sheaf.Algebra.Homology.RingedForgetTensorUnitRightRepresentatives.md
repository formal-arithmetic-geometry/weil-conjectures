## What changed

Filled `CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_right_representatives`
without changing its signature. The proof constructs the unit-complex comparison from
`singleMapHomologicalComplex` and the given underived unit, proves its right-unitor square
on tensor summands, and transports that square through the given representative comparison
and exact-functor localization factor. All added helper theorems are private and proved.
Only the assigned Lean module and its own DAG node change. The extra proof imports provide
the sheaf right-unitor formula, pure-tensor naturality, tensor-colimit instances and the
bounded-above flat criterion. The DAG proof now records the actual chain and localization
calculations. The complete proof compiled in 53.4 seconds with profiling enabled;
profiling options were removed for delivery. An axiom check of the complete proof reports
only `propext`, `Classical.choice` and `Quot.sound`.

## Proved and sorry left

Closed 1 original hole:
`CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_right_representatives`
(node `lem-sf-ringed-forget-tensor-right-representatives`). Added 0 holes and split off 0
statements. No `sorry` remains in the assigned module. This is a proof, not a decomposition.

## No longer needed

None. All original declared dependencies remain in use. No modules or nodes are withdrawn,
and no existing public imports are removed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The previous prose compressed two necessary calculations:
converting the local pure-tensor unitor formula into a morphism equation, and cancelling
the representative comparison while tracking the normalized unit isomorphism. Both are
now explicit Lean proofs. Vanishing unit summands are handled by zero-object preservation;
the proof makes no assumption that global sections generate the sheaves or that U acts
on their sections.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
