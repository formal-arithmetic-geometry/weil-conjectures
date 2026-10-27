## What changed

Proved `WeilConjectures.IntegralSystemRealization.IndependentExpression.shift_naturality_generic`
in `Sheaf.SixFunctors.IndependentExpressionShiftNaturality` using the existing
structural proof plan. Added private, fully proved helpers. The existing imports provide all
the functor and natural-isomorphism API needed by the proof.

The proof constructs a natural isomorphism by following the unique selected leaf.
An absent label leaves the entire evaluation functor unchanged, including maps.
Unary vertices whisker the inductive isomorphism and compose with the primitive
shift comparison. Tensor vertices pair it with equality transport on the other
subtree, then use the specified left or right tensor comparison. A simultaneous
induction identifies each component with the existing single-slot comparison.
The final proof removes its endpoint equality transports by heterogeneous equality
and applies naturality of the constructed isomorphism.

All existing public signatures, definitions, and public imports are preserved.
No source-library module is changed. The unit route and existing DAG proof
and dependencies are retained.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.IntegralSystemRealization.IndependentExpression.shift_naturality_generic`
(node `lem-pur-independent-expression-shift-naturality`).

No holes remain in the item; no holes are added or split off elsewhere.
All private helpers are proved completely.

Validation: `lcompile.py` completed cleanly in 8.1 seconds, exit code 0.
The delivery tool also runs its compile, axiom, and preflight checks before pushing.

## No longer needed

None. Both existing public imports are required by the unchanged declarations.
The proof uses the occurrence constructions and both designated tensor-slot
comparisons. No DAG dependency, module, or unit step is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect was found. The existing proof plan suffices;
constructing the natural isomorphism first makes naturality in the nonselected
tensor operand automatic and keeps equality transport out of the recursive square.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
