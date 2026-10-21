## What changed

Proved `CategoryTheory.tensorAction_trace_contraction` in
`Sheaf.CategoryTheory.TensorActionTraceContraction`, preserving its entire signature and
`CategoryTheory.tensorTraceContraction` unchanged. The proof follows the node's five steps:
form the structural isomorphism sigma, invert the assumed tensor-action equation as an
isomorphism equality, contract using associator naturality and left-unitor tensor coherence,
invert the supplied naturality square for PFg, and assemble by functoriality and tensor
bifunctoriality. All five domain memberships are used at precisely the displayed components.
No adjunction, braiding, composition comparison, or tensor-action law for g is introduced.

Validation: `lcompile.py` compiled the finished module cleanly on the server in 2.8 seconds,
with no errors or warnings. The original theorem signature and the contraction definition
were compared verbatim and are unchanged. Every delivered Lean line has at most 100 characters.

## Proved and sorry left

Closed the sole original hole, `CategoryTheory.tensorAction_trace_contraction`
(blueprint: `lem-pur-tensor-action-trace-contraction`). Holes closed: 1. Holes added: 0.
No sorry remains in the delivered module; no statements are split off.

## No longer needed

Removed the private import `Mathlib.CategoryTheory.Monoidal.Free.Coherence`.
The structural-coherence step uses the standard left-unitor tensor identity
`CategoryTheory.MonoidalCategory.leftUnitor_tensor_hom`, already available through the
existing public import `Mathlib.CategoryTheory.Monoidal.Functor`.
No project node or module is withdrawn. All three declared proof dependencies still describe
the argument: the ambient monoidal category, the specified tensorator, and structural
coherence (used through its dedicated left-unitor specialization).

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The given five-step argument works with the
original domain restrictions and arbitrary trace maps. The general free-monoidal coherence
import was stronger than needed: its specific unit-tensor identity is already in Mathlib's
monoidal-category API. The unit route is unchanged. No new nodes or change records.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
