## What changed

Proved the final theorem `integralExceptionalMappingSystem`, preserving all three
earlier proofs and every definition. A proved private helper derives naturality
of globalEvaluation from resolution coherence. The theorem expands the actual
three-factor Psi, applies the two outer naturality equations and the middle
Enriched.finiteEvaluation equation, then cancels comparison isomorphisms. The
H-zero formula follows from coefficientHomZeroEquiv naturality and finiteHom.

The disputed signature now requires resolution coherence of SX and SY, already
provided by the specified realization. The conclusion and all geometric and
integral-input hypotheses are unchanged. The change record is
`coord/changes/Q9-integral-mapping-resolution-coherence.md`. The node records the
actual argument and its Hom-zero dependency. No consumer adaptation is needed.

## Proved and sorry left

The repaired `WeilConjectures.IntegralExceptionalMapping.integralExceptionalMappingSystem`
is proved, with both its derived equality and Hom formula. It replaces the one
original disputed hole; the old theorem for arbitrary unconstrained objectwise
comparisons is not claimed. Zero holes remain in this module. Zero holes added;
zero statements split off. Earlier proofs remain verbatim.

## No longer needed

None. No imports or modules were removed. The declared dependencies and assigned
unit route are retained. Public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

Z8's dispute was correct: globalEvaluation has no naturality in the bare calculus.
The separate resolution-coherence structure fixes it to sections evaluation and
fiberHom, which do supply naturality. The stage-2 review's assertion that omitting
coherence was harmless did not justify the two outer counit squares. The repair
uses only the existing coherence supplied by finiteAdjunctionDiagramRealization.
There are no Lean callers; both DAG parents already use coherent calculi.

The current blueprint lacks the old integral-exceptional-adjoint proof path.
Read its retained DAG argument and the current latest finite-exceptional proof:
its internal-Hom adjunction followed by global sections is exactly the middle
map used here. Zero objects, empty schemes, identity f and n=0 need no additional
cases or hypotheses. Ramified coefficients remain allowed. No inverse limit or
faithfulness of finite evaluations is used to infer an equality of system maps.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
