## What changed

Proved `GradedAlgebra.veroneseGrade_isInternal` in
`Sheaf.RingTheory.VeroneseGradedRing`, preserving all signatures, definitions,
instances, and imports. The proof follows the existing docstring (Stacks Project,
algebra.tex, immediately before lemma-uple-generated-degree-1, Tag 0EGH).

Independence of the original grading passes to the subfamily indexed by `n*d`
using `iSupIndep.comp` and positivity of `d`. Pulling those additive subgroups back
along the injective subring inclusion preserves independence, giving injectivity
of recomposition via `iSupIndep.dfinsuppSumAddHom_injective`. Surjectivity follows
by `Subring.closure_induction`: each generator is a direct-sum singleton, and
`DirectSum.coeRingHom` preserves zero, one, addition, negation and multiplication.
The argument includes the zero ring, zero positive-degree components and `d=1`.

Searches through leanfinder, loogle, the Mathlib direct-sum sources and the two
project roots found the generic independence and recomposition lemmas used here;
no additional project lemma or theory was needed.

## Proved and sorry left

Closed 1 of 1 holes: `GradedAlgebra.veroneseGrade_isInternal`
(node `def-sfb-veronese-graded-ring`). Added 0 holes; split off 0 statements.
There are no remaining `sorry` proofs in the module. The existing
`GradedAlgebra.veroneseGradedRing` now obtains its decomposition from a proved
internality theorem.

## No longer needed

None. No imports were removed. The node has no declared proof dependencies,
and the original proof route needs no additional Sheaf or WeilConjectures modules.

## Where the brief, the DAG or earlier work was wrong

None. The Lean proof implements the decomposition argument already in the
existing theorem's docstring. No statement, definition, dependency route or unit
route changed; no node or change record is required for this proof-only delivery.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
