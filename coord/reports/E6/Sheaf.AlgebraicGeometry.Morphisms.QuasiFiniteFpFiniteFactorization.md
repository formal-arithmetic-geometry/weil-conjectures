## What changed

Proved `AlgebraicGeometry.Scheme.Hom.exists_qcqs_finitePresentation_factorization`
in `Sheaf.AlgebraicGeometry.Morphisms.QuasiFiniteFpFiniteFactorization`, preserving its
entire signature. The proof converts the isolated scheme-fibre points in `hq` into
Mathlib's `LocallyQuasiFinite f` using the canonical fibre homeomorphism. It then applies
`Scheme.Hom.exists_isOpenImmersion_isFinite_locallyOfFinitePresentation` from the existing
source library, and derives the explicit quasi-compactness and quasi-separatedness
clauses from finiteness and the qcqs base. The node's proof and proof dependencies now
record this shorter route. No definition, public import, instance, or consumer changed.

The existing factorization theorem was checked in full, as was Stacks Tag 0F2N in
`literature/stacks-project/more-morphisms.tex`. The route stays below the unit level;
none of `sk-thm-properbasechange.realized` is bypassed. Empty source or base causes no
exception: the conversion is pointwise and vacuous for empty fibres, and the existing
factorization theorem has no nonemptiness hypothesis.

Searches: LeanFinder returned only finite/quasi-finite property declarations, Loogle
returned zero hits, and the Mathlib regex search returned unrelated algebraic finite
presentation factorizations. Reading and searching the project library found the exact
finite-presentation refinement already listed in this node's `lean_candidates`.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Hom.exists_qcqs_finitePresentation_factorization`
(node `lem-weil-pbc-quasifinite-fp-finite-factorization`).

No `sorry` remains in the item. Added 0 holes and split off 0 statements.
The final file compiles cleanly through `lcompile.py` (4.3 seconds).
The delivery preflight also checks the declaration's transitive axioms.

## No longer needed

Removed these proof-only imports:

- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `Sheaf.AlgebraicGeometry.ClosedLimitLfpStabilization`
- `Sheaf.AlgebraicGeometry.FiniteClosedFpApproximation`

The full finite-presentation theorem already exists in
`WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization`, so this item no
longer needs to construct an approximation, descend an open, restrict the inverse system,
or prove stabilization. Its previous proof-dependency nodes no longer used directly are:

- `def-weil-finite-type-morphism`
- `thm-pqf-zmt-factorization`
- `lem-weil-pbc-finite-closed-fp-approximation`
- `lem-weil-pbc-closed-immersion-integral-separated-uc`
- `pqf-lem-limit-qc-open-descends`
- `def-weil-closed-immersion`
- `lem-weil-pbc-closed-limit-lfp-stabilization`
- `def-weil-open-immersion`

The existing source theorem internally uses the ordinary finite factorization, so
`thm-pqf-zmt-factorization` is not claimed globally obsolete; it is no longer an extra
direct proof dependency of this item. Removed the obsolete top-level `tool_uses` entries
`thm-pqf-zmt-factorization` and `lem-weil-pbc-limit-affine-transition`: this proof reuses the
existing source theorem and uses neither tool as a separate DAG obligation.
Other consumers may still need the pruned modules and nodes.

## Where the brief, the DAG or earlier work was wrong

The six-step DAG proof is valid but duplicates an already implemented source-library
finite-presentation refinement. Its own `lean_candidates` had identified that theorem;
the missing explicit qcqs properties require only Mathlib permanence. No statement was
false or changed, no new node was needed, and there were no tool failures.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
