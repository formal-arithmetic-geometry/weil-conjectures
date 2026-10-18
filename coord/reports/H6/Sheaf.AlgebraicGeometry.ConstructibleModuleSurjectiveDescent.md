## What changed

Replaced the single `sorry` in
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_of_surjective_pullback`
with the reverse implication of
`isConstructibleEtaleModuleSheaf_iff_surjective_pullback a G`, applied to `hG`.
The theorem's signature, visibility, documentation and imports are unchanged.
The proof follows the sole step of
`lem-weil-pbc-constructible-module-surjective-descent` exactly, so no node update
is needed. The unit route is preserved.

Read Stacks `etale-cohomology.tex`, `lemma-check-constructible` (Tag 095Q), part (3),
and checked the dependency's signature: both schemes are qcqs, the morphism is
surjective, the coefficient ring is finite and commutative, and the predicate
and inverse-image functor are identical. Lean infers these exact parameters.
LeanFinder, Loogle and grep searches found no shorter Mathlib specialization;
the already declared equivalence is the shortest route.

The assigned file compiled cleanly through `lcompile.py` in 2.9 seconds.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_of_surjective_pullback`
(node `lem-weil-pbc-constructible-module-surjective-descent`).

Added 0 holes. No `sorry` remains in the delivered module. The proof uses the
existing, still unproved dependency
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_iff_surjective_pullback`
(node `lem-weil-pbc-etale-constructible-surjective-pullback`); that existing
obligation is unchanged and is not a new split-off.

## No longer needed

None. All three public imports supply names in the unchanged statement, and
`Sheaf.AlgebraicGeometry.ConstructibleSurjectivePullback` supplies the proof.
No imports, nodes or modules are pruned. The existing proof dependencies remain
exactly those used by the proof.

## Where the brief, the DAG or earlier work was wrong

None. The existing equivalence matches every hypothesis and the conclusion,
so the planned one-step specialization works directly.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
