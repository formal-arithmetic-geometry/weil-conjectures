## What changed

Proved `SheafOfModules.isFlat_over_preservesFiniteLimits` in the assigned module, with its
signature unchanged. The proof follows Stacks, Modules on Sites, Tag 0E8J
(`lemma-restriction-flat`): extend an exact short complex, tensor using the flatness
hypothesis, transport through the natural projection formula, and reflect exactness.
Mathlib converts preservation of exact short complexes by this additive tensor functor
into preservation of homology and then of finite limits.

The natural functor comparison is built explicitly from the existing projection formula
and `tensorObjIsoSheafification`. Its naturality uses the projection formula at `(f, id F)`
and the two existing tensor/sheafification naturality lemmas. The direct-sum extension's
preservation of zero maps is proved on its generators. No helper declaration, definition,
consumer adaptation, or public import is added or changed. Added proof-only imports of
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree` (additivity and tensor
naturality) and `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor` (exact-functor criteria).

Updated the existing node's proof to describe the exact-complex argument implemented in
Lean. Its three existing proof dependencies are all used. The unit route is unchanged.

Searches ran through msearch.py: LeanFinder for tensoring with restriction of a flat sheaf
preserving finite limits (ordinary module-flatness and site-pullback results, no exact
slice theorem); Loogle for the finite-limit exact-complex criterion (identifier not in
that index); grep located the criterion in Mathlib's ShortComplex/ExactFunctor. Direct
source searches located the existing additivity and tensor naturality lemmas.

## Proved and sorry left

Closed the one original hole: `SheafOfModules.isFlat_over_preservesFiniteLimits`
(node `lem-weil-pbc-slice-restriction-flat-finite-limits`). No holes remain in the item.
Holes added: zero. Split-offs: zero. This proves the item from the already declared
projection formula and extension exactness dependencies; their transitive outstanding
proofs are unchanged.

## No longer needed

Removed the unused proof-only import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: the hypothesis uses the specialized
`IsFlat`, whose defining exactness predicate already supplies what the proof needs.
No declared proof dependency is pruned: extension exactness, the tensor projection formula,
and flatness all occur in the proof. No other module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier plan described extension and reflection of arbitrary finite-limit cones,
whereas the declared extension interface states equivalence of exactness of short
complexes. The source's own exact-complex proof fits that interface directly. Mathlib's
abelian exact-functor criteria supply the finite-limit conclusion, so no new cone-level
reflection theorem is needed. The theorem statement and all mathematical hypotheses
remain unchanged.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
