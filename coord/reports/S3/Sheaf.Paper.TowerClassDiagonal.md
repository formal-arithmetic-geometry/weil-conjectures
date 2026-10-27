## What changed

Replaced `lineEvaluation_existsUnique` by a comparison of the two scalar-extension
universal properties. The proof constructs the forward and reverse maps, proves
both inverse identities by naturality and injectivity, checks the prescribed pure
root tensors, and proves uniqueness by transporting roots through `rootForget`
and `Forget.sections`. Existing signatures and definitions are preserved.

Added proof imports `Sheaf.Paper.TowerLineEvaluationUniversal` and
`Sheaf.Paper.FiniteTateLineUniversal`. Each new module states one constituent
universal property, with its source and complete proof in words. Updated the
owning node's proof route. The unit's classes (2) coefficient-extension route is
preserved.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.ProEtale.SpTowerClasses.lineEvaluation_existsUnique` by
reduction to two constituent universal properties. This is a decomposition,
not a net decrease in holes. The item's module has zero remaining holes.

Added holes:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.towerLineEvaluation_universal`
  (`lem-sp-tower-line-evaluation-universal`).
- `AlgebraicGeometry.ProEtale.SpTowerClasses.finiteTateLine_universal`
  (`lem-sp-finite-tate-line-universal`).

The existing proof of `diagonalLine_invertible` is preserved.

## No longer needed

None. No existing import, node, module, declaration, or unit step is withdrawn.
The original owning node had no proof dependencies to prune.

## Where the brief, the DAG or earlier work was wrong

The owning definition node had an empty proof list, although its Lean module
included the finite comparison existence-and-uniqueness theorem. Its Lean
docstring supplied the tensor comparison argument; this delivery records the
two scalar-extension universal properties and their assembly explicitly.
The current three-module packet compiles; the item module compiled in 53.8 seconds.
No statement is disputed or weakened. Edge cases for the new statements include
level zero (exponent one), zero coefficient ring, empty scheme, and absence of
nonzero root sections; the Hom universal properties require no invertibility
of the prime on the scheme.

## New nodes

`lem-sp-tower-line-evaluation-universal`: maps from the evaluated scalar-extended
root module correspond to additive root-sheaf maps into arbitrary coefficient
modules. The statement includes postcomposition naturality and the generator
formula. It isolates the sequence-site evaluation/sheafification argument.

`lem-sp-finite-tate-line-universal`: maps from the finite Tate scalar extension
correspond to additive root-sheaf maps. Its generator formula is the finite
tensor adjunction. Neither lemma asserts an isomorphism between the two line
objects or their uniquely normalized comparison; the item constructs and
characterizes that comparison using both.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
