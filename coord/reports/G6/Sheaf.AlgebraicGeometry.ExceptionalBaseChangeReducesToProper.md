## What changed

Proved `AlgebraicGeometry.Scheme.exceptionalBaseChangeReducesToProper` with its existing
signature and canonical comparison map unchanged. The proof composes the two open
adjunctions with the supplied proper adjunctions, applies Mathlib `mateEquiv_hcomp`,
and transfers invertibility to the ambient adjunctions. A proved private helper performs
the transfer by the two change-of-adjunction mate identities and invertible conjugates
of identity transformations. Componentwise normalization identifies the pasted square
with the exact square in the conclusion. The node's proof and proof dependencies now
record this implementation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exceptionalBaseChangeReducesToProper`
(node `cor-exc-base-change-reduces-to-proper`). Added zero holes. No `sorry` remains
in the delivered module. The private helper `isIso_mate_of_same_left_adjoints` is proved.

## No longer needed

Removed proof-only imports:

- `Mathlib.CategoryTheory.Adjunction.Unique`: the canonical right-adjoint comparisons
  are obtained as invertible conjugates of identities using the already imported
  Mathlib mates API.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.
- `Sheaf.Paper.DerivedPullbackTensorHom`.

The proof does not need nodes `lem-weil-pbc-proetale-derived-pullback-composition`
or `def-weil-derived-pullback-tensor-hom`; they are removed from `proof_deps`.
The specified finite-level comparison `sfIntrinsicDerivedSquarePullback` is already
constructed in `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`, publicly imported
by `IntrinsicDerivedOpenAdjunction`. Thus neither the separate derived composition API,
the integral tower composition theorem, nor tensor/internal-Hom constructions are used.
The obsolete top-level tool approval for the separate composition node is withdrawn.
No unit statement or unit proof step is bypassed; the open/proper factorization and
canonical mate-pasting route are retained. No claim is made that these modules are
unneeded by other library modules.

## Where the brief, the DAG or earlier work was wrong

The DAG's composition-node attachment now names an integral tower theorem, although
this item uses only its already constructed finite-level square isomorphism. The two
corresponding proof imports therefore introduced unrelated work. No statement or
definition repair was necessary. All original public signatures and public imports
are unchanged.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
