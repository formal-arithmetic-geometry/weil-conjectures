## Worker report

The module `Sheaf.SixFunctors.ConstructibleOpenClosedRefinement` states
`AlgebraicGeometry.Scheme.exists_finite_open_closed_refinement` with proof
`sorry`.  It is the existing project declaration for this node, copied
verbatim for this delivery and re-recorded with the current worker and date.
The declaration uses the common scheme universe `u` and binds
`W : Scheme.{u}` with `[CompactSpace W] [QuasiSeparatedSpace W]`.  It binds
`m : ℕ`, `n : Fin m → ℕ`, finite families
`S a j : Scheme.{u}`, and maps `s a j : S a j ⟶ W`.  The hypotheses are exactly
`IsImmersion (s a j)`, constructibility of each `Set.range (s a j).base`,
coverage of `W` by each partition, and pairwise disjointness inside each
partition.

The conclusion introduces `O`, `Q`, and `Z`, maps `o`, `c`, `q`, and `z`, and
states, clause by clause: `o` and `q` are open immersions; `c` and `z` are
closed immersions; `c ≫ o = s`; `o` and `q` are quasi-compact; the range of
`q ≫ o` is the set difference between the ranges of `o` and `s`; and the range
of `z` is the complement of the range of `o`.  It then gives a finite vertex
type `Fin N`, a root, parent and left/right maps, edge maps, and a leaf
predicate.  The tree clauses render root identification with `W`, strict
parent descent away from the root, commuting edge maps, compact and
quasi-separated vertices, immersion into `W`, binary parent/child incidence,
and the leaf characterization.  Every internal node has distinct, ordered
children with open/closed, quasi-compact edges whose ranges are complementary.
The disjunction gives the two allowed scheme-theoretic pullback split forms,
including the `eqToHom` casts.  Finally, nonempty leaf images cover `W`, are
pairwise disjoint, and every nonempty leaf factors through a stratum of every
partition with the required composite equality.

The recorded dependency declarations used are:

* `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` from
  `Mathlib.AlgebraicGeometry.Scheme` (the scheme structure and morphisms);
* `AlgebraicGeometry.QuasiSeparated` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (a morphism is
  quasi-separated through its quasi-compact diagonal, and
  `QuasiSeparatedSpace` is the terminal-map specialization);
* `AlgebraicGeometry.IsClosedImmersion` from
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (closed embedding with
  surjective stalk maps);
* `AlgebraicGeometry.IsOpenImmersion` from
  `Mathlib.AlgebraicGeometry.OpenImmersion` (the locally-ringed-space open
  immersion predicate);
* `Topology.IsConstructible` from `Mathlib.Topology.Constructible`, together
  with `IsRetrocompact` (constructibility is the Boolean subalgebra generated
  by open retrocompact sets);
* `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, with scheme
  pullbacks supplied by `Mathlib.AlgebraicGeometry.Pullbacks`;
* `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.  The node's
  quasi-compact branch-map condition is rendered directly by `QuasiCompact`.

Edge cases checked against the statement and its proof are `m = 0` (the
factorization condition is vacuous), a partition with `n a = 0`, `W = ∅`, and
empty leaves.  The corrected leaf condition allows the root to be a leaf and
does not require an internal split when there are no strata.  Zero-stratum
partitions and the empty scheme therefore do not force an impossible
existential.  The common universe `u` is used for every scheme and finite
family, so no case is excluded by a smaller independent universe.

Searches made for an existing declaration or duplicate notion:

* `msearch.py ... leanfinder "finite open closed refinement through
  constructible strata with a finite binary tree of scheme-theoretic
  pullbacks"`: eight generic open-cover, affine-transition, or pullback hits;
  none states this refinement.
* `msearch.py ... loogle "IsImmersion, IsOpenImmersion, IsClosedImmersion,
  QuasiCompact, IsConstructible, pullback"`: the service reported zero hits
  because `IsImmersion` is not a valid standalone Loogle identifier.
* `msearch.py ... grep "exists_finite_open_closed_refinement|constructible.*refinement"
  AlgebraicGeometry`: zero hits.
* Direct `rg` over `WeilConjectures/` found only the separate constructible
  sheaf refinement and open/closed derived material; no declaration of this
  scheme-theoretic theorem.  Direct `rg` over `lean/Sheaf` found only the
  copied node module.  `grep -rl` over `dag/nodes` found this item and its
  consumer `lem-fix-constructible-tensor-completion`, with no second node
  carrying the same statement.

The module has no local notation, private declarations, or unbound variables;
all postponed work is the single theorem proof `sorry` described by the
node's nine proof steps.  Compilation is performed with `scompile.py` and the
existing-declaration probe in `deliver2.py`.

## Second reading by Q107

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
