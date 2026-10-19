## What changed

In `Sheaf.Paper.DiagonalTowerSystem`, replaced five of the six original theorem
holes by compiling Lean proofs, with every existing signature unchanged.

* `diagonalForget_exact`: use the scalar adjunction for limits and the
  restriction/coextension adjunction, followed by sheafification, for colimits.
* `diagonalForget_additive`: composition and sheaf postcomposition are additive.
* `diagonalFiniteToPadic_exact`: use extension/restriction for limits,
  restriction/coextension and sheafification for colimits, and sectionwise additivity.
* `diagonalImmersion_cartier`: the kernel subscheme of the diagonal projects
  isomorphically to the first projective line. The first projection of the surface
  is smooth of relative dimension one. The existing, proved relative Cartier
  criterion therefore applies over every base, without Noetherian hypotheses.
* `diagonalSurface_power_unit`: map the given unit along global sections of the
  surface-to-base morphism, then take its positive power.

Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier` and
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth`.
Updated step 1 and the proof dependencies of
`det-prop-diagonal-tower-system` for this shorter geometric argument.
The Cartier criterion is an already closed generic tool, not a replacement of
any step of the diagonal-tower unit.

On resumption on 2026-10-19, compared the retained Lean and node changes against
the current shared sources. The required delivery dry run passes compilation and preflight (checked again at
06:47). Both added imports pass the cycle check. A fresh axiom probe containing
the actual sandbox source compiles in 39.3 seconds against the current published
build. There are no overlong Lean lines and exactly one remaining local hole. The node changes only proof, proof_deps and proof_origin, and its proof
dependencies equal the union of the proof-step uses.
Edge cases retain the empty base and
arbitrary non-Noetherian bases; all scalar maps and positive exponents are unchanged.

## Proved and sorry left

Original holes: 6. Holes closed: 5. Holes added: 0. Split off: 0.

Closed, in namespace `AlgebraicGeometry.ProEtale`:

* `diagonalForget_exact`
* `diagonalForget_additive`
* `diagonalFiniteToPadic_exact`
* `diagonalImmersion_cartier`
* `diagonalSurface_power_unit`

The only remaining sorry is
`AlgebraicGeometry.ProEtale.exists_diagonalTowerSystem`, on node
`det-prop-diagonal-tower-system`. Its original complete natural-language proof
and exact statement remain. The outstanding work is the simultaneous derived
reduction functor, its completion comparison and the source/roots identifications
with the signed finite Cartier class. No corresponding theorem has been renamed,
weakened or moved to a new hole.

A fresh axiom inspection containing the sandbox proofs verifies that
`diagonalForget_additive`, `diagonalImmersion_cartier` and
`diagonalSurface_power_unit` use only `propext`, `Classical.choice` and `Quot.sound`.
The two exactness proofs still transitively reach pre-existing sorry dependencies
in coefficient infrastructure; closing their local holes does not claim that all
their dependencies have been proved. The older import-only inspection loaded the
published module, so it was replaced by this direct probe of the sandbox source.

## No longer needed

No modules or DAG nodes are pruned. No imports are removed: the original proof
dependency imports remain the declared plan for the one unresolved main theorem.
For the proved Cartier helper, the four-chart polynomial calculation is no longer
needed; the already proved relative Cartier criterion supplies it abstractly.
The stalk, Kummer, K-flat, open/closed and completion dependencies of the remaining
main theorem have not been claimed unnecessary.

## Where the brief, the DAG or earlier work was wrong

No statement was disputed or changed. The geometric regularity step has a shorter
route already in the source library: the relative Cartier criterion applies to the
diagonal as a section of a smooth relative curve over the first projective line.

The derived-change-of-rings and completion interfaces use internal ringed-site
modules. Applying them here requires their comparisons with fixed-scalar sheaves
and with the strict-system category. The main proof and its finite class
normalizations remain unfinished; the presence of sorry in dependencies is not
being treated as a blocker.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
