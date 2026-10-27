## What changed

Proved `AlgebraicGeometry.ProEtale.exists_connected_finiteEtale_irreducibility_detector`
without changing its statement. Added only private proved helpers and private proof imports
to `Sheaf.DeligneLaumon.ProEtaleIrreducibilityDetector`. Updated its DAG proof to match.

The proof uses the source library's proved universal pro-etale monodromy directly.
Burnside's theorem supplies finitely many matrices with nonzero determinant. Continuity
keeps this determinant nonzero after perturbation by a sufficiently small open normal
subgroup. A common quotient for the finite family gives a connected finite etale cover.
Connected pullback to a curve forces surjectivity onto that quotient; path transport and
monodromy compatibility then give irreducibility of each pullback.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.exists_connected_finiteEtale_irreducibility_detector`
(node `lem-zl-proetale-irreducibility-detector`). Added zero holes; none remain in the item.
All four private helper theorems are proved. This is a proof, not a decomposition.
The complete module compiled cleanly through `lcompile.py` on the project server
in 10.2 seconds, with no warnings. The public statement was compared verbatim
against the repository version and is unchanged.
The construction also handles the empty family: the intersection is the full group,
its quotient is trivial, and the cover has degree one.

## No longer needed

The following declared proof dependencies are removed from this item's DAG proof:

- `thm-lisse-qlbar-representations` / `Sheaf.Paper.LisseQlbarRepresentations`:
  the native proved universal pro-etale monodromy suffices; finite fields of definition
  are unnecessary for the determinant argument.
- `lem-zl-common-irreducibility-detecting-cover` /
  `Sheaf.RepresentationTheory.CommonIrreducibilityDetectingCover`:
  its etale adic coefficient interface does not need to be compared with pro-etale sheaves.
- `lem-pod-profinite-stable-lattice` /
  `Sheaf.RepresentationTheory.ProfiniteStableLattice`:
  openness of the nonzero determinant replaces integral congruence lattices.

- `cor-galois-lisse-representations` / `Sheaf.Paper.GaloisLisseRepresentations`:
  the proved native `universalLisseMonodromy_isEquivalenceAt` supplies the needed
  pro-etale correspondence directly.
- `lem-galois-transitive` / `Sheaf.CategoryTheory.Galois.GaloisTransitive`:
  the native Mathlib `IsFundamentalGroup` action already has transitivity.
- `thm-galois-fundamental` / `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`:
  no FLC comparison is used; the proved source-library functoriality suffices.

The existing node `lem-galois-pi1-functoriality` is now an explicit dependency of
the last step, matching the actual `fundamentalGroupMap_smul` API.

These dependencies were not imported by the starting item, so no pre-existing import
line was removed and no library module was withdrawn. All original public imports stay.
A source-import traversal confirms that none of the six modules is imported transitively
by the new proof either.
`lem-zl-finite-matrix-irreducibility` remains as the source of the proved Burnside and
matrix-determinant support API used here; its integral-congruence conclusion is not used.

## Where the brief, the DAG or earlier work was wrong

The previous plan correctly noted that its common-cover declaration uses a different
sheaf interface. That comparison is avoidable: the source tree already proves native
pro-etale monodromy and compatibility for arbitrary morphisms of connected regular
Noetherian schemes. Continuity of matrix coefficients also avoids the coefficient-field
and stable-lattice part of the original proof. The unit's curve-testing route is preserved.
No statement or definition was repaired, and no other module was changed.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
