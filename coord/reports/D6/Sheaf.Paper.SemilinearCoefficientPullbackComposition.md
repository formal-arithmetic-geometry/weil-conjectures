## What changed

Filled `WeilConjectures.SemilinearSections.Geometry.coefficientPullback_composition`
in `Sheaf.Paper.SemilinearCoefficientPullbackComposition` without changing its
signature or public imports. Added one private proof import,
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`, for the
exact-localization comparison API.

The proof first establishes ordinary restriction-square composition using the
faithful underlying-sheaf functor and the section identity characterization of
restriction composition. It transports this equation to derived categories via
the factorization isomorphisms on complexes and localization natural-transformation
extensionality. A private categorical calculation then applies the two scalar
hom-equivalences, substitutes the supplied transpose normalizations, uses
naturality, and cancels the invertible comparisons.

Only the assigned module and its own DAG node are changed. The proof uses the
actual supplied adjunctions and all indices, including equality indices. It
requires no flatness hypothesis and no geometric direct-image comparison.

Validation: `lcompile.py` compiled the full delivered module cleanly in 31.2 s.
The exact theorem signature, public imports, node attachment, zero textual holes,
and 100-character Lean line limit were also checked.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.SemilinearSections.Geometry.coefficientPullback_composition`
(node `lem-sp-semilinear-coefficient-pullback-composition`).

Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
All private helpers are proved. No split-off statements or new axioms are added.

## No longer needed

No existing imports are removed and no library module is withdrawn.
The standalone DAG dependency `lem-weil-pbc-mate-pasting` is no longer required:
the proof gives its particular hom-equivalence calculation directly in the proved
private helper `mate_composition`. Its edge is removed from the item's proof plan.
The three semilinear definition dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The stated plan can be completed from the
existing normalization fields, so another decomposition is unnecessary. The
three searches ran through `msearch.py`: LeanFinder returned the general
`mateEquiv_hcomp`/`mateEquiv_vcomp` lemmas, Loogle did not resolve the unqualified
`conjugateEquiv` identifier, and grep returned general mate and scalar-composition
APIs. There was no existing theorem of the exact normalized coefficient equation.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
