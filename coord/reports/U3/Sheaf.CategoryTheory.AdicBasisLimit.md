## What changed

Proved both theorem holes in `Sheaf.CategoryTheory.AdicBasisLimit` without changing
any theorem statement. The ideal bounds follow from the equality of extended
principal-power ideals. Quotient bases come from base change and the tensor-product
quotient equivalence. The completed scalar map is the map of tower limits.

Added the fully proved `Sheaf.CategoryTheory.ConstantSpecifiedBasis`, exposing the
specified-column version of the constant-sheaf finite-basis argument. The existing
`ConstantFiniteFreeSectionBasis` theorem chooses section bases and uses
`CommRingCat`; it does not identify the columns for a given basis in these
`RingCat` constant sheaves. Its private construction guided the new proof.

The completed module map is the sum of the coordinate projections followed by the
completed constant columns. Its sectionwise injectivity and surjectivity follow
from the quotient basis maps and the sectionwise limit universal property. This
includes rank zero, zero rings and empty covering sieves.

Made the existing residue wrapper an abbreviation and expressed the quotient
tower directly using `Ideal.Quotient.factorPow`, preserving all objects and
transition maps. The recursive successor construction made the arbitrary
transition-map lemma take about 29 seconds of kernel checking in isolation.
Change records are `coord/changes/adicBasisResidue-U3.md` and
`coord/changes/adicBasisTower-U3.md`. There are no downstream Lean importers and
no forced adaptations.

## Proved and sorry left

Closed 2 of the item's 2 holes:

- `CategoryTheory.adicBasis_ideal_bounds`.
- `CategoryTheory.adic_basis_limit`.

Added 0 holes. No `sorry` remains in either delivered Lean module. The new
`CategoryTheory.constantSheaf_specifiedBasis` theorem and all private helpers
are proved. This is a proof, not a decomposition into postponed statements.

## No longer needed

Removed from the item module:

- `Mathlib.CategoryTheory.Sites.LeftExact` (previous public import). The new
  constant-basis module imports it privately for its own proof.
- `Mathlib.CategoryTheory.Sites.PreservesSheafification` (previous proof import).
  The comparison uses local bijectivity of sheafification units directly.

Changed `Mathlib.CategoryTheory.Functor.OfSequence` to a private proof import;
the repaired public tower definition no longer uses it.

No original mathematical dependency is pruned: all six original dependencies
remain used, directly or through `lem-pur-constant-specified-basis`. No existing
module is withdrawn. The separate cofinal-limit isomorphism suggested by step 4
is unnecessary as an auxiliary construction: cofinal projections and compatible
coordinate cones give the inverse directly.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. Both original theorem signatures are unchanged.
The prescribed-column sheafification step needed an exposed theorem beyond the
existing existential section-basis API. The original recursive tower construction
was mathematically correct but expensive for arbitrary-index transition proofs;
the direct reduction functor has the same meaning and a cheaper interface.
The complete main module compiled cleanly in 39.8 seconds after this change;
the prescribed per-file limit is unchanged. The separate specified-basis module
also compiled cleanly (18.2 seconds).

## New nodes

`lem-pur-constant-specified-basis` records the fully proved specified-basis
constant-ring-sheaf theorem, corresponding precisely to step 2 of the item's
original proof plan. Its proof uses module sheafification, finite-product
preservation, and local bijectivity of the ring-sheafification unit. The parent
node's proof and proof dependencies now describe this theorem and the explicit
sectionwise limit argument. The unit route is retained.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
