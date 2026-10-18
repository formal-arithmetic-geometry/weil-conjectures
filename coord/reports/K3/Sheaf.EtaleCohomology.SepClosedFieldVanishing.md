## What changed

Proved `AlgebraicGeometry.Etale.sepClosedField_etale_decomposition_and_vanishing`
in `Sheaf.EtaleCohomology.SepClosedFieldVanishing`, with its statement, universe,
visibility and public imports unchanged. Added the proved private helper
`surjective_sections_of_epi` for componentwise lifting and gluing.

The decomposition uses Mathlib `Scheme.exists_fac_of_etale_of_isSepClosed` to choose
one rational-point section for each point, `FormallyUnramified.isOpenImmersion_of_comp`
to make those sections open immersions, and `nonempty_isColimit_cofanMk_of` to assemble
the pairwise disjoint singleton images into the requested coproduct. The lifting helper
uses the existing PointCohomology terminal lifting theorem and the existing
CohomologyColimit covering-form sheaf axiom. Its empty-overlap case uses the empty-cover
sheaf axiom explicitly. Exactness of global sections and direct image then follows
from preservation of kernels and epimorphisms. Existing exact-functor comparisons
identify their derived images of a degree-zero sheaf with degree-zero objects;
positive homology therefore vanishes.

Added only proof imports of PointCohomology, CohomologyColimit,
RightDerivedFunctor.MapDerivedCategory and RightDerivedFunctor.PlusExact.
Updated `lem-kun-0ezp` proof, proof dependencies and proof origin to describe this route;
withdrew its obsolete fibre-decomposition tool-use entry. No definitions, statements,
consumers, public signatures or unit realizations changed. The unit's realized statement
and step lists are empty, and the current blueprint's three substantive steps remain:
etale-object decomposition, exact global sections, and higher-direct-image vanishing.

Searches used the launcher leanfinder, loogle and grep services plus repository/Mathlib
ripgrep. Loogle found `Scheme.exists_fac_of_etale_of_isSepClosed`; the repository search
found the already proved terminal lifting and exact-derived comparison APIs. Inspected
Stacks 02GL, 03QO and 015F in the local source. The file compiles through lcompile.py;
`#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.
The delivered file contains no audit command.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.sepClosedField_etale_decomposition_and_vanishing`
(node `lem-kun-0ezp`). Added 0 holes and split off 0 statements.
There are no remaining sorries in the item or in any file added by this delivery.
The private helper is fully proved. The axiom check also establishes that the final
proof has no transitive dependency on `sorryAx`.

## No longer needed

Removed these original proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`:
  the direct rational-point sections avoid the fibre/residue-field transport entirely.
- `Mathlib.CategoryTheory.Sites.GlobalSections`:
  the unchanged public imports already expose the global-sections API used here.
- `Mathlib.CategoryTheory.Sites.Sheafification`:
  preservation of kernels is supplied by the existing right-adjoint instances.
- `Mathlib.CategoryTheory.Limits.MorphismProperty`:
  base change and the site morphisms are already exposed by the unchanged public imports.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`:
  the exactness APIs come through the exact-derived-functor imports, and no separate
  complex-cohomology comparison is used.

Removed planned proof dependencies `lem-weil-pbc-etale-fibre-discrete-separable-points`
(module `WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`) and
`lem-weil-pbc-exact-functor-complex-cohomology` (Mathlib leaf). The first is replaced by
Mathlib rational-point lifting and disjoint-open gluing. The second is replaced by the
proved comparison of an exact functor's derived image of a single object with the
single object of its ordinary image; no explicit K-injective resolution is needed.
Other consumers may still need the pruned fibre module; this delivery withdraws only
this item's dependency, and does not claim it is globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The proposed route omitted already available shortcuts:
Mathlib supplies the rational-point lifts, and PointCohomology supplies terminal
surjectivity. The blueprint's phrase about decomposing into disjoint affine pieces
need not be formalized as a separate assertion: the explicit singleton open immersions
give the decomposition directly. Empty objects and empty overlaps are included. The
index type is the entire underlying point type, so no quasi-compactness or finite-index
hypothesis is used. The field need only be separably closed; it need not be perfect or
algebraically closed. The direct-image argument works for arbitrary target schemes and
arbitrary morphisms. No change records or forced adaptations are necessary.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
