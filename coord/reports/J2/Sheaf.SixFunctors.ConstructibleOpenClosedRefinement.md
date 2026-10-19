## What changed

Proved `AlgebraicGeometry.Scheme.exists_finite_open_closed_refinement` and its finite
pullback-tree construction. Added the recursive `SchemeRefinementTree`, its finite
parent-before-child encoding, and the tree induction theorem used by the item. The
geometric proof constructs the quasi-compact open/closed cuts and iterates their
pullbacks over the finite families.

## Proved and sorry left

Proved, with no `sorry` left in the delivered modules:

- `AlgebraicGeometry.Scheme.exists_finite_open_closed_refinement`;
- `AlgebraicGeometry.Scheme.exists_finite_refinement_tree`;
- `AlgebraicGeometry.Scheme.SchemeRefinementTree.exists_fin_encoding`;
- `AlgebraicGeometry.Scheme.SchemeRefinementTree.allLeaves_bind` and
  `allLeaves_mono`.

Closed the item's one original hole, in
`AlgebraicGeometry.Scheme.exists_finite_open_closed_refinement`. Added zero holes;
all three supporting modules are fully proved. The existing theorem signature and
visibility are unchanged. The construction handles no partitions, empty schemes,
and empty children; pairwise disjointness of the input strata is not needed by the proof.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso`
and `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
Also removed the unused direct proof import `Mathlib.AlgebraicGeometry.PullbackCarrier`
from the item (the tree construction retains its own needed import), and withdrew the
obsolete `lem-weil-pbc-closed-immersion-residue-field-iso` tool approval.
The nodes `lem-weil-pbc-closed-immersion-residue-field-iso` and
`lem-weil-pbc-reduced-induced-closed-subscheme` are unnecessary for this route:
Mathlib's `Scheme.Pullback.range_fst` and `range_fst_comp` supply the image
identities, and `IdealSheafData.vanishingIdeal` supplies the closed complement.

The separate planned steps through `lem-weil-pbc-open-preimage-fibre-product`,
`lem-weil-pbc-quasi-separated-affine-cover-criterion`,
`lem-weil-pbc-closed-in-quasi-compact`, and `lem-weil-pbc-closed-immersion-comp`
are unnecessary. The generic pullback range lemmas, quasi-separatedness under
immersions, compactness instances for quasi-compact morphisms, and composition of
immersions supply these properties directly. No existing library module is withdrawn;
other uses of these nodes are unaffected.

## Where the brief, the DAG or earlier work was wrong

The earlier retained attempt split the finite tree theorem but left it as `sorry`. The
Lean proof requires an explicit recursive tree invariant and a finite-order transport;
those are now proved in `SchemeRefinementTreeEncoding`. The resumed dry run also
identified an overlong definition-node `lean.statement` record; it now records only
the inductive declaration signature, as the delivery checker requires. The resumed source
check also added the two explicitly cited scheme/quasi-separatedness statement dependencies
to the new tree-construction node. The original proof-dependency list mentioned residue-field
points, but the range lemmas make that route unnecessary.

## New nodes

`def-fix-scheme-refinement-tree`, in `Sheaf.SixFunctors.SchemeRefinementTree`, defines
recursive finite splitting trees, leaf predicates and replacement. Its source is the
finite refinement construction of Stacks Topology Tag 09Y4. Recorded LeanSearch,
LeanFinder/Loogle and library/Mathlib grep searches found no existing dependent
scheme-tree interface. The definitions are recursive constructions; the two leaf
preservation theorems are proved by induction.

`lem-fix-scheme-refinement-tree-encoding`, in
`Sheaf.SixFunctors.SchemeRefinementTreeEncoding`, proves that a recursive tree has
finite parent-before-child labels with all geometric and leaf properties. It formalizes
the finite-tree bookkeeping of the same Tag 09Y4 construction. Recorded LeanSearch,
LeanFinder, Loogle and grep searches found the finite-order numbering tool
`Fintype.orderIsoFinOfCardEq`, but no theorem supplying this dependent geometric encoding.
The proof constructs lexicographically ordered labels and transports them to `Fin N`.

`lem-fix-constructible-open-closed-refinement-tree`, in
`Sheaf.SixFunctors.ExistsFiniteRefinementTree`, proves the finite pullback-tree construction
from already chosen cuts. Its source is the scheme-theoretic realization of Stacks
Topology Tag 09Y4 in the item's original proof steps 6–9. The recorded semantic and
text searches found constructible-set and cover statements, but no such scheme-theoretic
refinement. The proof builds each two-stage split and iterates it over the finite set
of strata, then applies the proved encoding theorem. No new statement is left with `sorry`.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
