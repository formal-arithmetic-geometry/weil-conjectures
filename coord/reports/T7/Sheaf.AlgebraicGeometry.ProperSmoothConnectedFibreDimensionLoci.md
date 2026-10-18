## What changed

Proved `AlgebraicGeometry.proper_smooth_connected_fibre_dimension_loci` in its original
signature. Four fully proved private helpers compare ordinary and geometric fibre dimensions,
recover fixed relative dimension for connected smooth schemes over fields, and deduce pure
dimension from irreducibility. The proof constructs the exact dimension level sets, descends
local constancy along the proper quotient map, proves their finite disjoint cover, and verifies
all base-change clauses. The zero-dimensional restriction is etale and therefore has discrete
fibres, which proves the project's finite-type quasi-finiteness predicate.

Added proof-only imports of `WeilConjectures.AlgebraicGeometry.Regular`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Fiber`. Updated the item's DAG proof, proof
dependencies and proof origin to this route. Existing public signatures and public imports
are unchanged. No definition or statement repair, consumer adaptation or change record is needed.

Validation: the complete proof compiled with lcompile.py, without warnings. The empty base,
empty individual loci, d = 0, and arbitrary residue fields are covered without auxiliary
nonemptiness assumptions: geometric connectedness supplies precisely the required nonemptiness.
The chosen local chart has nonempty source because it contains an actual fibre point.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.proper_smooth_connected_fibre_dimension_loci`
(node `lem-weil-pbc-proper-smooth-connected-fibre-dimension-loci`).

Added 0 holes. Split off 0 statements. There are no remaining sorry declarations in this
module or anywhere added by this delivery. The proof uses the existing
`AlgebraicGeometry.geometricallyConnected_iff_connectedSpace_of_isAlgClosed`
(node `lem-weil-geometrically-connected-algebraic-closure`), which remains a separate
existing proof obligation; this delivery does not claim its transitive proof is closed.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`: connected smooth
  fibres are integral, so a nonempty smooth chart computes their finite dimension directly.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: already publicly provided by the used source
  smooth module; the etale API itself remains used.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: already publicly provided by the used
  source smooth module; local dimension and its API remain used.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the public compatibility
  import already re-exports this module; no proof-specific declaration from it is needed.

Removed declared proof dependencies:

- `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension` and its module
  `Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`: finite dimension
  follows instead from the nonempty standard-smooth chart and integral open dimension equality.
- `def-weil-connected-scheme`: there is no separate clopen-rank saturation argument;
  the existing geometric-connectedness and regularity APIs supply the needed instances.
- `lem-weil-pbc-open-fibre-product`: no source rank-locus restriction is constructed;
  the proved ordinary-fibre comparison handles restriction to a base open directly.
- `lem-weil-pbc-dimension-at-point-open-subspace`: no manual local-dimension transport is
  needed; the source relative-dimension APIs perform that comparison internally.
- `lem-sc-dim0-finite`: etaleness gives discrete fibres directly, so the argument by a
  finite set of closed points is unnecessary.

Pruned only the obsolete top-level tool approval for the differentials-rank node; the remaining approvals retain their original order.
The item's public statement dependencies remain. These are local proof-route pruning claims;
other library users may still require these modules. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned differential-rank and finite-closed-points arguments were unnecessary, because
stronger usable relative-dimension and ordinary-fibre comparison declarations already exist
in the source library. No mathematical error in the original theorem was found.

The existing `lem-sc-smooth-regular` prose only asserts the result for curves, although its
recorded Lean declaration `IsRegular.of_smooth` works for every smooth scheme over a field.
A new node records this already proved general source theorem exactly; no duplicate Lean
notion or declaration was introduced. The additional regular-connected-integral and
integral-open-dimension dependencies are existing closed source results used below the
unit level, rather than new work assigned to another unit.

## New nodes

`lem-weil-pbc-smooth-scheme-over-field-regular` attaches the already proved source theorem
`AlgebraicGeometry.IsRegular.of_smooth` to its full dimension-independent statement
(Stacks Tag 056S, varieties.tex, lemma-smooth-regular). The source proof and theorem were
read; the existing curve-only node is insufficient as a statement of this general tool.
Mathlib searches used LeanSearch, LeanFinder and grep; blueprint text search found no
matching general node. This node adds no module and no proof hole. Its empty-scheme case
is vacuous, and no perfectness assumption on the field is needed.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
