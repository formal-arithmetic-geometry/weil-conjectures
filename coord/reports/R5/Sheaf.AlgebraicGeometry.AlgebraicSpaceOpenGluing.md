## What changed

Replaced the sole hole in `AlgebraicGeometry.algebraicSpace_of_open_gluing` by a complete
Lean assembly of the open-cover diagonal and open-coproduct base-change results.
The theorem's signature, universes, hypotheses, public import and conclusion are unchanged.

The proof explicitly converts monic sheaf maps into range subfunctors, derives the pairwise
representability condition from each summand's diagonal, constructs the scheme coproduct
of the representing opens, proves its projection etale using its open cover, and proves
surjectivity by lifting points through the fppf covering. It transports the base-change
comparison through the ULift Yoneda isomorphism, pastes pullback squares for surjectivity
of the composite atlas, and uses the existing `AlgebraicSpace.isEtale_comp`.

Added `Sheaf.AlgebraicGeometry.SmallOpenCoproductCover` for the independent universe and
local-cover argument missing from the available interfaces. It assumes no algebraic-space
structure or diagonal for any summand. Its conclusion only supplies a small subfamily with
the same coproduct and local lifts; it contains no diagonal or atlas conclusion for F.
This is a genuine part of the argument, rather than the item with a repackaged hypothesis.

Validation: both sandbox modules compiled together through lcompile.py. After removing
unused imports and an unused private helper, both compiled again (5.1s and 9.8s on the
server). The new module contains one named theorem hole and no definitions. No existing
statement or definition was changed, and no forced adaptations are needed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.algebraicSpace_of_open_gluing`
(node `lem-trf-algebraic-space-open-gluing`). The item now contains zero `sorry`.
All its private helpers are proved.

Added one hole: `AlgebraicGeometry.small_open_coproduct_cover`, in its own module,
node `lem-trf-small-open-coproduct-cover`. Its proof is exactly `by sorry`; its docstring
and node give a complete argument, including a non-circular discrete two-point detector
for the large-index size reduction and the Sierpinski open-image argument for Epi.

Counts: 1 original hole closed, 1 new hole added, 1 decomposition, net 0 holes closed.
The main theorem is proved from the named statements, not claimed independent of their
remaining proof obligations. The imported existing declarations retain their own proofs
and any existing holes; none were added to them by this packet.

## No longer needed

Removed all four original proof-only imports:
`Sheaf.AlgebraicGeometry.FppfAffineRefinement`,
`Sheaf.CategoryTheory.SiteCoveringAxioms`,
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability`.
They are not used directly by this assembly. No source declaration is removed or changed.

The item's direct proof dependencies no longer include
`lem-trf-fppf-sheaf-coproduct-partition`, `lem-pc-zariski-coverings-are-fppf`, or
`def-weil-pbc-sites-and-cohomology`. The first cannot handle its arbitrary label universe;
the latter two belong to the independent local-cover argument. This does not assert that
these modules leave the targets' entire closure: the existing base-change proof uses the
partition theorem, and the new small-cover node still uses the covering statements.

Removed obsolete direct tool approvals `lem-pc-fppf-affine-refinement` and
`lem-pc-schemes-criterion` from this item's `tool_uses`; the imported diagonal/base-change
nodes retain their own dependencies and approvals. No global module withdrawal is claimed.
Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The item has I : Type w and values in Type u. The available partition and base-change
statements instead put labels and values in the same universe `max u v`; the diagonal
statement requires I : Type u. Setting v = w lifts the values too and does not apply
them to the given small-valued colimit. Nor does the categorical Epi hypothesis by itself
instantiate Mathlib's Epi/local-surjectivity equivalence here: that interface asks for
HasSheafify on the big site with Type-u values. No such instance was assumed or invented.

The diagonal node's stage-2 review already advised restricting to the summands meeting
an atlas. The new lemma makes that missing argument an explicit separate obligation.
Its proof uses two-valued continuous-function detectors to obtain smallness before using
any small-index coproduct theorem. Thus there is no circular invocation of the current
partition interface. The Sierpinski continuous-function sheaf permits direct use of Epi.

Checked the empty base/test schemes, empty index set, empty summands, repeated summand
images, and arbitrary label universe. The initial summands omitted in the size reduction
have no sections on nonempty schemes and unique sections on empty schemes. Both the
coproduct universal property and the empty-cover case of the conclusion are preserved.
The new statement uses no summand diagonal. No source-library changes, unit-route bypass,
target changes, hollow definitions, arbitrary witness definitions, or new axioms occur.

## New nodes

`lem-trf-small-open-coproduct-cover` in `dag/nodes/sec-trace-formula/` realizes the
set-theoretic and local-cover part of Stacks Tag 02WR, with explicit detector and
open-image arguments. It inherits the item's chapter, unit and blueprint ancestry.
LeanSearch, LeanFinder and Mathlib grep searches found related coproduct and scheme-cover
facts but no matching statement; the rejected Loogle query is recorded honestly.
The main node's proof, proof dependencies and proof origin now follow the compiled Lean.
There are no change records because existing signatures and definitions are unchanged.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
