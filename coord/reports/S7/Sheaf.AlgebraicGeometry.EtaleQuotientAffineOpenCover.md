## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.etale_quotient_affine_open_cover` without
changing its statement or any definition. All edits are in its owning module and
its DAG proof record. Four proved private helpers establish restricted-relation
geometry, coproduct chart geometry, local chart membership, and local lifting.

The quotient isomorphism uses `etale_relation_restriction_quotient`; the chart maps
and open representability use `etale_relation_finding_opens`. Reflexivity supplies
a common section and hence surjectivity of the coproduct relation projections.
The local lifting proof uses the locally generated image subsheaf and the given
universal property. No global sheafification instance is assumed or constructed.
No data is chosen from a new unproved existence statement.

The proof preserves the 02WW affine-refinement route. It also works for arbitrary
open covers: the affine hypotheses need no use in these covering assertions.
Empty covers, empty test schemes, infinite indices and overlapping chart images
are handled by the ordinary covering and pullback arguments.

Server single-file compilation succeeds within the 60-second limit. The final
pruned-import version is compiled again by the delivery checks.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.AlgebraicSpace.etale_quotient_affine_open_cover`
(node `lem-trf-etale-quotient-affine-open-cover`).

Added 0 holes. Left 0 holes in every delivered Lean file. The two existing imported
quotient lemmas remain their owners' stage-3 items; this delivery proves the
assigned theorem from those declarations as required. All four private helper
proofs are complete.

## No longer needed

Removed proof imports:
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`

The proof no longer needs their nodes `def-weil-pbc-sites-and-cohomology` and
`lem-weil-pbc-site-sheafification-sections-local`; removed these proof edges and
obsolete `tool_uses` entries. Mathlib's actual fppf topology, slice covering
criterion and subpresheaf closure suffice. Other consumers may still need these
modules, so neither module is withdrawn.

Added proof imports for Mathlib coproduct comparison, clopen topology and
subsheaves. No public import was changed. Both quotient dependency imports remain
needed. No other planned dependency is pruned; etale base change and composition
are now explicit DAG dependencies for the direct restricted-relation proof.

## Where the brief, the DAG or earlier work was wrong

The restriction-quotient theorem returns geometric assertions only after both
quotient sheaves and their units have been supplied. The assigned conclusion
requires those assertions before any such sheaves are supplied. The proof
therefore establishes this geometry directly by the pullback universal properties
and etale base change/composition. It uses the existing restriction-quotient theorem
only when Q is supplied.

The stated `sheafification_sections_local` theorem requires a value universe
containing the object universe of the big site, whereas the assigned statement
specifies Type u valued sheaves on Over Scheme.{u}. Instead of adding a global
sheafification assumption, the proof realizes the same local covering argument
with the locally generated image subsheaf and the given universal property. This
is the same 00WK local-image argument and preserves the statement exactly.

No new nodes, public declarations, definition repairs, source-library edits or
consumer adaptations were necessary.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
