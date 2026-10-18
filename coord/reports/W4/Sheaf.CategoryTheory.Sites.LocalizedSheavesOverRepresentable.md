## What changed

Proved `CategoryTheory.exists_localizedSheavesOverRepresentable` in
`Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`, preserving its signature.
Constructed the sigma presheaf, its projection and functor on sheaves, the fibre sheaf
and functor, both comparison maps and their naturality. Both comparisons are isomorphisms
by local bijectivity, using Mathlib's covering equalizer/image sieves. `Equivalence.mk`
assembles the equivalence and all required section formulas are definitional.
All added helpers are private and completely proved; all data definitions are explicit.
The helpers work over an arbitrary Grothendieck topology; the theorem specializes to
`J.toGrothendieck` as in the existing Lean signature.

Added the proof-only import `Mathlib.CategoryTheory.Sites.LocallyBijective` and updated
the node's proof route to match. The unit and chapter route is retained.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.exists_localizedSheavesOverRepresentable`
(node `lem-weil-pbc-localized-sheaves-over-representable`).
Added 0 holes; split off 0 statements. There are no remaining `sorry`s in the delivery.

## No longer needed

Removed proof imports `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
and `Sheaf.CategoryTheory.SiteCoveringAxioms`.
The proof does not use node `lem-weil-pbc-site-sheafification-sections-local` or its module:
Mathlib's proved local-injectivity/surjectivity API supplies the exact local-section
facts directly. This node is removed from the item's proof dependencies.
The site-covering definition node `def-weil-pbc-sites-and-cohomology` remains a conceptual
definition dependency, but its separate Lean module is unnecessary for the proof.
All public imports remain unchanged. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The node's `lean.statement` and its 2026-10-17 note describe a theorem generalized to
`J : GrothendieckTopology C`, but the actual repository module still has the older
precoverage signature with stability, covering-pullback and sheafification assumptions.
This delivery proves that actual signature unchanged; all new helpers already work
for arbitrary Grothendieck topologies. No existing consumer applies the theorem by name
(`tools/downstream.py --uses` reports only its own declaration). No statement repair
or forced consumer adaptation is included.

The plan's separate precoverage local-section wrapper is unnecessary: Mathlib provides
the local statements directly for covering sieves without additional pullback assumptions.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
