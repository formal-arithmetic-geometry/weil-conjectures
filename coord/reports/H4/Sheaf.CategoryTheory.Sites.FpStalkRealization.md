## What changed

Filled `CategoryTheory.SiteFpStalkRealization.exists_fp_stalk_realization` in
`Sheaf.CategoryTheory.Sites.FpStalkRealization`. Existing public signatures and
constructions are unchanged. Added proved private helpers for the localized point,
normalized set/module stalk comparisons, finite-colimit preservation, free-module
basis comparisons, common-neighborhood matrix lifting, and the cokernel calculation.
Updated the existing node's proof route and dependencies to match the Lean proof.
The existing public signatures, construction bodies, and public imports are
preserved. The file uses additional elaboration settings and a private-helper
universe; these command changes are documented in
`coord/changes/H4-fp-stalk-proof-context.md`.

The localized point is Mathlib's `Point.over`, transported along the equivalence
between its element category and `Over n`. Its skyscraper adjunction supplies the
right adjoint. Finality supplies the normalized comparison maps. For modules the
underlying additive comparison is proved linear by representing a scalar and an
element at one common stage. Finite free stalks follow from coproduct universal
properties and the unit-stalk isomorphism. Proved private helpers cache the existing sheafification and sheaf-composition
properties during proof elaboration. Their instance registrations are local to the
private-helper section; the final theorem uses them only inside its proof. The private colimit isomorphisms and matrix section have explicit germ or value
APIs and are marked irreducible afterwards, avoiding repeated elaboration of their
constructions. The basis calculation supplies its existing additive and scalar actions, free-generator
ring, and finite index type
explicitly, avoiding inference through the free-sheaf coproduct. The finite-free coproduct comparison, matrix conjugacy, and cokernel transport
are proved for abstract functors, modules, and categories before specialization.
The free sheaf, ring, and basis index are explicit in the germ APIs.
The linear colimit comparison is proved first for abstract presheaves of modules
over a ring diagram, then specialized to sheaves and the site. Its naturality follows from the additive finality comparison through faithful
forgetting. An explicit identity isomorphism relates the restricted presheaves. The localized fiber comparison is also proved first for an abstract
Mathlib site point. Both it and the unit map reuse existing module bundles via
`ConcreteCategory.ofHom`. Finite free coproducts use the original stalk ring instance.
Finally a finite presentation of `M`
is lifted entry by entry and its cokernel is transported along the basis comparisons.

Validation: the complete module compiled cleanly through `lcompile.py` in 50.3 seconds.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.SiteFpStalkRealization.exists_fp_stalk_realization`
(node `lem-sfb-site-fp-stalk-realization`): 1 of 1 original holes closed.
No holes added, no statements split off, and no `sorry` remains in the item.
The proof uses the existing site-point reconstruction declaration as intended by
stage 3; its independent unfinished dependencies are not new holes in this packet.

The finite common-stage argument includes empty index sets. The free-module and
cokernel constructions include rank zero. Choices of colimit cocones in the set
comparison are constrained by the colimit universal property and the prescribed
germ formula; no arbitrary object is chosen from mere existence.

## No longer needed

Removed the private proof imports
`Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`,
`Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`,
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over`,
`Mathlib.CategoryTheory.Comma.Over.Pullback`, and
`Sheaf.CategoryTheory.Sites.GeometricMorphism` (already publicly available).

This proof no longer uses the planned direct proof dependencies
`lem-weil-pbc-localized-sheaves-over-representable`,
`lem-weil-pbc-site-sheaf-sets-limits-sectionwise`,
`lem-sfb-left-exact-left-adjoint-slices`, or
`lem-trf-geometric-inverse-image-exact`.
The associated planned slice-equivalence, slice-adjoint, and exact transported
inverse-image route is replaced by Mathlib site points and the existing proved
`moduleSheaves_colimits_forgetful` declaration. Removed the two obsolete top-level
`tool_uses` entries, retaining the site-point reconstruction approval.
No module is withdrawn: other consumers can still require those declarations.
The blueprint unit's own statement and realized proof route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The DAG's slice-adjoint route
was longer than the available Mathlib route. Its claim that algebraic inverse-image
exactness is required to preserve this cokernel can be replaced by finite-colimit
preservation through additive sheaf fibers. The existing node now records the
actual argument. No consumer adaptation or source-library change was required.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
