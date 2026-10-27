## What changed

Restored the existing sandbox assembly draft and completed
`CategoryTheory.exists_boundedAbove_rhom_hyperExt` from the three already stated
RHom/Postnikov dependencies. The public statement and both public abbreviations are unchanged.
The proof translates the exact-couple page coordinates, identifies E2 naturally, transports
the finite abutment filtration to actual RHom cohomology, and verifies the transition,
naturality and additivity equations by cancellation through inclusions and quotient maps.
All auxiliary declarations are private and proved in the item module.
The complete candidate compiled in 32.1 seconds; the final delivery checks verify the
cleaned file, including the existing dependency axioms.

The proof uses private imports of `LocalRHomCohomologicalBound`,
`PostnikovAdditiveExactCouple`, and Mathlib's restriction-homology comparisons.
The cutoff theorem is publicly imported by `PostnikovAdditiveExactCouple`.
No source-library module or public signature is changed.

## Proved and sorry left

Closed: `CategoryTheory.exists_boundedAbove_rhom_hyperExt`
(node `lem-per-bounded-above-rhom-hyperext`), the item's sole original hole.
Added: none. Remaining holes in the delivered module: none. Split off: none.
This is a proof from the three declared dependencies; their existing holes belong to their
own items and are not claimed closed by this delivery.

## No longer needed

Removed direct proof imports:

- `WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal`
- `WeilConjectures.Algebra.Homology.DerivedInternalHomShiftRight`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.ExactCoupleMorphism`
- `WeilConjectures.CategoryTheory.DerivedCoupleExact`
- `WeilConjectures.CategoryTheory.TruncationTriangle`
- `WeilConjectures.CategoryTheory.HalfPlaneConvergence`
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `WeilConjectures.CategoryTheory.Abelian.Filtration`
- `WeilConjectures.CategoryTheory.ExactCouple`

Removed the obsolete direct `tool_uses` entries from this item's node:

- `lem-pur-derived-internal-hom-shift-right`
- `lem-pur-rhom-into-kinjective-local`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-sf-derived-truncation-triangle`
- `lem-sp-couple-morphism`
- `lem-sp-derived-couple-exact`
- `lem-weil-pbc-hom-into-triangle-exact`
- `lem-weil-pbc-ringed-site-module-sheafification-exact`
- `lem-weil-pbc-truncation-triangle`
- `thm-sp-half-plane-convergence`

The three current `proof_deps` are all used and retained. The older detailed dependencies
are now handled inside those three items; no claim is made that their modules are absent
from the targets' transitive closure. No module is withdrawn and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The existing assembly requires explicit
index translation, finite-cycle stabilization, and uniqueness arguments to obtain all of
the strict transition/naturality equations in the Lean target; these are now proved.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
