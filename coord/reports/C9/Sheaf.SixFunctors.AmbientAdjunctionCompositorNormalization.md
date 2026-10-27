## What changed

Proved `WeilConjectures.AmbientCompositor.ambientAdjunctionCompositorNormalization`
in `Sheaf.SixFunctors.AmbientAdjunctionCompositorNormalization`, preserving all existing
statements and definitions. Added proved private helpers for adjunction normalization,
exact descent, coherence, and transport across the finite realization equivalences.
The system argument is on the full diagram module category, before evaluation.
The finite section formula is obtained from the fixed-scalar composition formula using
the existing bijective section realization and normalized direct-image comparison.

Updated the item's DAG proof, proof dependencies and proof origin to this route.
No other module was changed; no definition or interface repair is involved.
The full module compiles through `lcompile.py` without warnings (49.2 seconds).

## Proved and sorry left

Closed the single original hole in
`WeilConjectures.AmbientCompositor.ambientAdjunctionCompositorNormalization`
(node `lem-sf-ambient-adjunction-compositor-normalization`).
Holes closed: 1. Holes added: 0. Split-off statements: 0.
No `sorry` remains in the delivery. All private helpers are proved.
Existing named theorem dependencies may retain their own holes, as permitted by stage 3.

## No longer needed

Removed these private proof imports, because generic adjunction calculus and the
existing exact-descent API replace their proposed geometric/resolution route:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.SixFunctors.ResolvingDerivedAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenDerivedImage`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`

Removed these direct DAG proof dependencies. This records what this proof does not use;
it does not assert that another consumer, or an existing definition, no longer needs them:

- `lem-coef-semilinear-derived-sections`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-sf-proetale-tensor-composition-unit`
- `lem-pur-proetale-constant-ring-composition`
- `def-pc-fibre-product`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-weil-pbc-localization-universal-property`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `lem-sfb-resolving-derived-adjunction-normalization`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `def-pur-localized-ringed-site`
- `lem-weil-pbc-conjugate-iso-unit-equation`
- `def-weil-exact-derived-adjunction`
- `def-weil-pbc-adjunction-mate`
- `lem-weil-pbc-adjunction-of-natural-bijection`
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-diagram-site-realization`
- `lem-pc-pre-derived-adjoint-functors-general`
- `lem-exc-proetale-open-derived-image`
- `lem-weil-proetale-weakly-etale-localization`

Removed the obsolete `tool_uses` approvals of the previous route (all eleven entries):

- `lem-coef-semilinear-derived-sections`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-sf-proetale-tensor-composition-unit`
- `lem-pur-proetale-constant-ring-composition`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `lem-sfb-resolving-derived-adjunction-normalization`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-weil-pbc-diagram-site-realization`
- `lem-pc-pre-derived-adjoint-functors-general`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-exc-proetale-open-derived-image`

No Lean module is withdrawn. Public imports and the existing public interface are retained.
The blueprint unit `sk-rem-sf-pf-done` has no realized proof steps to bypass.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned geometric and resolving arguments were longer
than necessary for the actual declarations: `Operations` already includes the exact
functors and specified adjunctions, while the source library proves derived compositor
conjugation and fixed-scalar pullback coherence. The remaining work is categorical
normalization and faithful transport of the section formula.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
