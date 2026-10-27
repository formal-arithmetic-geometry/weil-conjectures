## What changed

Filled the six theorem proofs in `Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence`.
The proofs use the existing fixed-compactification normalized-mate declarations, the
canonical support right-mate equation, and the derived sum-counit equation. Proved private
helpers transport the coefficient-unit composition and square equations from the source
library and identify the chosen compactification comparisons. An arbitrary Cartesian square
is compared with the canonical pullback square through its canonical isomorphism.
All existing signatures, definitions, docstrings, and public imports are unchanged.
The node proof and proof dependencies now describe this argument. The packet changes
only the assigned Lean file, its proof record, and this report.

## Proved and sorry left

Closed all six original holes (full namespace `AlgebraicGeometry.Etale`):

- `etaleSumRightAdjoint_comp`
- `etaleSumRightAdjoint_id`
- `etaleSumRightAdjoint_baseChange`
- `etaleSumRightAdjoint_evaluation`
- `etaleSumRightAdjoint_refinement`
- `etaleSumRightAdjoint_openRestriction`

Holes added: zero. Holes left in the item: zero. No split-off statements or new modules.
The cited existing dependency theorems retain their own proofs or holes; this delivery
assembles the assigned theorem from those declarations, as required by stage 3.

## No longer needed

Removed these redundant private imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`
- `WeilConjectures.SixFunctors.BaseChange.Square`
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`

The direct proof no longer invokes `lem-pur-etale-sum-composition-counit`,
`prop-weil-pbc-inverse-image-modules-exact`, or `lem-weil-pbc-mate-pasting` as separate
steps. Composition and mate pasting are provided by the existing normalized-mates node;
coefficient-unit compatibility is proved from the source-library unit-composition theorem.
Those declarations remain needed indirectly by dependencies; no module is withdrawn or
claimed to be globally pruned. The support-map compatibility dependency likewise remains
inside the canonical support right-mate module.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The recorded support right-mate equation is presented for
the canonical fiber product, while the assigned base-change theorem quantifies over an
arbitrary Cartesian square. The proof supplies this transport explicitly using the canonical
pullback isomorphism, identity-base open restriction, and normalized pasting.
The existing source library already proves unit-composition compatibility, so no new
coefficient-unit lemma with a hole is necessary. The unit route is preserved.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
