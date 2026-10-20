## What changed
Proved `AlgebraicGeometry.Scheme.proEtale_unit_leray_chain_formula` without changing its
statement, definitions, instances, or public imports. Three fully proved private helpers
establish the composition-unit factorization, its compatibility with the derived adjunction
unit, and the arbitrary-chain-map calculation in general abelian categories. The public theorem
specializes that calculation to the recorded pro-etale module functors.

The shorter route uses the proved source `rightDerivedFunctorCompIso'`, its defining unit
factorization, Mathlib `Adjunction.derivedη_fac_app`, and naturality of the right-derived units.
The generic calculation avoids unfolding the intrinsic realization during normalization.
Updated the item's DAG proof, proof dependencies, proof origin, and obsolete tool approvals.
`coord/changes/B3-ProEtaleUnitLerayPrivateCalculation.md` records the scoped generic variable
command required by the mechanical interface checker. Source inspection with
`tools/downstream.py` finds zero current Lean consumers; no adaptations are required.
The unit `sk-d-weil` has no realized statement or proof steps affected by this change.

Validation: the final module compiles cleanly through `lcompile.py` in 27.1 seconds, with no
warnings or textual holes. Delivery preflight additionally checks the compiled declarations.
Searches used `msearch.py` with LeanFinder, Loogle and grep, plus source and Mathlib searches.
The source `EtaleKInjectiveUnitLeray` supplied the generic categorical calculation; its etale
statement is not applied to pro-etale coefficients.

## Proved and sorry left
Closed one original hole: `AlgebraicGeometry.Scheme.proEtale_unit_leray_chain_formula`
(node `lem-trf-proetale-unit-leray-chain-formula`).
Added zero holes; zero holes remain in the delivered module. No statements were split off.
The three private helpers `unitLerayFac`, `unitLerayHomotopy`, and `unitLerayChain` are proved.
The earlier sandbox-only `proEtaleUnitLerayNormalization` hole is removed, not delivered.

## No longer needed
Removed five unused private proof imports:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`

The proof no longer needs the declared dependency nodes
`lem-pc-pre-derived-adjoint-functors-general`, `lem-sf-kinjective-derived-map-computation`,
`lem-weil-pbc-kinjective-total-derived`, and
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: the source definitions already
provide the precise canonical adjunction and composition comparisons being calculated.
`prop-pur-kinjective-resolutions-exist` is also unnecessary as a separate proof dependency:
the recorded pro-etale operations already supply their K-injective-resolution instances.
Its existing statement dependency is retained. Removed these five obsolete top-level
`tool_uses` entries, retaining the other approvals in their original order.

Used the existing closed source node `lem-fin-kinjective-derived-composition` and Mathlib-leaf
node `lem-weil-pbc-exact-functor-derived-factorization` instead. These already lie in the
public import closure. No module is withdrawn, and other consumers may still need the five
removed proof-import modules.

## Where the brief, the DAG or earlier work was wrong
The previous attempt's claimed missing localization bridge is supplied by the existing
quotient comparison definitions. Its sandbox-only normalization statement reversed the
orientation: the hom of `rightDerivedFunctorObjQIso` is inverse to the right-derived unit.
The final proof needs no new bridge theorem and no new obligation.

A proposed intermediate special case requiring K-injectivity of L(I) was discarded:
exact pullback alone does not preserve K-injectives. The retained homotopy-category argument
never makes that assumption and works for every chain map j, including zero and maps that
are not quasi-isomorphisms. The generic calculation is valid for identity adjunctions and
zero categories as well. The original DAG's explicit fraction and terminal-ringed-topos
computations are valid but unnecessary for the already defined canonical comparisons.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
