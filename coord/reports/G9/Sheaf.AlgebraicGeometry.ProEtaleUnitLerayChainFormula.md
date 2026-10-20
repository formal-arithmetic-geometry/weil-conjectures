## What changed

Proved `AlgebraicGeometry.Scheme.proEtale_unit_leray_chain_formula` in
`Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula`. All existing public signatures,
definitions, instances, and public imports are unchanged.

Three proved private helpers calculate the universal-unit factorization of the Leray
comparison, combine it with the derived adjunction unit equation, and pass to arbitrary
chain maps between K-injective complexes. The calculation abstracts the coefficient functors
from the proved argument in `Sheaf.Paper.EtaleKInjectiveUnitLeray`; it does not identify
abelian étale sheaves with pro-étale module sheaves. The public proof specializes this
categorical calculation to the recorded module adjunction and terminal comparison.

The realization and comparison definitions are marked irreducible only locally during
this calculation. This prevents expensive unfolding of the concrete realization functors;
it changes no exported definition or reducibility attribute. Profiling and reduced-heartbeat
diagnostic runs identified this issue; the final file uses the normal compilation limits.

The static preflight requests a change record for scoped commands even though the
attributes are local and the helper variables are section-scoped. The record is
`coord/changes/ProEtaleUnitLerayChainFormulaLocalCommands.md`.
Read-only consumer checks found no current downstream Lean modules and only local
uses of the two affected names; no consumer or target interface changes.

Updated the existing node's proof, proof dependencies, proof origin, and removed obsolete
entries of its tool-use list to describe the implemented route. No new nodes or modules.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.proEtale_unit_leray_chain_formula`
(node `lem-trf-proetale-unit-leray-chain-formula`).

Validation: `lcompile.py` compiled the complete file without errors or warnings; the
final direct specialization compiled in 26.3 seconds. `#print axioms unitLeray_chain` reports only `propext`, `Classical.choice`,
and `Quot.sound`. The public theorem also reports `sorryAx` from the unchanged upstream
coefficient constructions.

Added zero holes. No `sorry` remains in the item, including its three private helpers.
This is a proof, not a decomposition. Existing coefficient constructions and their
upstream obligations are unchanged.

The formula is proved for arbitrary `j`; no quasi-isomorphism assumption is added.
The generic calculation works for the identity functor, zero morphisms, and zero
coefficient categories without additional hypotheses. It uses naturality before
cancelling only the derived-functor units known to be invertible on I and J.

## No longer needed

Removed these five private proof imports:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`

The direct proof dependencies
`lem-sf-kinjective-derived-map-computation`,
`lem-weil-pbc-kinjective-total-derived`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`lem-pc-pre-derived-adjoint-functors-general`, and
`prop-pur-kinjective-resolutions-exist` are unnecessary for this proof route.
The recorded operations already supply the K-injective resolution instances. The
canonical derived adjunction has Mathlib's defining unit compatibility, so no explicit
fraction or arbitrary-resolution comparison is required. Leray is already defined using
the proved generic composition isomorphism, whose defining universal-unit equation
normalizes it directly; no construction of a terminal ringed site is required.

The resolution-existence node remains an unchanged statement dependency. These removals
are local proof-dependency pruning; no module is withdrawn, and no claim is made that
other consumers no longer need the removed imports or nodes. The unit route is preserved:
`dag/units/sk-d-weil.json` assigns no unit statement or proof step to this auxiliary node.

The replacement dependencies are the already proved
`lem-fin-kinjective-derived-composition` and the Mathlib leaf
`lem-sc-derived-adjunction-from-underived`, together with the retained operations,
right-adjoint K-injectivity, and termwise-adjunction nodes.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was needed. The six-step plan was mathematically
valid but unnecessarily general: its resolution-comparison and terminal-ringed-topos
specializations can be replaced by the defining universal-unit equations of the exact
recorded constructions. The original proof docstring and node have been updated to
reflect that shorter argument. No source-library module or target was modified.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
