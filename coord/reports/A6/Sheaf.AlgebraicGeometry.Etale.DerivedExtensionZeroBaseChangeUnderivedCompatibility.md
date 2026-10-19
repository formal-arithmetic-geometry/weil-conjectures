## What changed

Filled the four proof holes in
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility`.
No signature, definition, or visibility changed. Removed eight unused proof imports
from the current source version. Updated the node's proof and
proof dependencies to the actual shorter route through the existing module-valued
open-square base-change API.

The pullback specialization is reflexivity. The specified open/etale comparison is a
whiskered identity in their common localization Kan-extension model. Simplifying this
identity identifies the transported map with the canonical inverse-conjugate mate.
Invertibility follows by composition. The main theorem uses the already proved
`unit_map_openImmersionLowerShriekBaseChangeMap_app` for its transpose clause;
functoriality and inverse cancellation prove the restriction clause.

## Proved and sorry left

Closed all four original holes (4 closed, 0 added):

- `AlgebraicGeometry.Etale.chosenSquareEtaleLowerShriekBaseChangeMate_pullback`.
- `AlgebraicGeometry.Etale.chosenSquareEtaleLowerShriekBaseChangeMap_eq_mate`.
- `AlgebraicGeometry.Etale.isIso_chosenSquareEtaleLowerShriekBaseChangeMap`.
- `AlgebraicGeometry.Etale.derivedExtensionZeroBaseChangeUnderivedCompatibility`.

Validation: on resuming the retained sandbox against current sources, `lcompile.py`
compiled the complete module cleanly in 3.8 seconds (exit code 0).

All belong to node
`lem-cbc-derived-extension-zero-base-change-underived-compatibility`.
No sorry remains in the delivered module and no theorem is split off.
The existing dependency
`openImmersionToEtaleLowerShriek_adjunction_agreement` still has its own proof hole;
this delivery uses its invertibility assertions as intended by the stage-3 brief.

## No longer needed

All four existing public imports are used by the existing signatures or definitions.
Removed these eight unused proof imports from the current source version:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`.
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`.
- `WeilConjectures.SixFunctors.BaseChange.Square`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `WeilConjectures.SixFunctors.OpenClosed.Complex`.

The last four are already available through the retained public imports; their direct
imports are redundant. No module was withdrawn.

The following declared proof dependencies are unnecessary for this proof:

- `lem-weil-pbc-inverse-image-composition-module-linear`
  (`Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`).
- `lem-weil-pbc-underived-exchange-module-linear`
  (`Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`).
- `prop-weil-pbc-inverse-image-modules-exact`
  (`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`).
- `lem-weil-pbc-etale-shriek-base-change-modules`
  (`WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`).

The source-library open base-change API is already expressed in ModuleCat coefficients,
including the transpose formula; separate lifting from abelian sheaves and the
fiber-product-only etale invertibility lemma are unnecessary. Removed these four entries
from proof_deps and withdrew the three corresponding old top-level tool_uses approvals.
This is local dependency pruning, not a claim that those modules are globally unreached.
The unit record has no realized steps to bypass, and the open-extension base-change,
canonical module mate, adjunction comparison, and restriction normalization are retained.

## Where the brief, the DAG or earlier work was wrong

The planned transpose calculation is already proved as
`AlgebraicGeometry.Etale.unit_map_openImmersionLowerShriekBaseChangeMap_app` in
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`.
The current open and etale lower shriek constructions and adjunctions agree
definitionally; the specified comparison is the identity after whiskering is simplified.
Thus no new intermediate theory or statement repair is required.

The argument imposes no nonemptiness, nonzero-ring, nonzero-sheaf, or nonidentity-map
assumption. The empty-open, zero-ring, zero-sheaf, and identity-square cases use the same
functor and isomorphism identities. The original Finite coefficient hypothesis stays.

Searches performed with msearch.py: LeanFinder for adjunction conjugation and comparisons;
Loogle for CategoryTheory.conjugateEquiv; grep for the open-square transpose and inverse
conjugation component formulas; LeanSearch for component inverses. Local rg searches of
Mathlib and both library roots found the existing BaseChangeSquare transpose theorem.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
