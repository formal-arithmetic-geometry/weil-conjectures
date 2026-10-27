## What changed

Replaced the hole in `AlgebraicGeometry.Etale.supported_kummer_boundary_pullback`
without changing its statement or public imports. The proof extracts the uniquely
normalized integral pole-extension class from the supplied boundary witnesses,
proves naturality of the coefficient generator through closed base change, and
proves the Kummer connecting-class square from a morphism of short exact
sequences. The exact-functor comparison transports Ext classes across the
module/abelian square. The supported integral derived unit makes forgetting
coefficients injective on these degree-two classes, so the integral geometric
square implies the required equality.

Added `Sheaf.AlgebraicGeometry.CartierPoleBoundaryPullback` for the remaining
geometric step. Its statement concerns only the degree-one integral extension
of a Cartier pair, before any exponent, finite coefficient ring, Kummer
connecting morphism, supplied boundary class or twist transport. It is a
strict part of the original argument. The coefficient comparison, source
normalization, Kummer naturality, associativity and injectivity arguments are
proved in the item rather than included in the new obligation.

Only the item module, its proof-route node, the new module and its new node are
changed. There are no shared interface changes or forced adaptations.

Validation: both sandbox modules compiled with `lcompile.py --all` within the
60-second per-file limit. Profiling options were removed for delivery.

## Proved and sorry left

Closed the one original hole, by reduction:
`AlgebraicGeometry.Etale.supported_kummer_boundary_pullback`.

Added one hole:
`AlgebraicGeometry.Etale.cartierPoleBoundary_pullback`
(node `lem-asd-cartier-pole-boundary-pullback`).

The item now has zero holes; the new module has one. This is a decomposition,
not a net reduction of the number of holes. All local helper lemmas are proved.

## No longer needed

Removed these direct proof imports and direct planned dependencies:

- `Sheaf.AlgebraicGeometry.SupportedKummerCartierPullback`
  (`lem-asd-supported-kummer-cartier-pullback`): geometry is isolated in the
  integral lemma, whose plan retains this dependency.
- `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`
  (`lem-amb-relative-torsor-cohomology`): the item uses the pole-extension
  specification directly, instead of passing through supported cohomology.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`
  (`lem-amb-kummer-any-base`): still used through existing public imports;
  the Kummer short exact sequence remains a proof dependency.
- `WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget`
  (`lem-weil-pbc-etale-module-cohomology-forget`): use the supported integral
  derived-unit bijection directly on Ext instead of module cohomology.
- `WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`
  (`lem-weil-pbc-etale-module-pullback-forget-naturality`): use the canonical
  `moduleAbelianUpperStarIso` and exact-functor composition comparison.
- `WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
  (`lem-weil-pbc-module-abelian-derived-direct-image-comparison`): the source
  comparison needed here is underived closed exchange.
- `Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality`
  (`lem-asd-supported-kummer-support-hom-naturality`): the boundary specification
  already records the required Ext equation.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
  (`lem-asd-etale-finite-twist-pullback`): the supplied transport's normalization
  equations suffice, including the roots component.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
  (`prop-weil-pbc-inverse-image-modules-exact`): the exact instances needed
  for `mapExactFunctor` are already available from the scalar interfaces.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
  (`lem-kun-inverse-image-monoidal`): no derived tensor comparison is used.
- `Sheaf.AlgebraicGeometry.PullbackConstantModule`
  (`lem-kun-pullback-constant`): use the underived canonical constant-sheaf
  isomorphism, with its adjunction-unit normalization.

These are removals from this item's direct route, not withdrawals of modules.
Some remain transitive dependencies, and the Cartier geometry remains required
by the new node. No existing module or declaration is deleted.

## Where the brief, the DAG or earlier work was wrong

`relative_extension_pullback` and `relativeExtensionExchange_isIso` in
`RelativeExtensionCohomologyNormalization` require an etale base morphism.
They do not directly apply to the arbitrary Cartier-preserving base morphism
in this item. The integral exchange is nevertheless invertible here by finite
closed base change; the proof establishes that instance directly.

The remaining arbitrary-base geometric pole-extension square has no matching
existing declaration found by the recorded searches. The new node isolates
precisely that part. Its edge cases include empty support and empty base;
its argument uses regularity of both Cartier ideals, not flatness. The proved
coefficient calculation also allows the zero ring and exponent one, as the
original statement requires. No statement is disputed or weakened, and the
unit's Cartier/Kummer route is retained.

The Ext composition-comparison declaration is used from the adopted source
module `WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension`.
Its DAG attachment names the existing Sheaf twin
`Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison`; these files have
the same public theorem name and statement. This delivery does not change
either existing module or the other node's attachment.

## New nodes

`lem-asd-cartier-pole-boundary-pullback`, implemented in
`Sheaf.AlgebraicGeometry.CartierPoleBoundaryPullback`, states the integral
Ext-degree-one square. Its source is the Cartier pair and complementary
trivialization argument in the current blueprint's
`lem-amb-cartier-kummer-map.proof.md`. Its proof plan identifies Cartier duals
and frames, transports the relative integral extension, and uses uniqueness
of the normalized pole class. The node records three kinds of searches and
the complete Lean signature. No change record is necessary because no
existing statement or definition changes.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
