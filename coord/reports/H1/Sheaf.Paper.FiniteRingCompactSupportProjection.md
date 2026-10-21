## What changed

Proved `AlgebraicGeometry.Scheme.isIso_finiteRingCompactSupportProjection` without
changing its signature or the canonical projection map. The proof implements the node's
six-step route: descend bounded intrinsically constructible inputs to the etale site;
commute exact extension by zero with comparison; apply the etale proper projection formula;
use the unbounded direct-image comparison on both the origin and its derived tensor;
identify the canonical counit mate; compose with the open projection and pullback
composition isomorphisms. Naturality transports invertibility to the given inputs.
No finite Tor amplitude or DVR presentation is introduced.

The existing fixed-coefficient tensor/mate compatibility proves the comparison step,
avoiding the general ringed-topos wrappers. Private categorical lemmas prove the changes
of adjunction and exact-derived presentation explicitly. The unbounded comparison is used
on every input, including the tensor that can be unbounded below.

In `FiniteRingCompactSupportProjectionMap`, named proofs of thirteen existing instances
share the coefficient and realization arguments with its consumer. All aliases are proved
by instance synthesis and registered only locally. The canonical map definition is retained
verbatim. Explicit coefficient types in the final proof avoid repeated kernel conversions
through a local type alias. The complete theorem compiled in 13.3 seconds with its kernel
check passing; the final packet is checked again by `lcompile.py --all` and delivery.
The performance repair and consumer inventory are in
`coord/changes/H1-finite-projection-instance-sharing.md`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.isIso_finiteRingCompactSupportProjection` (1 of 1).
No holes remain in either delivered module. No holes were added or split off; every
private helper and every new instance alias is proved. The map module has zero holes
before and after this repair. This is a proof from existing project declarations,
including the intended unbounded comparison dependency, rather than a claim to have
closed all holes in their transitive dependency closure.

## No longer needed

The proof no longer needs these three direct planned dependencies:

- `lem-weil-pbc-comparison-pullback`: use the proved fixed-coefficient pullback square.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: use its proved fixed-coefficient
  unbounded tensor comparison.
- `lem-weil-pbc-ringed-exchange-tensor-coherence`: use the proved fixed-coefficient
  projection/mate compatibility and the explicit adjunction-transport calculation.

They were removed from this node's proof dependencies and top-level tool-use list.
This does not withdraw any adopted source declaration or assert that these modules are
unused by all other targets. No Lean module is withdrawn in this packet.

Removed direct imports are listed completely below. The repeated public imports in the
theorem module remain publicly available through its map import; their public closure
is unchanged. The exact open comparison is imported from the existing source comparison
module; the proper torsion component wrapper is replaced by the source theorem asserting
invertibility of the full etale projection transformation. Unused private imports in
the map module are removed as well.

From `FiniteRingCompactSupportProjection`:

- `public import Sheaf.Paper.FiniteFieldFiber`
- `public import Mathlib.AlgebraicGeometry.OpenImmersion`
- `public import Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `public import Sheaf.SixFunctors.IntrinsicDerivedTensor`
- `public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`
- `public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`
- `public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection`
- `public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat`
- `import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`
- `import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `import Sheaf.Paper.RingedExchangeTensorCoherence`

From `FiniteRingCompactSupportProjectionMap`:

- `import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`
- `import Mathlib.GroupTheory.Torsion`
- `import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `import Sheaf.Paper.RingedExchangeTensorCoherence`
- `import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`

The earlier attempt's two unsent split modules/nodes are not used or submitted. They
were moved to scratch storage; neither exists in the current source, so no deletion or
withdrawal request is made for them. A duplicate import of
`Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison` from the working draft was also removed.

## Where the brief, the DAG or earlier work was wrong

The mathematical six-step plan is sound. Its general ringed-topos interfaces are more
than the fixed-coefficient argument needs: the adopted library already proves the exact
canonical tensor/mate compatibility required here. No new mathematical node is needed.

The earlier report's claimed missing transport interface was not an obstruction.
The compactification component equation and functorial preservation of isomorphisms
close the transport. The remaining difficulty was normalization of inferred instance
proofs and a local coefficient-type alias, repaired by instance sharing and explicit types.
The theorem, its hypotheses, its universes, and the specified canonical map are preserved.
The updated DAG records the actual route, and its existing map node also attaches the
proved instance aliases. No source-library file or declaration is changed.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
