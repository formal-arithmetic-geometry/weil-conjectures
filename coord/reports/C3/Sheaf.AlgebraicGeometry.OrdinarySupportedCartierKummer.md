## What changed

Restore the B3 proof of `ordinary_supported_kummer` and its proof dependencies.
The proof assembles the unique supported Cartier boundary, normalized finite twist
transport, the Chern realization, and the pullback and scalar compatibility lemmas.
The generic exact single-object comparison is included, together with the proved
unit-forgetting and Chern-realization modules. The unit-forgetting proof is adapted
to unfold the generic composite and the original concrete unit directly. The two
remaining compatibility lemmas are isolated as named split nodes. The existing scalar interface is retained.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.ordinary_supported_kummer`.
The item module and the derived-unit, unit-forgetting, Chern-realization, and generic
single-unit comparison declarations contain no `sorry`.

The delivery adds these two strictly separate holes:

- `AlgebraicGeometry.Etale.supported_kummer_boundary_pullback`
  (`lem-asd-supported-kummer-boundary-pullback`), the normalized Cartier pullback Ext equation.
- `AlgebraicGeometry.Etale.supported_kummer_boundary_scalar`
  (`lem-asd-supported-kummer-boundary-scalar`), the normalized coefficient-extension square.

## No longer needed

The proof does not need these former direct imports of the item (they remain reachable
through the retained compatibility modules where required):

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.AlgebraicGeometry.ClosedSupportHom`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.AlgebraicGeometry.PullbackConstantModule`
- `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`
- `Sheaf.AlgebraicGeometry.SupportedKummerCartierPullback`
- `Sheaf.AlgebraicGeometry.SupportedKummerScalarSource`
- `Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget`
- `WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`
- `WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.SixFunctors.OpenClosed.Exact`

No source declaration is withdrawn. The route keeps the unit's derived-single comparison
and the blueprint's boundary-existence step.

## Where the brief, the DAG or earlier work was wrong

The current item has one hole after removal of the earlier B3 proof packet. The
historical B3 packet already separated the single-unit, Chern, pullback and scalar
results. Its node records and source modules are restored without replacing
these nodes by new copies of the whole existence theorem. This is a decomposition:
one upper hole is closed and two compatibility holes are restored; it is not a net
hole reduction or an axiom-free proof of the item. The unique-boundary theorem's
existing proof remains intact.

The current `OrdinarySupportedKummerScalar` uses
`SheafExactDegreeZero.scalarUniversal`. That implementation is preserved verbatim.
The historical packet's edits to the system, boundary, and scalar definitions are
omitted. No existing definition, public import, target, or source-library signature
changes. The restored generic definition is the explicit derived-unit composite;
it contains no holes and selects no new data.

Validation: all thirteen sandbox modules compile together. The item takes 45.2 s;
`SupportedDerivedUnitForget` takes 37.3 s. The unchanged direct consumers
`ProjectiveLineDiagonalIntegrals` (24.4 s) and `FiniteP1DiagonalAlpha` (17.2 s), and
`OrdinaryFiniteClassComparison` (42.1 s), were included in this check and then removed
from the packet. No consumer adaptation is needed. Preflight requested a record for
the local options and instance attributes in the item module; it is provided in
`coord/changes/C3-supported-cartier-proof-context.md`. Those commands export no
instances and change no existing definition or public signature.

## New nodes

The following six nodes and source modules are restored from the removed B3 packet:

- `def-asd-derived-single-unit`: the explicit full derived-unit composite.
- `lem-asd-derived-single-unit-exact`: the proved comparison with the ordinary unit.
- `lem-asd-supported-derived-unit-forget`: the proved integral-generator equation,
  adapted here to the unchanged concrete unit definition.
- `lem-asd-supported-kummer-chern-realization`: the proved Chern equation from the
  extension's lifting torsor.
- `lem-asd-supported-kummer-boundary-pullback`: the remaining pullback Ext equation.
- `lem-asd-supported-kummer-boundary-scalar`: the remaining scalar compatibility.

Each records its source, proof in words, searches, and Lean attachment. The item's
existing node now follows the actual assembly. No existing node statement is changed.

The local command context is recorded in
`coord/changes/C3-supported-cartier-proof-context.md`.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
