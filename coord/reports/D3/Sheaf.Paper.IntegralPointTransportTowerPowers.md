## What changed

Constructed `IntegralPointTransportTower.ordinaryTransport_existsUnique` from the
completed-linear restriction maps and the existing uniquely normalized
`restrictionComparison`. The component formula is proved through the actual
restriction-of-scalars casts, and uniqueness is proved on every section.
Moved the proved completed-linear restriction construction into
`Sheaf.Paper.PointIntegralRestrictionNatural`, which proves its unique natural
sectionwise specification. The tower proof and the existing chain-level
`integralSigma_existsUnique` proof now use that specification. This prevents
repeated unfolding of the completed coefficient action. The proved termwise
transformation, its component formula, and the section-cast identity are shared
as private helpers in the same new module. Existing public signatures
and definitions are unchanged. The finite-evaluation proof now cancels its two
equality maps explicitly, with the inverse-evaluation helper locally irreducible.

Proved `IntegralPointTransportTower.sectionsLimitComparison_existsUnique` using
invertibility of the canonical exact-product derived-limit mate in the new module
`Sheaf.Paper.ExactProductTowerLimitMate`, whose general theorem is also proved.
The proof constructs the natural isomorphism by whiskering that mate, proves the prescribed entire-counit equation,
and proves uniqueness using the adjunction hom-set bijection. It does not infer
an equality from individual derived evaluations.

The comparison declarations are factored into
`Sheaf.Paper.IntegralPointTransportComparisons`, publicly reexported by the item.
Their names, public signatures and definitions are preserved. This is a compilation
split after profiling and improving coefficient unfolding; it leaves the original
`restrictionComparison_existsUnique` hole under the same name and statement, with
its own node. No unproved assertion is introduced by moving it.

Verification: `lcompile.py --all` accepted all four delivery modules and the
three unchanged direct importers `CompactSupportSystemRealizationNormalization`,
`ConstantExtensionReturnData`, and `LocalNormalizationStrictRealization`, with
exit code zero and no diagnostics. The unchanged verification copies were removed
from the packet. No consumer adaptation was necessary.

## Proved and sorry left

The starting module contained four holes. Closed:

- `WeilConjectures.IntegralPointTransportTower.ordinaryTransport_existsUnique`.
- `WeilConjectures.IntegralPointTransportTower.sectionsLimitComparison_existsUnique`
  (using the proved general derived-limit mate lemma).

Two original holes remain unchanged, both attached to
`lem-trf-integral-point-transport-tower-powers` or its newly explicit restriction
comparison subnode:

- `WeilConjectures.IntegralPointTransportTower.restrictionComparison_existsUnique`,
  now in `IntegralPointTransportComparisons`, node
  `lem-trf-integral-point-restriction-comparison` (the unchanged original hole).
- `WeilConjectures.integralPointTransportTowerPowers`, node
  `lem-trf-integral-point-transport-tower-powers`.

Added no holes. The new theorems
`CategoryTheory.exactProductTowerLimitMate_isIso` and
`WeilConjectures.PointIntegralRestrictionNatural.existsUnique` are proved, as are
all their private helpers. Thus two original holes are closed, none is split off, and two original
holes remain in this packet, for a net decrease of two. The existing proof of
`inverseLimitComparison_existsUnique` is retained and is not counted as new work.

## No longer needed

Removed the item’s direct proof import of
`Sheaf.Paper.PointAutomorphismRestrictionNatural`: it is now used by the new
linear-restriction helper module. Its node remains needed through that module.
No existing node or module is withdrawn. The comparison-only proof imports of
`RingedSiteGrothendieckCoefficientUniverse`, `PointProEtaleSectionsExact`,
`MapDerivedCategoryMate`, `ModuleCat.AB`, `IsomorphismScalarQuotientChainSquares`
and `ExactProductTowerLimitMate` moved with those declarations. The item no longer
needs its direct `Mathlib.CategoryTheory.Adjunction.Mates` import. The new
point-restriction module uses a local proved cast lemma and imports the comparison
models directly, avoiding an unused import of the quotient-pullback proof module. The new mate proof only needs
exact countable products in the target module category, so the provisional
`Sheaf.AlgebraicGeometry.ProEtaleProductsExact` import and its source-category
exact-product instance were removed. From the new helper module, removed redundant
explicit imports of `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
`Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`, and
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`; the remaining public imports
already provide them. The dependencies of the
remaining whole-system Laws proof are retained. The ordinary transport
construction uses the existing restriction comparison rather than duplicating
its tensor-unit construction. The sections comparison uses only the invertibility
part of the normalized Roos argument; its counit equation and uniqueness are
proved directly by adjunction.

## Where the brief, the DAG or earlier work was wrong

No target statement, existing theorem signature, or public definition was repaired.
The current source already contains E3's inverse-limit comparison proof, so the
starting count is four holes, not five. The existing helper declarations for
completed-linear restriction occurred after ordinary transport; they are now
encapsulated in the natural-restriction helper module. The existing proof plan's assertion that exact sections
commute with total limit requires identification with the specified mate, rather
than an arbitrary isomorphism between the endpoint functors. The new lemma
proves that precise invertibility assertion. Its private normalized Roos comparison
allows independent universes for the derived module and derived tower categories;
the existing comparison ties those presentations to one universe. No shared
interface was changed to obtain this flexibility.

## New nodes

`lem-trf-exact-product-tower-limit-mate`, attached to
`CategoryTheory.exactProductTowerLimitMate_isIso`, isolates invertibility of the
actual constant-tower mate for an exact product-preserving functor between
Grothendieck abelian categories with exact countable products in the target. It is the invertibility part
of the existing prerequisite's step 5. The natural-language proof follows the
normalized Roos computation and includes its whole-counit normalization. The
source is the local Stacks `sites-cohomology.tex`, section-derived-limits; the
zero and constant tower cases give the identity comparison. The proved lemma omits
coefficient systems, restriction of scalars, and the existence/uniqueness
specification of the parent statement, which are handled in the parent proof.


`lem-trf-point-integral-restriction-natural`, attached to
`WeilConjectures.PointIntegralRestrictionNatural.existsUnique`, records the unique
natural restriction map on completed integral point sections. Its scalar proof is
the already proved completed coefficient square; its naturality is ordinary
module-morphism naturality, and its uniqueness follows on every section. The new
module isolates this checked construction for reuse on towers and complexes,
without introducing a new hole or changing any completed coefficient definition.


`lem-trf-integral-point-restriction-comparison` attaches the unchanged original
`restrictionComparison_existsUnique` declaration to the new comparison module.
It records the original finite tensor-unit/completed-scalar compatibility argument.
This is preservation of an existing hole during the compilation split, not an
additional split-off hole or an asserted proof of that subclaim.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
