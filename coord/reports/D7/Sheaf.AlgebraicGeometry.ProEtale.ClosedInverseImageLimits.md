## What changed

Proved `AlgebraicGeometry.Scheme.closed_inverseImage_preserves_limits` with its original
signature, universes, visibility and definition `AffineProEt.closedSiteLiftOver` unchanged.
The retained attempt already contained the module-object limit and adjunction argument,
but left canonical unit evaluation as an unproved new module. That module is now fully
proved and folded into private helpers of the item; it is not delivered as a new module.

The canonical evaluation proof splits affine surjective covers using global weak
contractibility and subcanonical Yoneda, transports their sections through the fully
faithful open-chart inclusion, calculates the affine adjunction unit, and globalizes its
actual component by explicit mate equations. The localization calculation follows the
proved helpers of `ProEtaleSpecializationUnitComparison`; it is included locally because
that module's public specialization theorem assumes projectivity of the lift rather
than its closed fibre. The affine evaluation module's proved private set-sheaf helpers
are reused with `import all` and then transported through abelian sheafification.

For all limits, only the abelian clause of
`proEtale_immersion_inverseImage_preservesLimits` is used. This is a generic tool from
another unit implementing the same affine-lift/localization route; it does not restrict
the arbitrary monoid coefficient B to a commutative ring. `Mod.forget` creates limits and
reflects limit cones; `mapModAdjunction` and left-adjoint preservation give all colimits.
The finite assertions follow from these two results. No unit-level route is bypassed.
The DAG proof and direct dependencies now describe this argument. The existing public
import interface is retained; all added imports are proof-only.

Validation: the assembled single file compiled in 9.1 seconds with no errors or warnings.
The named-private-instance revision also compiled in 10.0 seconds; its one long line was
subsequently wrapped to the required width.
On the current resumption (2026-10-19), the retained file compiled against the current
dependency build in 10.7 seconds with no errors or warnings. The theorem signature,
lift construction and public imports were checked against current sources and are
unchanged. The node changes only proof, proof_deps, proof_origin and the permitted
withdrawal of obsolete tool_uses entries; its dependencies equal the union of step uses.
The affine cover argument includes empty covers, and the unit calculations do not assume
nonempty schemes, proper ideals, finite coefficient rings, or commutative B.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.closed_inverseImage_preserves_limits`
(node `det-sf-open-closed-pullback-limits`).
Added 0 holes. No `sorry` remains in the delivered module. All private helpers are proved.
The abandoned retained helper `closed_inverseImage_unit_isIso_on_lift` is now a proved
private helper in this module; there is no split-off theorem or new node.
Existing imported declarations may retain their own upstream proof obligations.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.ProEtaleClosedLocalization`
- `Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.Basic`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`
- `Mathlib.Algebra.Category.ModuleCat.Limits`
- `Mathlib.CategoryTheory.Sites.Limits`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`

The inverse-image definitions remain available through the retained public interface;
the last two imports add no fact used by this proof.

`AffineClosedInverseImageEvaluation` remains a proof import, now `import all`, because
its proved private sheafification-evaluation helpers are used directly.
Added proof imports are `WeilConjectures.CategoryTheory.Monoidal.Mod.Limits`,
`Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`,
`WeilConjectures.CategoryTheory.InverseMateEquivalence`, and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`.
The retained attempt's unpublished `ClosedInverseImageUnitEvaluation` module is eliminated;
it never existed in the shared repository, so no repository deletion is requested.

Removed direct DAG proof dependencies:
- `det-pe-topos-functoriality-inverse-image`
- `lem-exc-closed-localization`
- `lem-weil-pbc-closed-immersion-affine-cover-criterion`
- `lem-weil-pbc-ind-etale-basis-wcontractible-cover`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-proetale-inverse-image-limits-zariski-local`
- `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`

The first is subsumed by the existing monoidal adjunction; the constant-coefficient
localization declaration is replaced by the explicit abelian mate calculation; the
quotient chart is already supplied as a hypothesis; the immersion theorem supplies the
previous sectionwise-limit and globalization argument; the lifted adjunction supplies
colimit preservation without the other module-sheaf encoding. Dependencies still reached
inside the reused theorems are not claimed as globally pruned. Obsolete top-level
`tool_uses` entries for the removed direct dependencies are withdrawn, preserving order.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox was not ready to deliver: it used an unproved unit-evaluation helper
without a node or report. That gap is now proved, with no added holes. The initial DAG
repeated an all-limit argument already available for abelian immersion inverse image.
Its constant-coefficient localization declaration does not directly accept abelian
sheaves, so the proof verifies the canonical localization comparison at that coefficient
category instead of asserting that an arbitrary evaluation isomorphism is the unit.
There is no statement or definition repair, and no forced adaptation of another group.

Change record: `coord/changes/d7-closed-inverse-image-localization-helpers.md`.
The scoped continuity instances are named private declarations; no consumer is adapted.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
