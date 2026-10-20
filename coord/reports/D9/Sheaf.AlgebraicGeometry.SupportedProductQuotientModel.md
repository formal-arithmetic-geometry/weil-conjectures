## What changed

Completed `lean/Sheaf/AlgebraicGeometry/SupportedProductQuotientModel.lean`.
The ordinary comparison comes from the tensor cokernel universal property and
open/closed restriction conservativity, avoiding free presentations. The unbounded
comparison uses the source flat-preserving-functor resolution theorem. Counit
compatibility follows by transport of adjunctions and localization extensionality.
All theorem signatures and the Challenge targets are unchanged.

Refactored the canonical localization construction to avoid repeated expansion,
with two generic public natural transformations and irreducible descended maps.
This fixes the full-file kernel-check timeout without increasing its limit or
splitting the delivered module. Change record:
`coord/changes/D9-supported-product-quotient-localization.md`.
The existing node now records the implemented route and the additional definitions.
No downstream module needs adaptation. The unchanged direct consumer
`Sheaf.AlgebraicGeometry.SupportSiteComparison` compiled unchanged against this packet in 11.8 seconds; the item compiled
in 33.1 seconds in the same ordered run. The delivery dry-run compile is also
required and is being checked separately.

## Proved and sorry left

Closed all seven original holes (each attached to
`lem-pur-supported-product-quotient-model`):

- `AlgebraicGeometry.Etale.supportQuotientOrdinary_existsUnique`
- `AlgebraicGeometry.Etale.supportQuotientLocalization_naturality`
- `AlgebraicGeometry.Etale.supportQuotientLocalization_isIso`
- `AlgebraicGeometry.ProEtale.supportQuotientOrdinary_existsUnique`
- `AlgebraicGeometry.ProEtale.supportQuotientLocalization_naturality`
- `AlgebraicGeometry.ProEtale.supportQuotientLocalization_isIso`
- `AlgebraicGeometry.supported_product_quotient_model`

Actual remaining hole count in the item: **0**. Added holes: **0**.
Split-off statements: **0**. All private helpers are proved. The proof may use
existing library declarations still containing sorry, as authorized by stage 3;
none is introduced by this delivery.

## No longer needed

Removed direct proof imports:

- `Sheaf.SixFunctors.IntrinsicDerivedTensor`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.SixFunctors.OpenClosed.Exact`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.AlgebraicGeometry.SupportedExteriorProduct`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

These are removed as direct imports, not a claim that every source module has
become unreachable through the retained public statement imports. In particular
some source tensor/adjunction modules remain transitively available.

Removed planned proof dependencies:

- `def-weil-finite-type-morphism`
- `def-weil-pbc-constant-sheaf`
- `def-weil-proper-morphism`
- `det-sf-open-closed-sequence-ring-sheaf`
- `lem-pc-kflat-resolution`
- `lem-weil-pbc-adjunction-of-natural-bijection`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-open-closed-short-exact`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-ringed-pullback-preserves-kflat`
- `lem-weil-pbc-site-module-presheaf-sheafification-exact`

The ring-sheaf short exact sequence and rank-one/free-presentation extension are
replaced by tensoring the actual cokernel and detecting isomorphisms on the two
restrictions. The ringed-topos K-flat resolution/pullback path is replaced by the
existing coefficient flat-resolution and flat-preserving-functor APIs. Separate
K-injective Hom calculations, preservation of K-injectives and construction of an
adjunction from a new Hom bijection are replaced by counit transport for the
already specified derived adjunction. The existing generic derived-adjunction API
still uses its K-injective-resolution hypotheses.

Withdrawn obsolete top-level tool approvals (remaining entries keep their order):

- `det-sf-open-closed-sequence-ring-sheaf`
- `lem-pc-kflat-resolution`
- `lem-weil-pbc-ringed-pullback-preserves-kflat`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-adjunction-of-natural-bijection`

The blueprint UNIT realization has no assigned statement or proof-step nodes
bypassed by this change. No parent statement is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically reasonable but longer than the available
source-library route: arbitrary coefficient modules need no free-presentation
argument, and the available categorical flat-resolution API handles the unbounded
comparison without the ringed-site detour. The original localization-component
representation also expanded too much during kernel checking; the refactoring in
the change record keeps the same maps and makes the complete module compile under
the fixed limit. No false statement or disputed target was found. The empty support,
full support, zero coefficient ring and unbounded/nonflat coefficient cases are
covered without adding hypotheses.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
