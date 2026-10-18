## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_sheaves`
in `Sheaf.Paper.FormalClosedSupportSheaves`, keeping its signature and both kernel
functor definitions unchanged. Six private proved helpers transfer the abelian
closed-support theorem to internal modules, prove exactness of closed direct image,
and construct the adjunction for the actual functor-category kernel in the statement.
The final proof obtains limit preservation, injectivity, and unbounded K-injectivity
from this adjunction and the existing generic results.

Added proof-only imports of `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport`,
`Sheaf.Paper.ProfinitePointPullback`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
All public imports, existing definitions, statements, visibility and docstrings stay
unchanged. Updated only proof/proof_deps/proof_origin of
`det-lem-formal-closed-support-sheaves` to describe the compiled argument.
The unit's kernel, adjunction, and exact-left-adjoint route is preserved.
Change record: `coord/changes/W6-formal-closed-support-proof-scopes.md`
records the local open commands and private proof elaboration scopes requested
by the static checker; no downstream adaptation is required.

Validation: single-file server compilation passed without warnings (14.3 seconds).
The abelian-closed-support import-direction query permits the import. The two
transitive consumers are `Sheaf.Paper.FormalClosedSupportDerived` and
`Sheaf.SixFunctors.IntegralRestrictionClosed`; their declarations use the unchanged
kernel functor API, so neither requires adaptation. Empty closed/open components
are covered by the same zero-object arguments without a nonemptiness hypothesis.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_sheaves`
(node `det-lem-formal-closed-support-sheaves`).
Added 0 holes; split off 0 statements. No `sorry` remains in this delivery.
All six private helpers are completely proved. No axioms or data definitions added.

## No longer needed

Removed these direct proof-only imports:

- `Mathlib.RingTheory.Noetherian.Defs` (Noetherian consequences come through the
  retained algebraic-geometric imports).
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
  (`lem-weil-pbc-proetale-ringed-open-closed`): the proved abelian supported-unit
  theorem transfers directly to internal modules; exact closed direct image is
  proved by joint detection of zero cokernels.
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
  (`lem-weil-pbc-proetale-immersion-limit-preservation`): the actual internal-module
  inverse images already have the required exactness instances in UpperLowerStar.Defs.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`
  (`lem-weil-pbc-proetale-ringed-open-comparison`): use the existing abelian open
  adjunction triple and lift its fully faithful extension-by-zero functor.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
  (`def-weil-proetale-inverse-image`): no declaration of this interface is referenced
  directly; the proof uses the existing abelian inverse/direct-image framework.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit`
  (`lem-weil-pbc-proetale-ringed-closed-counit`): transfer the abelian counit instead.
- `Sheaf.CategoryTheory.RingedSiteModules`
  (`def-weil-sheaf-of-modules-category`): the actual categories are internal modules
  over condensedRingObj, already supplied by the unchanged statement imports.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`: its needed generic
  declarations are already available through the retained imports; the corresponding
  node `lem-sp-exact-functor-preserves-homology` is still used.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
  (`lem-weil-pbc-termwise-adjunction-homotopy`): the proved generic K-injective
  transfer theorem uses termwise adjunction and transports null homotopies directly.

Also removed the explicit proof dependency `def-weil-pbc-noetherian-ring`:
finite-type-over-Noetherian supplies the required scheme instances directly.
Pruned the five obsolete top-level `tool_uses` approvals for ringed open/closed,
immersion limit preservation, ringed open comparison, ringed closed counit, and
homotopy-category adjunction, retaining finite-type-over-Noetherian in order.

These are dependencies pruned from this item's route, not claims that other parents
cannot need them or that all their modules disappear from the global import closure.
The theorem still uses `lem-weil-pbc-finite-type-over-noetherian`,
`pqf-def-locnoeth`, the coefficient/module-operation nodes, generic limit,
exact-functor and injective preservation, and the K-injective definition.

## Where the brief, the DAG or earlier work was wrong

No statement was disputed or changed. The original proof plan unnecessarily routed
internal module objects through a separate ring-sheaf module presentation. The existing
proved abelian supported-unit theorem plus scalar-change equivalences suffices, so no
new comparison or localization obligation is needed. The specified functor is a
functor-category kernel, so the proof explicitly uses evaluation's kernel comparison
rather than silently replacing it with a pointwise kernel functor.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
