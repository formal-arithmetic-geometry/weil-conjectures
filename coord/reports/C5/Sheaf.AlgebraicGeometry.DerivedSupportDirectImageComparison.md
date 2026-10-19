## What changed

Proved `AlgebraicGeometry.ProEtale.derivedSupportDirectImageComparison` in
`Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison` by constructing every
field of the original package. The proof uses the source library's canonical
K-injective composition isomorphism, exact open-restriction/extension-by-zero
adjunctions, kernel lifts, and the defining factorization of the canonical derived
adjunction unit. It constructs all maps directly; it chooses no arbitrary witness
from an unproved existence statement.

Long concrete equations are named by `supportCompositionNormalization` and
`supportRestrictionSquare`. The affected fields unfold to their original equations,
with all original binders and hypotheses retained. The specified ordinary and derived
open-pullback comparisons are factored through abstract coefficient categories, and
inferred functor types are annotated. These changes prevent repeated expansion of
chosen ModuleCat kernels and derived-category constructions. The canonical derived
adjunction is now a typed definition with its original body. The two identity
comparisons keep their identity components and use `Iso.refl`.

The node's proof, proof dependencies, proof origin, and declaration list follow the
implemented route. No target statement changes. The change record is
`coord/changes/derived-support-direct-image-comparison-normalization.md`.
`tools/downstream.py --uses` finds no consumer of a modified public definition;
the similarly named `SupportedBottomEdge.kernel_normalization` is unrelated.
Direct importers are `SupportSiteComparison` (S2) and `SupportedBottomGluing` (K4);
neither needs a source adaptation.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.derivedSupportDirectImageComparison`
(node `lem-pur-derived-support-comparison-direct-image`).

Holes closed: 1 of 1. Holes added: 0. Split off: 0. No `sorry` remains in the
item or is added elsewhere. Every private helper is proved; the new public helpers
are concrete definitions of equations or of the specified canonical maps.

Validation: the complete item compiled without warnings in 21.0 seconds. Both
direct consumers compile unchanged against the delivered item: `SupportSiteComparison`
(34.2 seconds) and `SupportedBottomGluing` (38.7 seconds). The latter initially
hit the limit in the batch check, then passed on its own against the same compiled
overlay; its unchanged published-dependency baseline also passes (46.7 seconds).

## No longer needed

Removed these ten proof imports, together with their use as proof dependencies:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
  (`prop-pur-kinjective-resolutions-exist`): source Grothendieck-abelian resolution
  instances suffice directly for fixed-coefficient sheaves.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
  (`lem-weil-pbc-site-pullback-abelian-exact`): comparison exactness is already an
  instance on the source comparison inverse image.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
  (`lem-weil-pbc-kinjective-total-derived`): use the existing canonical unbounded
  `rightDerivedFunctor`, its composition isomorphism, and its unit factorization.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
  (`lem-weil-pbc-etale-site-localization-open`): no separate site-equivalence argument
  is needed; the source open-restriction APIs provide the required adjunctions.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
  (`lem-weil-proetale-weakly-etale-localization`): the source finite-coefficient open
  restriction and exact extension-by-zero adjunction replace the localization wrapper.
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
  (`lem-sfb-proetale-object-inverse-image-restriction`): use the source canonical
  `upperStarIsoOpenImmersionRestriction` directly.
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`
  (`lem-pur-kinjective-restrict-localized`): the exact extension-by-zero left adjoint
  proves K-injective preservation on each site.
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
  (`lem-pc-derived-adjoint-functors`): the source canonical derived adjunction and
  Mathlib's `derivedη_fac_app` give the required unit equation directly.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
  (`def-weil-pbc-site-comparison-morphism` wrapper): the actual comparison functors,
  adjunction, and exactness are already available from the retained public imports.
- `Sheaf.CategoryTheory.RingedSiteModules`
  (`def-weil-sheaf-of-modules-category` wrapper): no ringed-site module transport is used.

Removed obsolete tool-use entries for the abelian-exactness, total-derived,
pro-etale-localization, pro-etale-object-restriction, localized-K-injective, and
generic-derived-adjunction wrappers. Kept the existing etale restriction and
comparison-pullback approvals. Statement dependencies remain unchanged; an unused
proof wrapper is not a claim that its statement-level notion is unnecessary elsewhere.
The unit's realized statement and step lists are empty, so this route bypasses no
required unit realization. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned ringed-site localization and total-derived wrappers are unnecessary for
this fixed-coefficient source API. Exact open extension by zero gives the required
K-injective preservation immediately. The canonical source derived-adjunction unit
has a defining factorization, so no additional derived-adjunction theorem or choice
of resolution data is needed.

The original fully expanded normalization and restriction expressions caused costly
elaboration of chosen kernels and localization instances. Naming the same equations
and keeping coefficient categories abstract resolves this without changing their
mathematical meaning. There is no statement dispute and no new node.

The sandbox and proof work were retained across provider-error continuations.
The dispatcher refreshed its reference clock (current recorded start
2026-10-19 18:22:29 UTC); no budget metadata was edited. Compiler attempts are
retained under `scratchpad/resume*.log`; no unchanged delivery was retried to wait
out a budget gate.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
