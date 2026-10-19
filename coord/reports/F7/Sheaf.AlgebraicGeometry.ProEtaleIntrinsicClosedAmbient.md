## What changed

Proved `AlgebraicGeometry.Scheme.sfIntrinsicClosedAmbientAdjunction` from the existing
arbitrary-ring-sheaf closed-support interface
`AlgebraicGeometry.Scheme.proEtale_ringed_closed_kernel_adjoint`.
The statement and its public imports are unchanged.

Private constructions identify direct image after transport along the canonical coefficient
isomorphism, identify inverse images by uniqueness of adjoints, and compare the natural
unit kernels. The support comparison then transports the ordinary sheaf adjunction.
The upstream exact-left-adjoint derived adjunction and exact-functor right-derived
comparison give precisely the requested adjunction of unbounded right derived functors.

The coefficient-transport equivalence has an explicit result type to keep elaboration from
unfolding the construction of the inverse-image ring. The direct-image comparison uses
Mathlib's pushforward-composition interface. The existing node's proof and dependencies
were updated to describe this route. No existing declaration's signature changed.
The preflight-required record for the file-local transparency registration is
`coord/changes/ProEtaleIntrinsicClosedAmbientLocalTransparency.md`; it documents why no
consumer adaptation or target rereview is needed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.sfIntrinsicClosedAmbientAdjunction`
(`lem-exc-proetale-closed-support`), one of one original holes.
Holes added: zero. Sorries left in the delivered Lean module: zero.
The existing ringed-support theorem remains an imported obligation, not a newly added hole.
The complete module compiled without errors or warnings through `lcompile.py` in 21.9 seconds on this resumed run.
The pointwise-kernel comparison is proved first for general abelian categories, avoiding
unnecessary unfolding of the concrete coefficient adjunction during elaboration.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`, replaced by the stronger existing
  `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint` interface.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.

The proof does not separately invoke `lem-exc-proetale-closed-exact`,
`lem-exc-proetale-closed-fully-faithful`, or `lem-exc-proetale-closed-essential-image`:
the ringed closed-kernel adjunction already supplies their needed consequences.
It does not separately invoke `lem-weil-proetale-weakly-etale-localization` or
`prop-weil-pbc-proetale-constant-exact`; localization is internal to the ringed theorem
and the canonical coefficient isomorphisms are the existing support definitions.
The direct dependencies `def-weil-proetale-inverse-image`,
`def-weil-proetale-module-direct-image`, `def-weil-pbc-proetale-site`, and
`def-weil-abstract-derived-category` remain available through the statement interfaces,
but need no separate proof step. Removed obsolete top-level tool approvals for
`lem-exc-proetale-closed-fully-faithful`, `prop-weil-pbc-proetale-constant-exact`,
and `lem-weil-pbc-kinjective-total-derived`.

The existing `lem-weil-pbc-kinjective-total-derived` statement is not invoked: the upstream
`mapDerivedCategoryRightDerivedAdjunction` supplies the complete unbounded construction.
The explicit resolution theorem `prop-pur-kinjective-resolutions-exist` is also unnecessary:
the published operations already provide the K-injective-resolution instance. Their modules
need no direct import here.

These are removals of direct dependencies. No claim is made that modules still reached
transitively through other theorem interfaces become globally unreachable.
The unit's own statement and steps are preserved; no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The older plan repeated ringed open-closed localization and the K-injective derived
adjunction argument. The already stated arbitrary-ring closed-kernel interface and
upstream generic derived-adjunction construction make that repetition unnecessary.
No mathematical error or statement correction was needed. The first resumed delivery attempt
encountered a 600-second temporary-checkout timeout; the retry compiled and reached
preflight, which required a change record for the file-local transparency attribute. That
record is now included. The imported ringed theorem
is used as a coefficient-independent tool for the same closed-support argument.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
