## What changed

Proved `AlgebraicGeometry.ProEtale.finiteProper_classical_neighborhood_vanishing` with
its signature unchanged. Finite-ring sections are torsion; the proper torsion bound
and coefficient-forgetting comparison give the etale module bound. The proved source
bounded-below/unbounded compatibility and the canonical comparison mate transfer it
to the specified total pro-etale direct image.

For global sections, a faithfully flat ind-etale w-contractible affine cover of V
splits by the stated weak-contractibility hypothesis over Y. Lifting on that cover
and restricting along the splitting proves weak contractibility of the terminal object
of V_proet. Module evaluation there is exact. The terminal-object section formula,
total-derived composition, and exact evaluation prove the second bound. All helpers
are private and proved in this module. No other Lean module changes.

Updated the item's proof, proof dependencies and proof origin to this argument.
Preserved all existing public imports, hence the importer-visible interface.
Added private proof imports for source derived compatibility/composition, torsion
characterization, and w-contractible affine evaluation.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.finiteProper_classical_neighborhood_vanishing`
(node `lem-sfb-finite-proper-classical-neighborhood-vanishing`).

Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
The proof uses existing library declarations as allowed by stage 3; this does not
claim that all their transitive proof dependencies are sorry-free.

Checked the empty-scheme, zero-ring and e=0 cases: the contractible cover and splitting
arguments impose no nonempty assumptions, and card(A) is positive even for the zero
ring. The proof uses no invertibility of the finite-ring exponent, no Noetherianity,
no constructibility, and no descent of H from X.

## No longer needed

Removed these private proof imports:

- `Sheaf.CategoryTheory.KInjectiveComputes`: the proved source
  `rightDerivedFunctorPlusCompatibility` directly compares the total derived functor.
- `Sheaf.AlgebraicGeometry.ProperHeartContinuitySections`: exactness of fixed-scalar
  module evaluation follows directly from lifting set-valued sections and kernels.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`: a split contractible affine
  cover proves the required terminal-object weak contractibility directly.
- `Sheaf.Paper.FiniteDiscreteCondensedRing` and
  `Sheaf.Paper.FiniteDiscreteSchemeRing`: the statement already uses ordinary fixed
  `ModuleCat A` coefficients and explicitly supplies its etale model.
- `Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`: the source pro-etale-site
  imports already provide the representable sheaves and subcanonical topology.

The proof therefore no longer needs nodes `lem-sp-kinjective-computes`,
`det-proper-heart-continuity-sections`,
`lem-weil-proetale-weakly-etale-localization`,
`lem-weil-pbc-finite-discrete-condensed-ring-constant`, or
`lem-weil-pbc-finite-discrete-scheme-ring-constant`. Removed their obsolete top-level
tool-use approvals from this node. Retained `det-pe-topos-functoriality-site` for the
subcanonical representable-sheaf argument, supplied by existing source instances.
These are proof-route removals; no module or declaration is withdrawn and no claim
is made that other consumers cease needing these nodes.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound but uses unnecessary coefficient-ring and
slice-site bridges for this fixed-ModuleCat statement. The source compatibility
isomorphism and splitting a contractible affine cover give shorter implementations
of those steps while retaining the unit's uniform proper bound and classical transfer.

Initial elaboration searched too long for additivity of coefficient forgetting.
Providing its sectionwise additive instance explicitly resolves that search.
Explicit types for the projection and the derived functors avoid expensive repeated
normalization through identity scheme functors. Remote single-file compilation passes
within the 60-second limit (38.7 seconds with the final profiling check). The final source has
zero sorry tokens, unchanged theorem signature, no diagnostic options, and all lines
at most 100 columns. The node's proof dependencies equal the union of its step uses;
all cited nodes exist. The new source composition import passes the import-cycle check.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
