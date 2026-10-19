## What changed

Proved `AlgebraicGeometry.Scheme.hasFiniteCoefficientProEtaleTorAmplitude_iff_locally`
in `Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal`, with the existing statement,
visibility and `coefficientModelSliceRestriction` definition unchanged. All new helpers
are private and proved in this same module; there are no new modules or public declarations.
The conservative command-scope change record is `coord/changes/ProEtaleTorLocalGlobal-interface.md`.

The forward implication compares the representative Tor test with the localized tensor,
then applies `siteTorIntervalRestriction`, explicitly identifying the two restriction
models using `mapDerivedCategoryFactors`. The representative comparison is proved using
flat-term K-flat resolutions, acyclic K-flat cones and `wfSiteDerivedTensor_first`.

The converse selects finitely many original covering members over a finite affine open
cover, takes a common interval, restricts every global representative test to those
members, and detects zero homology by the sheaf uniqueness axiom. The finite selection
is proved from Mathlib's pro-etale covering API and transported through AsSmall. It retains
original local members, so no interval needs transporting to a further affine refinement.
The inserted zero in the bounds and the empty-cover sheaf argument handle the empty scheme.

Validation: the retained consolidated module compiled in 24.3 seconds with no diagnostics
against the published library and the sandbox overlay. The resumed required dry run passed at commit `048615a596`: the delivery compiles and
passes preflight against the current sources, with CODEX review required for the node
and command-scope changes. Both original public imports remain
unchanged; the command-scope record documents the inserted private helper section.

The node's proof and dependencies now describe this implemented argument. The unit's
integral-model route is unchanged. The following are generic tools used for the explicit
tensor-model glue: `lem-pc-kflat-resolution`, `lem-pc-kflat-cone-direct-sum`,
`lem-pur-acyclic-kflat-tensor-arbitrary`, `lem-sfb-ringed-site-restriction-kflat`, and
`lem-weil-pbc-slice-tensor-natural`. The first-variable tensor calculation is the generic
ringed-site part of `def-wf-tensor-product`; no Frobenius or Weil-pair assertion is used.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.hasFiniteCoefficientProEtaleTorAmplitude_iff_locally`
(`lem-sfb-proetale-tor-local-global`). Added 0 holes. No `sorry` remains in the delivery.
This proves the item from the existing declared dependencies; some of those dependencies
still contain their own previously existing holes. No split-off proof item is added.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The unused exploratory import `Mathlib.CategoryTheory.Sites.LocalProperties` was also
removed before delivery.

The original parent proof dependencies
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-site-derived-tensor-descent`, and
`lem-pur-site-restriction-module-adjunction-exact` are no longer direct steps of this proof.
The first two obsolete parent tool-use approvals are removed. Exactness now uses the
existing `ringedOverFunctor_exactGeneral` interface; the local-to-global calculation uses
actual representative restriction and the natural ordinary tensor comparison. The
recorded representative restriction is still used, exposed through SiteTorIntervalRestriction;
its separate direct import was redundant. Site covering operations are supplied by Mathlib.
Some removed modules remain indirect dependencies of the existing declarations used here;
no whole-module pruning beyond these direct imports is claimed.

The earlier sandbox's directional split files and new comparison/cover helper files were
never delivered. Their proved contents have been consolidated into private helpers; none
is part of this delivery and there are no new nodes.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report described two unproved directional splits. It was stale:
the actual proof now closes both directions without adding holes. The plan's affine
refinement step need not transfer Tor bounds to refined affine objects: retaining the
original members through which the refinements factor gives a finite covering already.
This avoids the extra relocalization glue without changing the hypothesis or conclusion.

The compile initially failed because the two syntactically different slice coefficient
rings needed the same standard derived-category instance. After supplying it, the
remaining mismatch was the orientation of the comparison isomorphism. Both have been
repaired and the individual helper modules compiled before consolidation. The retained
change record incorrectly claimed public-import removals; the resumed session corrected
it against the current source. No public import was removed.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
