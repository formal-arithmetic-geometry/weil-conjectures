## What changed

Replaced the single hole in `WeilConjectures.point_identity_admissibility` by an explicit
construction of its finite systems and the finite, integral, rational and algebraically
closed admissibility witnesses. All existing signatures and public imports are preserved.
The new private `identityModel` transports the identity adjunction along support
isomorphisms, defines left refinement comparisons as beta_d followed by beta_e inverse,
and defines right comparisons as identities. The unit, counit, refinement and coefficient
mate equations are proved in Lean. All three uniform bounds are zero.

Added `Sheaf.AlgebraicGeometry.IdentityFullCohomologicalDimension` with a proved theorem:
conjugate the existing direct-image equivalence along scheme isomorphisms through the
canonical realization, use exact derived descent and its singleFunctor comparison, then
apply this both to the identity and to every base-changed projection.

Added `Sheaf.Paper.PointIdentitySupportNormalization`. Its exposed definition
`pointIdentitySupportIso` constructs support isomorphisms from the existing proved
`clopenSectionComponent`, its K-injective preservation and section-normalized sheaf
isomorphism, and the canonical exact-precomposition and derived-identity comparisons.
The proved `pointIdentityClopenComparison` exposes just the K-injective and normalized
section clauses, avoiding expensive checking of the full clopen conjunction in the data
definition. Its public proof imports are needed in the exposed data definition. The one remaining
obligation is the canonical LEFT coefficient comparison equation, strictly one part of
step 8 of the original argument. No model, preservation bound, right mate, finite system,
prime invertibility or higher-stage admissibility is assumed by that lemma.

Updated the parent DAG proof and dependencies, and added nodes for both new modules.
No existing statement or definition is repaired; no change record is required.

## Proved and sorry left

Closed the original hole `WeilConjectures.point_identity_admissibility` (1 of 1).
Added one hole: `WeilConjectures.point_identity_support_normalization`, node
`lem-sf-point-identity-support-normalization`. This is a decomposition, with net hole
change zero, not a completed sorry-free proof of admissibility. No holes remain in the
item module or in `IdentityFullCohomologicalDimension`.

Proved `AlgebraicGeometry.Scheme.sfFullCohomologicalDimension_identity` and constructed
`WeilConjectures.pointIdentitySupportIso`. The private adjunction and mate helpers have
complete proofs. Final `lcompile.py --all` passed without warnings: FullCD 4.0 s,
support normalization 48.1 s, admissibility 47.7 s, all within the 60 s limit.
The profiler options were removed before this final check.

## No longer needed

Removed proof imports:

- `Sheaf.Paper.FiniteCoefficientPoint`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.CategoryTheory.Adjunction.Unique`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint`.
- `Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension`.
- `Sheaf.Paper.FiniteDirectImageComposition`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`.
- `Sheaf.Paper.SfCommonStageDirectImage`.
- `Sheaf.Paper.SfCommonStageWeilCohomology`.
- `WeilConjectures.Compactification.Refinement`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`.

The point fibre equivalence module is unnecessary: the statement's higher-stage
admissibility predicates are finite-family criteria, and the actual finite systems
satisfy them directly. No common-stage direct-image or Weil-cohomology theorem is used.
No generic intrinsic interval or finite-Tor transport is needed because the chosen
right adjoints are literally identity. No direct-image composition theorem for the
paper's coefficient categories is needed: the canonical abstract right-derived
precomposition comparison and the existing clopen-section theorem give support identity.
Uniqueness of right adjoints is unnecessary because the theorem asks for an existential
model and we construct it. The direct separated-section lemma is replaced by the proved
`Compactification.isClopen_range_openImmersion` API.

The following old direct proof dependencies are no longer used by the parent proof:

- `def-weil-proetale-module-direct-image`.
- `def-weil-derived-direct-image`.
- `lem-weil-derived-direct-image-composition`.
- `def-weil-extension-by-zero`.
- `def-weil-compact-support-candidate`.
- `def-weil-full-cohomological-dimension`.
- `def-weil-derived-cohomology-sheaves`.
- `def-weil-compactifications-refinements`.
- `def-weil-proper-morphism`.
- `lem-weil-pbc-section-separated-closed-immersion`.
- `det-sp-unique-right-adjoint`.
- `def-weil-constructible-intervals`.
- `def-weil-finite-tor-amplitude`.
- `def-weil-finite-coefficient-point`.

These are removed as direct parent obligations, not globally withdrawn: the constructed
support and FullCD lemmas still use their defining module APIs transitively. No library
module is withdrawn, and no source-library declaration is removed or reproved using sorry.
Removed the parent's now-unused top-level tool approvals for the separated section lemma
and right-adjoint uniqueness, retaining all statements and the unit route.

## Where the brief, the DAG or earlier work was wrong

The prescribed dependencies are definitions rather than a ready-to-apply identity
normalization theorem. The existing clopen-section API already proves the support
isomorphisms and K-injective preservation, so there is no reason to duplicate that
geometric proof. The only missing canonical equation is isolated rather than hidden
inside an arbitrary comparison or right-adjoint existence claim.

The current blueprint identity sentence is at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-global-duality/lem-sf-point.proof.md`.
The current clopen proof moved to
`sec-six-functors-basics/sk-prop-sf-comp-coherence/lem-weil-pbc-clopen-section-direct-image.proof.md`;
the old node source path is stale, and only the latest text was read. Its displayed
section formula gives the normalization used by the constructed support isomorphism.

Edge cases checked mathematically: arbitrary schemes including empty and non-Noetherian
schemes; all sheaves and pro-etale test objects; identity and nonflat coefficient maps,
including Z/l² to Z/l; equal reduction exponents; zero coefficient rings; the positive
first exponent; arbitrary algebraic-closure universe, using the existing Shrink criterion.
The original coefficient and prime hypotheses are unchanged.

## New nodes

`lem-sf-identity-full-cohomological-dimension` records the proved FullCD-zero theorem.
Its proof uses the exactness of an isomorphism direct image and degree-zero cohomology,
not a geometric-point or constructibility equivalence.

`lem-sf-point-identity-support-normalization` records the canonical left coefficient
normalization for the explicit `pointIdentitySupportIso`. Its only hole is the equation
between actual published maps; its proof plan explains section normalization, derived
representatives, and transposition through tensor/restriction. It is strictly simpler
than the original admissibility assertion. Searches are logged by msearch.py. Blueprint
searches found no duplicate identity-support or identity-FullCD node.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
