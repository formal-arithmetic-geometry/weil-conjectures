## What changed

Proved `AlgebraicGeometry.ProEtale.properHeartBoundTorsion` with its original statement and
coefficient definitions. Added proved private helpers in the same module for natural tensor
projection, finite quotient scalar restriction, constructible etale origin, geometric fibre
dimensions, and the cohomology bound. No public signature or definition changed. The conservative command-scope gate is documented
in `coord/changes/A2-proper-heart-torsion-private-proof-scopes.md`, including both consumers
and their current holders.

The natural isomorphism uses flatness of the extended lisse integral module and the supported
locally closed tensor projection. The quotient is constructed by ordinary scalar extension,
then transported through the normalized finite discrete encoding; every integral scalar is
checked against its actual quotient. Finite constant stratifications give constructible etale
origin. The bound uses the proper torsion direct-image theorem, the qcqs comparison, and exact
abelian evaluation at the given object V. Bounded-below derived composition and its unbounded
compatibility identify this with the requested cohomology.

Updated the existing node's proof, proof dependencies and proof origin to follow this argument.
The requested LeanFinder search for finite quotients of lisse integral modules found no matching
whole theorem; Loogle did not resolve the scalar-extension search name, and the required grep
search found no direct proper-torsion replacement. Repository searches located the supported
flat tensor projection, finite-discrete encoding, proper bound and comparison APIs used here.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.properHeartBoundTorsion` (1 existing hole).
Added holes: none. Remaining holes in the delivered module: zero. Split-off statements: none.
Every private helper is proved. Private comparison constructions are locally irreducible
after their normalization and naturality lemmas, so later tactics use their interfaces without
unfolding large monoidal terms. The complete assembled module compiled successfully through
`lcompile.py` (exit 0, 44.4 seconds; no warnings). A byte-for-byte source comparison confirms that the
original coefficient definitions and theorem signature are unchanged. The axiom query reports
`propext`, `Classical.choice`, `Quot.sound` and transitive `sorryAx`; this delivery closes
the assigned theorem body, not every unfinished dependency in the project. The delivered module
contains no `sorry` token and every line is at most 100 characters.

## No longer needed

Removed these direct proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.PullbackCarrier`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`
- `Mathlib.Topology.Constructible`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.Paper.CondensedConstructibleOpenClosedImages`
- `Sheaf.Paper.FiniteConstantCokernel`
- `Sheaf.Paper.FiniteRingConstructibleSheafOrigin`
- `Sheaf.SixFunctors.IntTensorProjection`
- `WeilConjectures.AlgebraicGeometry.Dimension`
- `WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover`
- `WeilConjectures.AlgebraicGeometry.DimensionBaseChange`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`

The revised proof does not need these former direct DAG dependencies:

- `def-weil-constructible-subset`
- `def-weil-finite-type-morphism`
- `det-lem-int-tensor-projection`
- `lem-pc-dim-base-change`
- `lem-pc-dimension-affine-open-cover`
- `lem-pc-proper-base-change`
- `lem-pc-scheme-dimension-local-rings`
- `lem-sc-affine-noetherian-underlying-space`
- `lem-weil-pbc-comparison-pullback`
- `lem-weil-pbc-condensed-constructible-open-closed-images`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-finite-constant-proetale-cokernel`
- `lem-weil-pbc-finite-ring-constructible-sheaf-origin`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-localized-sheaves-over-representable`
- `lem-weil-pbc-open-fibre-product`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-weil-pbc-proetale-weakly-contractible-evaluation-exact`
- `lem-weil-pbc-standard-quotients-perfect`
- `sk-def-sfb-coefficient-morphisms`
- `sk-def-sfb-constructible`
- `sk-def-sfb-derived-categories`
- `sk-def-sfb-module-lower-shriek`

The supported flat tensor projection replaces the resolution-and-cokernel route. Explicit
finite constant local models replace the arbitrary-presentation cokernel route. The normalized
fixed-module constructible comparison supplies etale origin. Dimension invariance for finite-type schemes under
field extensions replaces the affine-chart dimension calculation. Exact evaluation at V in
Y's site and the existing bounded-below derived-composition API avoid constructing the localized slice topos, and applying the torsion direct-image
bound to p avoids checking the bound again after base change to V. No module is withdrawn;
shared dependencies can remain needed by other declarations and by the imported proofs.

## Where the brief, the DAG or earlier work was wrong

No statement repair was required. The DAG's proof was mathematically sufficient but contained
extra intermediate machinery. The proof now records the shorter routes above while retaining
the unit's required integral reduction, classical etale origin and proper torsion bound.
The characteristic restrictions remain verbatim, although this torsion argument does not use
them: the relative proper torsion bound is stronger than those hypotheses require.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
