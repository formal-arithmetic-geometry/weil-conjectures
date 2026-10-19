## What changed

Retained and repaired the earlier sandbox and completed all eight original theorem
proofs. Public statements, definitions and public imports are unchanged.

Slice restriction is additive and exact by sectionwise limits and its existing left
adjoint. Upstream covering conservativity and the dense affine subsite detect
isomorphisms of underlying abelian sheaves, then module sheaves. Exact-functor homology
compatibility lifts these criteria to derived categories. The affine-open criterion
combines covering conservativity with affine restriction.

For etale-origin stalk detection, the sheafification counit identifies coefficient
realization after forgetting scalars with the original underlying abelian sheaf.
Forgetting modules commutes with the neighbourhood colimit. Combine these comparisons
with the canonical comparison-stalk isomorphism and exact comparison's homology
compatibility, then use etale stalk conservativity. Constructible morphisms lift through
full faithfulness after choosing their bounded-below etale-origin presentations.

For the counterexample, identify the specified quotient with the proved affine
functions-quotient construction via its section identifications and the sheafification
unit/counit identities. All functions on the field spectrum are constant. The proved
private classicalStalk_initial helper, available through import all of
ProEtaleClassicalStalk, makes the identity pointed neighbourhood initial directly over
k, so its evaluation-to-stalk colimit leg is invertible. For nonvanishing use
Spec(LocallyConstant E k), with E the one-point compactification of the discrete natural
numbers. Existing weaklyEtale and spectrum-homeomorphism results apply directly.
A nonzero spike at infinity is not locally constant, since the natural numbers are
dense. Its affine quotient class is nonzero.

Added private proved helpers and proof imports of Open.Conservative, ExactFunctor and
OnePoint.Basic. The declaration-local unused-variable linter option preserves the
original hF/hG binder names. Updated the existing DAG node to match these arguments.

## Proved and sorry left

Closed all eight original holes:

- AlgebraicGeometry.ProEtale.finiteCoefficientSliceRestriction_exact
- AlgebraicGeometry.ProEtale.finiteCoefficient_cover_detection
- AlgebraicGeometry.ProEtale.finiteCoefficient_affine_basis_detection
- AlgebraicGeometry.ProEtale.finiteCoefficient_affine_open_basis_detection
- AlgebraicGeometry.ProEtale.finiteCoefficient_etale_origin_stalk_detection
- AlgebraicGeometry.Scheme.proEtale_abelian_cover_zero_detection
- AlgebraicGeometry.Scheme.proEtale_abelian_affine_basis_zero_detection
- AlgebraicGeometry.Scheme.proEtaleFunctionsQuotient_counterexample

No holes remain in the item module. No holes added; no split-offs or new nodes.
The declarations realize lem-cbc-proetale-stalk-conservative. Named dependencies may
still have their own holes, as intended in stage 3.

## No longer needed

Removed these unused proof-only imports:

- Sheaf.CategoryTheory.SiteCoveringAxioms
- Sheaf.Paper.SiteRestrictionInjectives
- Sheaf.AlgebraicGeometry.StrictHenselization
- WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
- Sheaf.RingTheory.IndPrincipalZariski
- Sheaf.RingTheory.IndEtaleStability
- Mathlib.CategoryTheory.Sites.Abelian
- Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
- Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
- Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
- Sheaf.RingTheory.IndEtaleUniverseTransport

The completed proof no longer needs these declared dependency nodes:

- def-weil-pbc-sites-and-cohomology: use upstream covering conservativity directly.
- lem-weil-pbc-proetale-restriction-injectives: use the existing module slice adjunction.
- lem-weil-pbc-site-restriction-injectives: use the existing module slice adjunction.
- lem-weil-pbc-left-adjoint-preserves-colimits: use Mathlib's existing instances.
- def-weil-pbc-site-comparison-morphism: the comparison API is already provided by
  the public coefficient definitions and the comparison-stalk dependency.
- def-weil-pbc-strict-henselization-limit: use the identity pointed neighbourhood directly.
- lem-exc-etale-lift-separably-closed-factorization: reuse proved weakly etale lifting.
- def-weil-pbc-ind-etale-algebra: use the direct proved locally-constant weak etaleness.
- lem-weil-pbc-ind-etale-stability: use that same proved instance.
- lem-weil-pbc-profinite-limit-function-factorization: no filtered presentation is needed.

The localized-ringed-site node remains needed through its Mathlib overFunctor API.
All unit statements and realized routes are preserved. Public imports are unchanged.
The direct import of ProEtaleSiteComparison is retained to preserve the unit route.
These are direct import and proof-dependency removals; some removed modules remain
reachable through retained dependencies, notably the classical-stalk module.
The bounded-below comparison is used through ProEtaleSiteComparisonDerived rather
than the unused compact-support unit interface.

## Where the brief, the DAG or earlier work was wrong

The retained attempt required repairs to its component-isomorphism tactic, derived
isomorphism criterion application and acyclicity proof. The counterexample's planned
filtered-colimit construction is unnecessary because the library already proves weak
etaleness and the spectrum computation for LocallyConstant E k. No mathematical error
in the statements or unit route was found.

The current session compiled the seven retained proofs independently, then compiled
the full eight-proof experiment and removed its tactic-style warnings. Delivery tool
retries were necessary: one process ended with exit code 137 and another crashed with
a TimeoutExpired during temporary-worktree checkout after 600 seconds. Compile-server
requests also occasionally returned no answer and were retried. No launcher script
was changed or bypassed.

The resumed dry run compiled and passed its axiom probe, then identified a new
global notation-scope command and a removed unit-route import. Removed the global
scope by qualifying OnePoint.infty, and restored ProEtaleSiteComparison.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
