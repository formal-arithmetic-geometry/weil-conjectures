## What changed

Repaired all three points of return C-acb12 (returned head acb128f534). The retained
sandbox and the delivery-final log confirmed the earlier delivery before any new push.
The assigned theorem keeps its signature and all eight conclusions unchanged.

1. The criterion is now specialized to l, E and pbcIntegralDatum l E. Its forward
   implication takes the homologyProperty clause directly from the landed
   pbcUniformReductionCriterion, whose forward implication is Q5's proved
   pbcUniformLocalModelCohomology. This avoids an unnecessary round trip through the
   duplicate intrinsic predicate and the fixed-module encoding.
2. Its reverse implication proves the existing PbcUniformReductionProfile on
   [min a b,b] by the exact coefficient-restriction homology isomorphism, then applies
   pbcUniformReductionCriterion_backward. Both duplicate assembly modules are removed.
3. The criterion and both operation lemmas now state the existing profile's
   homologyProperty clause. Their proofs transport this clause through the canonical
   exact homology isomorphism. No duplicate cohomology predicate remains. All five
   criterion calls in PreservationConstructible pass l and E. Nodes and dependencies
   follow these proofs.

Also completed pbc_finite_directImage_cohomology rather than retaining its split hole.
The private reductionEncoding is the actual exact coefficient equivalence. The
sectionwise direct-image comparison follows from the canonical coefficient square;
right-derived composition gives its derived comparison. The private fixedDirectImage
uses etale proper finiteness for a constructible sheaf, then the existing bounded
truncation arguments for constructibility and the [a,b+2e] bound. Transport through
homology gives the specified quotient-module result. The comparison is chosen from a
unique normalized isomorphism, not arbitrary object existence. All private helpers
are proved. No definition has postponed data.

All six production modules were compiled together through lcompile.py --all. During
initial checks the shared server lacked newly landed uniform-criterion artifacts;
unchanged dependency sources were temporarily compiled in the sandbox, then removed
from the packet. Only their compiled sandbox artifacts are used by subsequent checks.
The final dry run is recorded separately by deliver3.py.

Change record: coord/changes/B5-preservation-uniform-profile-repair.md. Its consumer
check covers the complete packet. The five support modules and four removed modules
never landed on main, and no external consumer or another group's module is adapted.

## Proved and sorry left

Original assigned hole: WeilConjectures.pbc_preservation_constructible. Closed: 1 of 1.
New holes added: 0. Sorries left anywhere in the delivery's six Lean modules: 0.

The following public intermediate theorems are proved, not split obligations:

- AlgebraicGeometry.Scheme.pbc_constructible_reduction_criterion
- AlgebraicGeometry.Scheme.pbc_constructible_reduction_directImage
- AlgebraicGeometry.Scheme.pbc_constructible_reduction_pullback
- AlgebraicGeometry.Scheme.pbc_finite_directImage_cohomology
- AlgebraicGeometry.Scheme.pbc_finite_pullback_constructibility

Relative to the returned packet, the finite direct-image hole is proved and the
uniform-reduction-constructibility hole is removed as a duplicate of a landed result.
Relative to current main, the packet closes the assigned hole and introduces none.
These proofs use the project's named declarations; this is not a claim that all
transitive library dependencies are already free of sorry.

## No longer needed

Removed from the returned packet, both module and newly proposed node:

- Sheaf.Paper.PbcUniformReductionConstructibility;
  lem-weil-pbc-uniform-reduction-constructibility. The landed uniform criterion's
  forward direction already supplies the cohomology clause.
- Sheaf.Paper.PbcCanonicalReductionModels;
  lem-weil-pbc-canonical-reduction-models. The landed backward criterion supplies it.
- Sheaf.Paper.PbcCanonicalEtaleOrigins;
  lem-weil-pbc-canonical-etale-origins. The same backward criterion supplies it.
- Sheaf.Paper.PbcReductionConstructibility;
  def-weil-pbc-reduction-cohomology-constructible. Reuse the existing
  def-weil-pbc-uniform-reduction-profile cohomology clause.

The criterion no longer directly imports normalized local effectivity, levelwise
adic truncations, normalized origin witnesses or bounded-below comparison. Those
remain internal to the landed uniform criterion, so are not claimed globally pruned.
The new finite direct-image proof no longer uses
Sheaf.Paper.FiniteRingConstructibleDerivedOrigin /
lem-weil-pbc-finite-ring-constructible-derived-origin: the site-universe coefficient
encoding and fixed-module truncation argument avoid a small-ring presentation.

Removed direct imports from the original assigned module:

- Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
- Sheaf.Paper.AdicCoefficientDatum
- Sheaf.Paper.AmplificationProper
- Sheaf.Paper.BoundedConstructibleTower
- Sheaf.Paper.CompletedConstantSheafReduction
- Sheaf.Paper.CompletedDirectImageLimits
- Sheaf.Paper.CompletedPullbackReduction
- Sheaf.Paper.ConstantCompletionEquivalence
- Sheaf.Paper.FiniteLevelAmplification
- Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
- Sheaf.Paper.IntegralUniformCoefficient
- Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity
- Sheaf.Paper.NormalizedEtaleOriginWitnesses
- Sheaf.Paper.PerfectProjectionFormula
- Sheaf.Paper.ProEtaleCanonicalTensorPullback
- Sheaf.Paper.RestrictionDirectImage

The route does not use thm-weil-pbc-amplification-proper or
 def-weil-pbc-finite-level-amplification: proper finite-level finiteness and exact
pullback apply separately to the single maps. The actual quotient-linear projection
comparison supplied by completedDirectImageProjectionFormula_properties removes the
need to lift an arbitrary completed-linear isomorphism. Thus no direct proof use of
lemma-weil-pbc-perfect-projection-formula,
lem-weil-pbc-completed-constant-sheaf-reduction or
lem-weil-pbc-constant-completion-equivalence is needed for that lift. These modules
are not claimed globally unreachable; retained intermediate declarations may use them.
No blueprint unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned packet duplicated the existing uniform-profile definition and both
halves of the landed integral uniform criterion. C-acb12 correctly identified those
copies. The repaired criterion uses that existing interface directly; the generic
adic-datum claim is no longer asserted by this new packet lemma. Every consumer in
this packet already uses the integral datum.

The finite direct-image proof does not need a small-ring presentation. The existing
ConstructibleCoefficientSerre encoding works in Type (u+1), and its exact equivalence
transports both homology and right-derived direct image. This completes the retained
finite-level proof instead of introducing further statements.

The refreshed blueprint says both pullbacks retain [a,b], but pullback of Rf_*K must
retain [a,b+2e]. The assigned statement already corrects this and is preserved. For
g=id and a proper projective line, degree-two cohomology explains the issue. The
proved field-dimension and Cartesian-pasting arguments handle the arbitrary base map.

## New nodes

Five retained new nodes, all realized by completely proved public theorems:

- lem-weil-pbc-canonical-reduction-constructibility-criterion: integral completeness
  paired with the existing constant-reduction cohomology clause.
- lem-weil-pbc-constructible-reduction-direct-image: completeness, the existing profile
  cohomology clause, and support bounds for one proper completed-coefficient image.
- lem-weil-pbc-constructible-reduction-pullback: the corresponding interval-preserving
  completed pullback statement.
- lem-weil-pbc-finite-direct-image-cohomology: proved one-level proper finiteness and
  support growth in the actual quotient-module category, with no completed object.
- lem-weil-pbc-finite-pullback-constructibility: proved exact inverse-image
  constructibility at one finite quotient level.

The four duplicate new nodes listed above are removed from this resubmission, as the
review requests. No existing DAG node is deleted. Change record:
coord/changes/B5-preservation-uniform-profile-repair.md.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
