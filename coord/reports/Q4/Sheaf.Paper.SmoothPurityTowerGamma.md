## What changed

Replaced the single sorry in AlgebraicGeometry.ProEtale.SpTowerGamma.tower_gamma
by an assembly proof. It obtains a diagonal orientation and its actual finite
comparison words, applies twisted_pullback_tower_domain to each input's common
Tor interval, and applies tensor_transpose_evaluation. Cancellation of the two
invertible word comparisons gives finite-evaluation invertibility, and the given
system calculus detects invertibility of the actual tower map. The same evaluation
lemma supplies naturality and every finite-level equation. The two normalization
fields are supplied separately.

Added OrderedTowerOrientation and TowerNormalizationPreservation as strictly smaller
source subarguments. FiniteGammaEvaluationIsIso is fully proved using the library
smooth tensor-duality theorem and preservation of inverses.
The full theorem's hypotheses, conclusion and Purity fields are unchanged.

Extracted the twenty original data declarations verbatim into
SmoothPurityTowerGammaData. SmoothPurityTowerGamma publicly re-exports them and
retains every original public import. This removes the actual import cycles from
the existing domain and evaluation lemmas back to the tower theorem.
TwistedPullbackTowerDomainDefinitions and TowerTensorTransposeWords change only
their public import to the data module. Their declarations are untouched. The recently
landed proofs of twisted_pullback_tower_domain and tensor_transpose_evaluation
are used unchanged from the current library.

Change record: coord/changes/Q4-tower-gamma-data-extraction.md.

## Proved and sorry left

Closed the original hole
AlgebraicGeometry.ProEtale.SpTowerGamma.tower_gamma (det-sp-tower-gamma),
by a complete combination proof from the stated domain and evaluation lemmas and
three smaller substeps (one now proved). The item's module contains no sorry.

Added two holes:

- AlgebraicGeometry.ProEtale.SpTowerGamma.ordered_tower_orientation in
  Sheaf.Paper.OrderedTowerOrientation (lem-sp-ordered-tower-orientation):
  the diagonal orientation and its coefficient-unit comparison, without purity
  isomorphy, naturality or normalized-output assertions.
- AlgebraicGeometry.ProEtale.SpTowerGamma.tower_normalization_preservation in
  Sheaf.Paper.TowerNormalizationPreservation (lem-sp-tower-normalization-preservation):
  the two normalized-output properties only, without orientation or tower purity.

This is a decomposition: one original hole closed, two added, net -1, not a
claim of a complete proof of smooth purity. Both holes have source references,
complete natural-language proof plans and corresponding nodes. The extracted data
module has zero holes. Also proved finite_gamma_evaluation_isIso without a new hole,
using Etale.smooth_tensor_duality on the actual finite gamma word. The two
import-adapted definition modules have no new holes.

Six further modules are not part of the delivery and are unchanged; the global build
rebuilds them against the relocated definitions: TowerTensorTransposeEvaluation,
TensorTransposeTowerNaturality, TensorTransposeFiniteEvaluation,
TwistedPullbackTowerDomain, TwistedPullbackTowerBounds and
TwistedPullbackTowerOrigins. Their existing holes are unchanged:

- AlgebraicGeometry.ProEtale.SpTensorTranspose.tensor_transpose_tower_naturality.
- AlgebraicGeometry.ProEtale.SpTensorTranspose.tensor_transpose_finite_evaluation.
- AlgebraicGeometry.ProEtale.SpTwistedTowerDomain.pullback_ordered_tate_bounds.

## No longer needed

Removed the proof-only imports Sheaf.Paper.StrictLineHeartAssembly,
Sheaf.Paper.FiniteCoefficientSmoothPurity,
Sheaf.SecSmoothPurity.ScalarExtensionFunctor and
Sheaf.SecSmoothPurity.ReductionDirectImage from the original module; their roles are
recorded in the smaller orientation, finite-isomorphy and normalization substeps.
Those nodes remain needed by these substeps and are not withdrawn or pruned.
The original finite-orientation, strict-heart, scalar-extension and reduction
arguments remain in the unit route. The finite gamma sublemma instead uses
thm-asd-smooth-tensor, which proves invertibility of the exact tensor-counit word;
it does not need the uniformizer-orientation identification. The orientation
normalization hypothesis stays explicit for use by the main evaluation lemma. No module or mathematical dependency is claimed
pruned. Every original public import is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies had Lean declarations, but two imported the module
containing the theorem that was meant to use them. The data extraction repairs this
cycle without changing any mathematical object. The orientation result uses a record with a separate OrderedDiagonalLevels
predicate, so the generated eliminator does not repeat the long finite word equations.
Its structure and predicate are constructions with no sorry. The DAG now separates its original
data attachment from its theorem attachment and describes the proof actually used.
The unit's own statements and steps remain unchanged.

The common Tor interval must be transported from the original strict-tower
coefficient evaluation to the realization used in the domain lemma. The proof
composes its representing isomorphism with levelComparison, rather than assuming
these two evaluations are identical.

## Forced adaptations

TwistedPullbackTowerDomainDefinitions and TowerTensorTransposeWords are currently
unclaimed. In each, only line 8 changes: the public import of
Sheaf.Paper.SmoothPurityTowerGamma is replaced by the public import of
Sheaf.Paper.SmoothPurityTowerGammaData. Without these edits the import graph contains
Gamma -> TwistedPullbackTowerDomain -> TwistedPullbackTowerDomainDefinitions -> Gamma
and Gamma -> TowerTensorTransposeEvaluation -> TowerTensorTransposeWords -> Gamma.
Lean rejects cyclic imports before elaborating declarations. No signature,
visibility, definition body or proof changes in these two modules. The current
proved domain and evaluation modules themselves are not part of this packet.
PurityConjugatesTowerReduction is also unchanged.

The first preflight was based on older copies of the two theorem modules, which
had acquired proofs on the server during this session. Those copies were removed;
the refreshed packet preserves the new proofs and adapts only the data modules.

## New nodes

lem-sp-ordered-tower-orientation records source clause (1), the compatible diagonal
orientation and its ordered strict-line presentation. The zero-dimensional case
uses the coefficient unit; indices always represent n+1 > 0.

lem-sp-finite-gamma-evaluation-isIso records the proved finite-invertibility step of
source clause (2). Its proof uses thm-asd-smooth-tensor directly. It assumes no input
tower normalization; the normalized finite orientation is explicit.

lem-sp-tower-normalization-preservation records source clause (3), separately from
construction and isomorphy of gamma. Equal quotient indices and d=0 are included.

def-sp-tower-gamma-data attaches the twenty verbatim existing data declarations to
the extracted module. It adds no mathematical assertion or hole.

The original det-sp-tower-gamma proof, dependencies and declaration attachment were
updated to match the assembly. No existing node's statement, source, unit route or
maintainer tool approvals were changed. Change record:
coord/changes/Q4-tower-gamma-data-extraction.md.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer corrections

The item's node det-sp-tower-gamma now lists def-sp-tower-gamma-data (owner of
Purity, used by the statement) in proof_deps and in the last step's uses. The change
record's Users table gained FieldExceptionalSystemComparison and
FieldExceptionalSystemDomains, direct importers landed after the delivery base.
The item's stmt_deps still lack def-sp-tower-gamma-data, because stage-3 tooling
refuses a stmt_deps change together with a proof change (maintainer note).
