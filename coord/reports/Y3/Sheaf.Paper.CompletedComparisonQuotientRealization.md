## What changed

Reduced completedComparisonQuotientRealization to three strictly smaller realization
steps: completedComparisonQuotientNormalization (normalization, presentation and
recursive naturality), completedComparisonCanonicalIdentification (identification
with the fixed comparison, strict coherence and derived naturality), and
completedComparisonScalarLimitImage (scalar closure and limit-image equations).
Each has its own new module, node, source and complete proof in words.

The assembly proves the whole-system counit equation explicitly using counit
naturality and cancellation of the target substitution. It constructs structural
isomorphisms as the conjugates of strict isomorphisms and proves both required
squares and uniqueness. The inverse comparison follows from the forward equality
by cancellation. Scalar identity, successive extension and quotient association
use the existing ScalarExtensionTower.unit, composition and quotientModels.

Moved the existing construction declarations to a publicly re-exported definitions
module to let the independent proof-step modules use them without importing the
parent theorem. Existing names, signatures and mathematical meanings are retained.
Profiling found monoidal-instance search on the complex alias in strictMap; the
tensor branch now supplies all complex objects to the same tensorHom explicitly,
with local irreducibility of the sheaf monoidal structure. GoodExpressions is an
abbrev of its identical predicate to keep witnesses usable as functions across
module boundaries.
See coord/changes/Y3-completed-comparison-realization-steps.md.

## Proved and sorry left

This is a decomposition, not a sorry-free proof of the mathematical theorem.
Closed the one original theorem hole:
WeilConjectures.CompletedQuotient.completedComparisonQuotientRealization
(lem-pur-completed-comparison-quotient-realization).

Added three named holes, each exactly `:= by sorry`:

- WeilConjectures.CompletedQuotient.completedComparisonQuotientNormalization
  (lem-pur-completed-comparison-quotient-normalization).
- WeilConjectures.CompletedQuotient.completedComparisonCanonicalIdentification
  (lem-pur-completed-comparison-canonical-identification).
- WeilConjectures.CompletedQuotient.completedComparisonScalarLimitImage
  (lem-pur-completed-comparison-scalar-limit-image).

The original item has zero remaining holes. The definitions module has zero holes.
No hole was added inside a definition. The original theorem signature was checked
byte-for-byte against the current source; it is unchanged. Net holes closed minus added is -2.
The elementary assembly includes genuine calculations beyond conjunction packing.

## No longer needed

Removed unused direct proof imports from the original definitions/assembly:
Sheaf.Paper.QuotientExpressionKFlatNormalization,
Sheaf.Paper.CompletedPrimitiveCounitComparison,
Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus,
Sheaf.SecSmoothPurity.StrictCoefficientComparisonCalculus,
Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients,
and Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients.
They are not directly needed by the explicit elementary assembly or the data.
Their mathematical results remain needed below the three split statements, as
recorded by those nodes. This packet does not claim to prune their modules from
the target closure, and withdraws no module.

The original node's direct proof obligations are now the three split steps and
the scalar tower coherence theorem. Its former direct proof dependencies
lem-pur-quotient-expression-kflat-normalization,
lem-pur-normalized-actual-reconstruction-maps,
lem-pur-completed-operation-tower-substitution,
lem-pur-cochain-pullback-tensor-coherence,
lem-weil-pbc-ringed-strict-tower-homotopy-limit,
lem-pur-completed-primitive-counit-comparison,
def-pur-completed-pullback-tensor-comparison,
lem-weil-pbc-site-derived-tensor-descent,
lem-pur-normalized-scalar-comparison-realization and
lem-pur-strict-coefficient-comparison-calculus are retained in the lower realization
proof plans where they are used, rather than direct steps of the parent assembly.
The parent node's now-obsolete direct tool approvals for
lem-pur-normalized-actual-reconstruction-maps,
lem-weil-pbc-ringed-strict-tower-homotopy-limit and
lem-weil-pbc-site-derived-tensor-descent were removed from its tool_uses list;
these results remain lower proof-plan dependencies.

## Where the brief, the DAG or earlier work was wrong

The generic dependency statements do not immediately identify the particular
recursive substitutions in this module with the fixed canonical comparison:
normalization of an isomorphic quotient family does not by itself identify the
actual prescribed quotient transitions, and the generic completed-operation model
is existential. The three new obligations isolate these representative and
interface identifications; none merely renames the whole theorem.

The current blueprint definition of derived pullback/tensor/Hom states these
operations directly and places finite-reduction/scalar compatibility in a theorem.
This packet retains the assigned representative realization route without changing
any unit or chapter route. The unit realized.statement and realized.steps are empty;
no realized unit assertion or step is bypassed. Dependency traversal confirms that
none of the four new nodes has a statement/proof dependency path back to the item.

Checked empty schemes, zero complexes, identity pullbacks/coefficient extension,
repeated inputs and units: the lower statements introduce no nonemptiness,
boundedness, coefficient flatness or new finiteness assumptions. Proofs of good
and invertible are propositions, so the scalar and canonical steps can use any
witnesses of those same properties without changing the substitution maps.

## New nodes

- def-pur-completed-comparison-quotient-realization-data owns the relocated exact
  construction declarations and their predicates; it adds no chosen object.
- lem-pur-completed-comparison-quotient-normalization is realization proof step 1
  and recursive representative naturality from step 3.
- lem-pur-completed-comparison-canonical-identification isolates the fixed-map
  identification in steps 2–3 and strict coherence in step 5.
- lem-pur-completed-comparison-scalar-limit-image isolates the scalar normalization
  and actual strict-square limit image of steps 6–7.

Searches ran through msearch.py (LeanSearch, LeanFinder, Loogle and grep) and local
rg over Sheaf, WeilConjectures and DAG records. The Mathlib hits concern ordinary
completion/tensor and adjunction naturality; none supplies the three specialized
realization steps. Blueprint searches for quotient realization and scalar comparison
found no exact existing node. Available source dependency declarations were read
before splitting. The recorded module NormalizedScalarComparisonRealization is
absent from lean/ and has no row in coord/rework.tsv; its node remains attached and
its mathematics is retained in the lower scalar proof plan. Existing
ScalarExtensionTowerCoherence.realizationModels, scalarExtensionTowerCoherence,
quotientModels and CoefficientExtensionReductionModel were read as the available
normalized scalar interfaces. The existing scalar unit/composition/quotient-model
statements are used without introducing duplicates.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
