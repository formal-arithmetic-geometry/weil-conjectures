## What changed

Replaced the body of AlgebraicGeometry.Scheme.rationalCompactSupportCoefficientCoherence
with a complete Lean assembly of normalized compact-support families, normalized
completed-pullback families, single-stage exchange transformations and their
coefficient-square equality. Its original signature and all four public imports stay
unchanged. The base-changed finite-type hypotheses are derived from c' and the open
Cartesian square, not added as assumptions.

Added four theorem modules and four matching DAG nodes. The single-stage theorem
cbcRationalExchangeStage_existsUnique has a complete proof: it restricts the actual
completed exchange, uses its existing generator-independence theorem, extends the
integral natural transformation through scalar localization and proves uniqueness by
components. Its private localization helper reuses the tensor-Hom comparison with
Rationalization and the existing localization/full-whiskering API. No new definition
or arbitrary mathematical datum is extracted from an unproved existence theorem.

The other three modules state strictly separate parts of the original sixteen-step
argument, with the complete source-based natural-language proofs in their docstrings.
The existing parent node now records the actual assembly. The old detailed steps
remain assigned to the subordinate nodes. No source-library module was changed.

## Proved and sorry left

Original item: one hole closed in
AlgebraicGeometry.Scheme.rationalCompactSupportCoefficientCoherence; zero holes remain
in that module. This is a decomposition, not a sorry-free proof of the original
mathematical result: three holes are added, a textual net increase of two.

Additionally proved AlgebraicGeometry.Scheme.cbcRationalExchangeStage_existsUnique
(node lem-cbc-rational-exchange-stage) and the private helper localization_full,
with no sorry in their proof bodies.

The three added holes, each exactly the whole body of its public theorem, are:

- AlgebraicGeometry.Scheme.cbcCompactSupportCoefficientFamily_exists:
  lem-cbc-normalized-support-family-existence. This constructs one compact-support
  family and its normalization, without any square or exchange.
- AlgebraicGeometry.Scheme.cbcCompletedPullCoefficientFamily_exists:
  lem-cbc-normalized-pull-family-existence. This constructs one completed-pullback
  family, without compactifications or exchange.
- AlgebraicGeometry.Scheme.cbcRationalExchange_coefficientSquare:
  lem-cbc-rational-exchange-coefficient-square. The four families and all normalized
  stage exchanges are supplied; its conclusion is only the coefficient-square
  equality. It does not construct the families, the stage maps or their normalization.

The new statements retain arbitrary base-change morphisms, repeated coefficient
stages, all raw rational objects and all generating tuples (including an empty tuple
whenever it generates the ideal). Empty schemes and zero objects impose no
nonemptiness condition. The coefficient-square theorem makes no claim that exchange
is invertible. Family existence supplies no exchange clause. Thus none of these
three is the original theorem with its hypotheses repackaged.

Validation: the initial assembly and all four statement modules compiled together.
The complete single-stage proof also compiled successfully with lcompile.py. The
final import-minimized packet is checked together and then by deliver3.py.

## No longer needed

No mathematical node or module is claimed to be pruned from the project: the old
proof dependencies are distributed over the subordinate argument nodes and remain
needed by those proofs. No module is withdrawn. The four public imports of the item
stay verbatim.

The following private imports were removed from the item because its proof now uses
only the four new theorem modules; relevant lower dependencies remain in the new
nodes or are imported by the proved single-stage theorem:

- `Sheaf.Paper.PbcActualRingedExchange`
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`
- `Sheaf.Paper.CompletedOpenExchangeTransport`
- `Sheaf.Paper.IntegralCompactSupportUniformRestriction`
- `Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.Paper.SbcCompletedOperations`
- `Sheaf.CategoryTheory.StrictTowerArithmeticRestriction`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.CategoryTheory.Sites.Limits`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.Paper.WeilCompletedTensorReflector`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.Paper.PbcUniformCompleteTriangulated`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.KoszulReconstruction`
- `Sheaf.Paper.PreservationConstructible`
- `Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `Sheaf.Paper.CondensedAmbientExchange`
- `Sheaf.Paper.IntegralUniformCoefficient`
- `Sheaf.Paper.PbcQbarCompletedPullback`
- `Sheaf.Paper.PbcRationalCategory`
- `Sheaf.Paper.PbcRationalTransport`
- `Sheaf.Paper.PbcScalarExtension`
- `Sheaf.Paper.ProjectionCompactification`
- `Sheaf.SixFunctors.OpenTensorNormalization`

The parent's obsolete top-level tool_uses list was cleared: its immediate proof now
uses the four same-unit subordinate nodes and the compactification/normalization
definitions. This does not withdraw the generic tools from the subordinate proofs.

## Where the brief, the DAG or earlier work was wrong

The original sixteen-step plan was mathematically useful, but its existing imported
signatures do not directly construct CbcCompactSupportCoefficientFamily or
CbcCompletedPullCoefficientFamily with all of their strict datum, unit, localization
and shift equations. PbcPullbackCoherentFamily is the closest existing result; it
uses the reflector pullback and a different beta specification. The missing
strict/unit transport is now explicitly assigned, not hidden in the assembly.

The existing finiteExtension_compactSupportBaseChange uses the unlifted integer-ring
datum, whereas this item uses PbcIntegralRing and the canonical small coefficient
stages. The proved single-stage theorem avoids assuming these different data are
definitionally equal: it works directly in the existing stage categories and uses
the existing actual completed exchange and generator-independence result.

The historical thm-cbc-qbar source path in the original node is absent from the
current latest blueprint. New nodes cite the present compact-support coefficient
comparison and coefficient-coherence proof pages, while retaining the original
open/proper mate and strict completion normalization argument. The parent statement,
its historical source metadata and the unit route are unchanged.

## New nodes

lem-cbc-normalized-support-family-existence: one chosen compactification has its
specified exact normalized coefficient family. Module
Sheaf.Paper.CbcCompactSupportCoefficientFamilyExistence; one named hole.

lem-cbc-normalized-pull-family-existence: one morphism has its specified strict
completed-pullback coefficient family. Module
Sheaf.Paper.CbcCompletedPullCoefficientFamilyExistence; one named hole.

lem-cbc-rational-exchange-stage: existence and uniqueness of the normalized exchange
at a fixed raw rational stage for supplied families. Module
Sheaf.Paper.CbcRationalExchangeStage; fully proved in Lean.

lem-cbc-rational-exchange-coefficient-square: supplied normalized stage exchanges
satisfy the coefficient square. Module
Sheaf.Paper.CbcRationalExchangeCoefficientSquare; one named hole.

No change record is required: no existing public signature, definition or public
import changed. No forced adaptations were made.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
