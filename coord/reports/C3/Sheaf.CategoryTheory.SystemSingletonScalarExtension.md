## What changed

Replaced the sole sorry in SheafOfModules.singletonScalarExtension by a compiling proof
that assembles three strictly smaller intermediate theorems. The full original statement
is unchanged. Direct proofs establish the Hom-transpose clause, the precise local tensor
formula, and both zero objects and the zero map above n. The tensor formula uses actual
normalized adjoints, systemSingleTranspose, the singleton unit/transition formulas and
module linearity; it is not an independently chosen tensor isomorphism.

The K-flat representative clause now combines singletonSequenceOrdinary_kFlat over B and D
with isKFlat_ringedToposPullback for explicitly constructed identity algebraic inverse
images. The existing computes fields give invertibility of both universal comparisons.
The representative equation and lower-singleton square are supplied by their respective
new intermediate statements.

Extracted the existing fixed comparison constructions into SystemSingletonScalarBasic,
with unchanged signatures and bodies, reexported publicly by the item. This breaks the
otherwise circular imports between the parent and its three intermediate modules.
Change record: coord/changes/system-singleton-scalar-proof-decomposition.md.

All five packet modules compile within the 60-second limit. The final parent proof
compiled in 28.1 seconds with both respectTransparency checks enabled. The unchanged direct consumers compiled against the packet:
SystemSingletonGeometricPullback (29.7 s), NormalizedArithmeticInterpolation (34.6 s), and
SystemEvaluationNormalizationData (34.4 s). Their original source copies were removed from
the sandbox after checking, so no unchanged consumer is delivered.

## Proved and sorry left

Closed the original textual hole in SheafOfModules.singletonScalarExtension (node
lem-pur-system-singleton-scalar-extension). There are zero sorries in the item module.
This is a decomposition: one original hole closed and three new holes added, net -2;
it is not claimed as a complete proof of the full theorem.

The public theorem bodies left as exactly `by sorry` are:

- SheafOfModules.singletonSequenceOrdinary_kFlat, node lem-pur-system-singleton-kflat,
  module Sheaf.CategoryTheory.SystemSingletonKFlat. It states only preservation of the
  flat-term K-flat class by ordinary singleton extension, independently of coefficient a.
- SheafOfModules.singletonScalarDerivedIso_rep, node
  lem-pur-system-singleton-scalar-representative, module
  Sheaf.CategoryTheory.SystemSingletonScalarRepresentative. It states only the comparison
  equation, for arbitrary complexes, and makes no K-flatness or lower-map assertion.
- SheafOfModules.singletonScalarDerivedIso_lower, node
  lem-pur-system-singleton-scalar-lower, module Sheaf.CategoryTheory.SystemSingletonScalarLower.
  It states only compatibility with lower-singleton maps.

The four private helpers singletonIdentityInverseImage, singletonScalarModel_kFlat,
singletonSequenceComparison_isIso and singletonScalarOrdinary_tmul are completely proved.
No data is selected from a new unproved existence theorem, and no definition has a hole.

## No longer needed

Removed these original proof-only imports from the parent:

- Sheaf.CategoryTheory.SystemCoproducts
- Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
- Sheaf.CategoryTheory.SystemDerivedEvaluation
- Sheaf.CategoryTheory.SystemOrdinarySingleExtension
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
- Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
- Mathlib.Algebra.Homology.BifunctorShift

Their statements or instances remain available where needed through the preserved public
imports or the new step modules. SystemOrdinarySingleExtension's declarations are still
used in the parent via its preserved public imports; it is not a pruned dependency.
The parent no longer directly proves the old total-tensor/evaluation, resolution and
normalization steps. The relevant original dependencies remain recorded on the new
intermediate nodes: SystemCoproducts, TensorColimitsIndependentCoefficients,
SystemDerivedEvaluation and SheafRingCoefficientOrdinaryAdjunction serve the K-flat step;
KFlatResolutionIndependentCoefficients and SystemScalarCoherence serve the lower square;
NormalizedAdjunctionComposition and the derived adjunction nodes serve normalization.
The old lem-pur-derived-change-of-rings dependency is not separately used by the assembly:
the normalized scalar models and their existing computes fields already retain it.
The old lem-pur-system-level-left-extension existential package is not chosen or applied;
the proof uses the fixed singleton and scalar constructions directly. No whole module or
unit-route node is withdrawn. No adopted WeilConjectures declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original nine steps are mathematically consistent,
but the supplied declarations do not yet give whole-site singleton K-flatness, the
normalized transported singleton representative equation, or the lower-singleton square
as a directly applicable Lean theorem. Those exact steps are now independently stated,
with their full proofs in words and nodes. No unit statement or route is changed.

Edge cases checked in the statements and arguments: n=0, j=n, j>n, n=m, empty sites,
zero rings, arbitrary nonflat coefficient maps and unbounded complexes. The tensor formula
uses the actual scalar-first convention; commutativity converts c*a_j(b) to a_j(b)*c.
The representative equation does not require invertibility; hence its stronger version
for all complexes is valid without imposing K-flatness there.

## New nodes

- def-pur-system-singleton-scalar-comparisons attaches the unchanged fixed constructions
  extracted into SystemSingletonScalarBasic. It introduces no extra assumption or data.
- lem-pur-system-singleton-kflat carries original Steps 4--5, the whole-site flatness and
  total-tensor acyclicity test for the singleton.
- lem-pur-system-singleton-scalar-representative carries original Steps 7--8, normalized
  composite transposition and the identity right comparison on complexes.
- lem-pur-system-singleton-scalar-lower carries original Step 9, the balanced tensor
  lower-map calculation and transport through a flat-term K-flat resolution.

All new nodes inherit the parent's chapter/unit and blueprint ancestor, and record
LeanSearch, LeanFinder/Loogle and source grep searches. None restates the whole parent.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
