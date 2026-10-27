## What changed

Repair of the returned head e69069ed997: reviewer C-e6906 passed the packet,
but landing failed while applying a fix to a report basename that was not a
delivery path. The report is delivered at
coord/reports/F3/Sheaf.Paper.OrderedExchangeCoefficientComparison.md.
Compared the retained packet with the current source: the existing node differs
only in lean, proof, proof_deps and proof_origin; the four added modules are
still new. The first server recompile hit the fixed time limit. Profiling found
an expensive kernel conversion in lambda_existsUnique. Its proof now uses the
same local sheafification-instance setting as completedRlim and respects
transparency. The naturality proof also respects transparency locally. All five
modules compile successfully without warnings with lcompile.py --all on this
repair. The mathematical reduction and all public signatures are preserved.
The delivery command recreates the packet on the current sheaf-dag base.

Decomposed coefficientComparison into strict coefficient equations, reconstruction
equations, and the pointwise raw coefficient equation. The original theorem assembles
the seven equations, proves equality of natural transformations by extensionality,
and proves the witnessed base-change clause by unfolding its definition.

Moved the preceding public interfaces with identical signatures and definition bodies
into OrderedExchangeCoefficientData to avoid
an import cycle with the new proof obligations. The original module publicly imports
this module, retaining the same public API. No public signature or definition body
changes. The private limit-preservation proof uses an explicit identity isomorphism
in place of an expensive implicit instance conversion. See coord/changes/F3-ordered-coefficient-decomposition.md.

## Proved and sorry left

Closed the body hole of AlgebraicGeometry.Scheme.OrderedExchange.coefficientComparison
by a decomposition into named, strictly smaller statements. This is a decomposition,
not a completed mathematical proof; the net hole count increases by one.

Proved (reviewer correction, 2026-10-26, re-applied from the 2026-10-25 review): AlgebraicGeometry.Scheme.OrderedExchange.rawCoefficientEquation
(lem-weil-pbc-ordered-raw-coefficient-equation), by cancellation from the third strict
equation, the third and fourth reconstruction equations, and naturality of lambda.

The five original auxiliary holes remain in OrderedExchangeCoefficientData
(def-weil-pbc-ordered-coefficient-comparison-data):

- AlgebraicGeometry.Scheme.OrderedExchange.ordinaryRho_existsUnique
- AlgebraicGeometry.Scheme.OrderedExchange.rho_existsUnique
- AlgebraicGeometry.Scheme.OrderedExchange.restriction_complete
- AlgebraicGeometry.Scheme.OrderedExchange.phi_existsUnique
- AlgebraicGeometry.Scheme.OrderedExchange.rho_unit

Added holes:

- AlgebraicGeometry.Scheme.OrderedExchange.strictCoefficientEquations (lem-weil-pbc-ordered-strict-coefficient-equations)
- AlgebraicGeometry.Scheme.OrderedExchange.reconstructionCoefficientEquations (lem-weil-pbc-ordered-reconstruction-equations)

All seven remaining holes are whole proofs of named public theorems with source,
complete proof in words, and DAG attachments. No sorry appears inside a definition.

## No longer needed

No node, mathematical dependency, declaration or module is withdrawn. The original
public imports are retained transitively through the data module; the original
proof imports remain with the unchanged auxiliary proofs. The exploratory rho proof,
private helpers and added resolving-comparison imports are not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

The 2026-10-25 return itself reports no mathematical or compiler defect. Its sole
failure is the landing fix path
Sheaf.Paper.OrderedExchangeCoefficientComparison.md; the delivery report path
is the full coord/reports/F3 path recorded above. No launcher script is changed.

No statement was found false and no unit route is bypassed. A direct rho proof using
the existing model comparison reached expensive kernel conversions between counit
presentations, and is not claimed as proved. The delivered reduction instead makes
the existing coefficientComparison argument into independently stated steps, as the
stage-3 brief permits. Each step is a proper subset of the original conclusion. Edge cases retain the
original domains: arbitrary complete inputs, no finite-origin witnesses for the
strict or reconstruction equations, and pointwise cancellation in the full complete
subcategory. On an identity square these are the specified unit and counit formulas;
zero inputs and the zero ideal introduce no extra hypothesis.
The raw equation is pointwise; the delivered proof derives natural-transformation
equality and the witnessed identity itself.

## New nodes

- def-weil-pbc-ordered-coefficient-comparison-data: unchanged comparison interfaces.
- lem-weil-pbc-ordered-strict-coefficient-equations: first three strict-tower equations.
- lem-weil-pbc-ordered-reconstruction-equations: four reconstruction equations.
- lem-weil-pbc-ordered-raw-coefficient-equation: pointwise final cancellation (proved).

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
