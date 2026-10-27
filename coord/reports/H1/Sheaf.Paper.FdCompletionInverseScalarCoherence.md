## What changed

Replaced the sorry of `WeilConjectures.fdCompletionInverseScalarCoherence` by a
Lean assembly of integral descent inputs, the existing
`FdRawLocalization.rawLocalizationScalarCoherence`, and presentation transport of the
resulting inverse comparison to a morphism of the specified stage systems.
The original theorem signature and public imports are unchanged. The existing structures
retain their fields, whose large proof predicates are now named predicates with exactly
the original bodies; the performance repair is recorded below.

Added two strictly intermediate statements, one per new module. The integral statement
has no rational scalar family or rational coherence conclusion. The packaging statement
assumes the actual integral and rational comparisons, their normalized lift, unit and
three-field equation; it only transports their presentations and reverses the lift square.
The parent contains real categorical proofs of the inverse three-field cocycle and
both four-field contractions for any `StageSystem.Morphism`: cancel the source
associator in `Morphism.coh_inv`, combine the two inner functor images, apply naturality
of the outer inverse comparison, and use the target system's pentagon.

The three relevant existing modules and their signatures were read before introducing
these statements. The remaining gap is not the existence of another unnamed comparison:
it is transfer between the actual integral/presentation APIs and packaging on the
specified, uniquely normalized framework stage system. Both new statements have full
proofs in words and DAG nodes preserving the original integral and localization route.

Validation: an earlier predicate-only revision compiled in 53.1 seconds, but delivery
revalidation took 66 seconds; the family types were subsequently named as well.
The unchanged `RationalCoefficientCategoryComparison` consumer compiled cleanly in
15.2 seconds against the sandbox. The two new modules were compiled separately;
The final matched chi-family interface compiled cleanly in 43.5 seconds;
raw packaging last compiled in 15.1 seconds and integral descent in 53.8 seconds. No profiler or warning remains.

## Proved and sorry left

Closed the original hole in `WeilConjectures.fdCompletionInverseScalarCoherence`
(node `lem-fd-completion-inverse-scalar-coherence`). No sorry remains in the item module.
Both private categorical helpers, `inverseScalarCocycle` and `inverseScalarCoherence`,
are proved without sorry.

Added these two holes, each with exactly `:= by sorry` and its complete argument in
the docstring:

- `WeilConjectures.fdIntegralScalarDescentInputs`
  (`lem-fd-integral-scalar-descent-inputs`).
- `WeilConjectures.fdRawScalarComparisonPackaging`
  (`lem-fd-raw-scalar-comparison-packaging`).

This is a decomposition of one original hole into two smaller holes, not a claim of
net sorry reduction. Existing dependency holes are reused as instructed, and their
sources are unchanged. No data definition contains sorry or chooses an arbitrary
witness from a new existence theorem.

Edge cases were checked against each statement and the arrow directions: zero objects,
empty T, identity inclusions, repeated fields adjacent to a strict inclusion, all fields
equal, and every positive or negative shift. The calculations never assume strictness
or faithfulness of rational localization. Integral fullness is used only for its full
inclusions; no rational map is lifted back to an integral map.

## No longer needed

Removed these direct private imports from the item:

- `Sheaf.Paper.FiniteFreeConstructibleScalarTransport`.
- `Sheaf.Paper.QuotientScalarComparisonDescent`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`.
- `Sheaf.Paper.CompletedScalarShift`.
- `Sheaf.Paper.ScalarCompletionAssociator`.
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`.
- `Sheaf.CategoryTheory.SemilinearScalarLocalization`.

These modules are not asserted globally unnecessary: the normalized integral comparison
and inverse-cocycle dependencies still need their underlying mathematics. Their proofs
belong under the integral descent item, rather than being imported directly by this
assembly. No Lean module is withdrawn. No source-library declaration is removed.

At the parent DAG level, the direct uses of
`lem-fd-normalized-integral-completion-comparison`,
`lem-fd-integral-inverse-scalar-cocycle`,
`lem-fix-scalar-completion-associator` and `prop-weil-pbc-scalar-extension`
move below `lem-fd-integral-scalar-descent-inputs`; they are retained, not globally pruned.
The parent no longer needs the raw theorem's separate four-field conclusions: its
four-field equations follow directly from the assembled morphism's cocycle and the
stage-system pentagon. The raw theorem itself is still used for existence, shifts,
lift, unit and the three-field equation.

## Where the brief, the DAG or earlier work was wrong

The mathematical route is retained. The DAG's original short assembly treated several
presentation and restriction transfers as automatic; the declared Lean APIs distinguish
ambient, integral restricted and raw rational comparisons, and distinguish transition
from the uniquely specified stage-system transition. The two new statements isolate
these actual missing glue steps without changing any target or existing signature.

The historical source path `sk-def-trace/def-fd-trace-function.md` no longer exists in
`literature/blueprint/latest`. The current trace definition was read at
`sec-fourier-transform/sk-cor-plancherel/def-fd-trace-function.md`. It states the trace
function and finite-dimensional coefficient stalks, rather than the old expanded
coefficient-category proof. The complete agent-written comparison argument is preserved
in the existing item docstring and node; the new nodes explicitly identify that argument
as their proof origin, not as a quotation from the present blueprint.

Profiling found that kernel checking of the original large structure fields dominated
the compile. A complete diagnostic run type-checked the proof but took 127 seconds.
Named locally irreducible predicates now share the original formulas across generated structure
declarations; no file or proof was split to avoid the limit. Profiling also found 26 seconds of
local linter traversal; this module disables those lint passes after the unused-variable
and formatting checks were completed. Kernel proof checking and transparency remain enabled. The declaration-use search
found only AdicFiniteRealizationCocone and RationalCoefficientCategoryComparison, which
store the structure/use family or invoke the unchanged theorem. The latter also uses
the proof fields; its unchanged source compiled against the sandbox interface in
15.2 seconds, confirming ordinary downstream transparency of the named predicates.

No independent second reader was started, as required by the dispatcher brief.

## New nodes

`lem-fd-integral-scalar-descent-inputs`, module
`Sheaf.Paper.FdIntegralScalarDescentInputs`, isolates the common integral presentation,
its exact shifted comparison, actual quotient-cocone lift, inverse cocycle and unit.
It uses the existing normalized comparison, integral inverse cocycle and normalized
associator results; it supplies exactly the integral hypotheses of the already stated
raw-localization theorem.

`lem-fd-raw-scalar-comparison-packaging`, module
`Sheaf.Paper.FdRawScalarComparisonPackaging`, converts the already constructed raw
comparison into a morphism of the specified systems, transfers the prescribed shifts
and exactness, and inverts its integral lift. Its hypotheses supply the hard existence
and cocycle assertions, and its conclusion has no four-field formula.

LeanFinder, LeanSearch, Loogle and Mathlib grep were run; the results supplied only
ordinary scalar-completion lemmas and generic equality-transport or inverse-shift
primitives, not either project-specific presentation theorem. Blueprint searches for
scalar comparison and integral completion found no duplicate statement. The definitional performance repair is recorded in
`coord/changes/fd-completion-comparison-predicates.md`. It introduces eleven real family/predicate
definitions in the item (irreducible only locally) and explicitly unfolds them in the constructor proof. The old
and new fields are definitionally equal; no mathematical hypothesis or conclusion changes.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
