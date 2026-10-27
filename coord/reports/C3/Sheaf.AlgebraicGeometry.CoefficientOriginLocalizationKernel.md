## What changed

Completed the proof of `AlgebraicGeometry.ProEtale.coefficientFixed_localization_kernel_origin`
from two geometric steps: epimorphy of the canonical closed unit, and comparison origin
of its kernel. The first step requires no classical-origin hypothesis. The second step
asserts only the kernel conclusion. Their proofs remain separate named obligations.

The proof uses `Adjunction.leftAdjointUniq` and its unit formula to transport both
conclusions to the supplied arbitrary adjunction. Its unit is the canonical unit followed
by an invertible direct-image morphism. Epimorphy survives this postcomposition, and
`kernel.mapIso` transports essential-image membership. The original theorem's signature
is unchanged.

Added `CoefficientFixedClosedUnitEpi` and
`CoefficientFixedLocalizationKernelComparison`, and updated the item's DAG proof to
match. The former constructs the canonical adjunction using Mathlib's sheaf adjunction;
all definitions have complete bodies.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.ProEtale.coefficientFixed_localization_kernel_origin` by reduction.
This is a decomposition, not a net reduction in holes: one hole closed and two added.

The remaining holes are:

- `AlgebraicGeometry.ProEtale.coefficientFixed_closed_unit_epi`
  (`lem-pe-coefficient-fixed-closed-unit-epi`), the epimorphy step without any
  comparison-origin assumption or kernel assertion.
- `AlgebraicGeometry.ProEtale.coefficientFixed_localization_kernel_comparison`
  (`lem-pe-coefficient-fixed-kernel-comparison`), the open-extension-by-zero comparison
  step, asserting only essential-image membership of the canonical kernel.

No `sorry` remains in the assigned module, and no definition contains `sorry`.

## No longer needed

The assigned module no longer directly uses
`lem-sf-proetale-open-closed-sequence` or
`lem-cbc-proetale-extension-zero-comparison`. Their coefficient-sized versions are the
geometric arguments recorded by the two new nodes, so neither old dependency is
claimed prunable transitively. No prior Lean import or existing module was removed.

## Where the brief, the DAG or earlier work was wrong

The existing `exact_openClosedSequence` and extension-by-zero comparison declarations
use the module universe `u+1` tied to the scheme universe `u`. This item instead has the
independent coefficient universe `max v (u+1)`, so those declarations do not directly
instantiate. The categorical arbitrary-adjunction transport is now complete; the two
coefficient-sized geometric steps remain. Restriction to the canonical adjunction alone
would retain the entire geometric conjunction, so the delivered reduction separates its
two actual conclusions instead.

All files compiled without errors or style warnings before delivery. The two new
statements have source/proof docstrings, retain quasi-compactness of the complementary
open, and discuss the empty-open and empty-closed boundary cases.

## New nodes

`lem-pe-coefficient-fixed-closed-unit-epi` records the scalar-linear local-surjectivity
step of Stacks Tag 09AH for the canonical closed unit. It is independent of classical
origin of the open restriction.

`lem-pe-coefficient-fixed-kernel-comparison` records the kernel identification from
Tag 09AH followed by extension-by-zero comparison from Tag 09AF. Neither new statement
reasserts the original conjunction or its arbitrary-adjunction quantifier. No change
record is needed: no existing definition or statement was changed.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
