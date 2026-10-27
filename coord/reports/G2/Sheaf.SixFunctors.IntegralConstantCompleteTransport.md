## What changed

The target theorem is assembled pointwise from two strictly smaller transport statements. Added the pointwise completeness and pointwise Hom-bijection modules, with the source tower and small-site transport recorded in their docstrings and DAG nodes.

## Proved and sorry left

The original theorem `integralConstantCompleteTransport` is reduced to the two pointwise declarations. Two new proof holes remain:

- `integralConstantCompleteTransport_complete`;
- `integralConstantCompleteTransport_hom`.

## No longer needed

No imports or existing nodes were removed. The target proof uses only the two new pointwise modules and `ConstantSemilinearGeneratorComparison`; no additional route dependencies were imported.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan did not provide a Lean declaration identifying the specified `H` with the constant-completion Hom equivalence on arbitrary constructible inputs. The target was therefore decomposed into pointwise completeness and pointwise Hom bijection statements, each strictly below the universal conjunction.

## New nodes

- `lem-sf-integral-constant-complete-transport-complete`
- `lem-sf-integral-constant-complete-transport-hom`

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
