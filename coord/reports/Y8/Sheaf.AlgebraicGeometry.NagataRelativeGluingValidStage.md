## What changed

Replaced the proof of `AlgebraicGeometry.nagataRelativeRawStage_le_validStage`
with an application of `le_directedFiniteUpperBound`, using the fixed
`R.base.boundPair_le` and `Finset.mem_insert_self`. The raw stage is explicitly
inserted into `nagataRelativeGluingEqualityStages`, so the selected upper bound
bounds it. This is the argument already recorded in the theorem's docstring;
all definitions, signatures, visibility and imports are unchanged.

Validation: the complete module compiled without errors or warnings through
`lcompile.py` (9.8 seconds). The argument works for a preorder without
antisymmetry, for empty chart/relation index types, and when the two orders on
`I` differ: the raw stage remains an inserted member and the upper-bound theorem
uses the original preorder and the supplied auxiliary linear order separately.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.nagataRelativeRawStage_le_validStage`
(node `def-nagata-relative-gluing-valid-stage`).

Zero holes remain in the item module. Zero holes added; zero split off.
The existing dependency `le_directedFiniteUpperBound` remains a separately stated
obligation in `Sheaf.Order.DirectedFiniteUpperBound`; this delivery uses its
recorded interface as intended by stage 3.

## No longer needed

None. No imports were added or removed. The existing public construction and
statement dependencies remain; the existing upper-bound import supplies exactly
the theorem used. No unit step, node or module is bypassed by this proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The assigned module has only the short
raw-stage inequality as a hole; its docstring already gives a complete route
through the existing upper-bound theorem. No geometric gluing identities are
asserted or needed for this inequality. No new nodes or definition repairs
were necessary.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
