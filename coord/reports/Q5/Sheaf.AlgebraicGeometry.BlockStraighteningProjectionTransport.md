## What changed

The original theorem `AlgebraicGeometry.HilbertCoefficient.blockStraighteningProjectionTransport`
now has a complete combining proof. It uses the initial-jet calculation to form a
lower triangular evaluated Jacobian, computes its determinant as a product, obtains
a common affine geometric chart, and fills every original output field.

The stored projection clauses are proved from the existing coefficient-operator
base-change declarations. A private helper enumerates precisely the finite subset
of earlier generators, so the existing finite-family ideal-correction theorem
applies without adding unused generators. Noetherianity applies to the full target
series ring. Evaluation compatibility gives later-generator fixing; kernel image
containment gives zero in every coefficient; empty tests imply both operators are
the identity by their pointwise fixing clause. The pointwise formal-target proof
works on arbitrary inputs, not only images of the original coefficient map.

Existing definitions and structures were moved verbatim to `BlockStraighteningData`,
which the item publicly reexports. Their names, signatures and bodies are unchanged.
The new projection-free `BlockStraighteningGeometry` separates the geometric chart
from operator transport. It also records surjectivity of the center residue map,
which follows from its locally closed inclusion. The existing output structure and
the original theorem statement remain unchanged. There are no current direct Lean
importers of the item; its DAG parent remains unchanged and still needs the item.
Change record: `coord/changes/Q5-block-straightening-data.md`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.HilbertCoefficient.blockStraighteningProjectionTransport`
(node `lem-trf-block-straightening-projection-transport`) by decomposition.

Added three holes, all whole public theorem proofs in separate modules:

- `AlgebraicGeometry.HilbertCoefficient.blockStraighteningInitialJet`
  (`lem-trf-block-straightening-initial-jet`): vanishing, zero upper entries, and
  nonzero diagonal of the initial Jacobian; no geometric construction.
- `AlgebraicGeometry.HilbertCoefficient.blockStraighteningGeometricChart`
  (`lem-trf-block-straightening-geometric-chart`): common affine geometric chart,
  after vanishing and nonzero determinant are supplied; no operator transport.
- `AlgebraicGeometry.HilbertCoefficient.blockProjectionFirstTransport`
  (`lem-trf-block-projection-first-transport`): only first-exponent conjugacy for
  an already specified chart and operator, with no chart existence or projection
  hypotheses/conclusions.

The item has zero remaining holes. New modules have three holes in total. This is
a decomposition, not a net proof-count gain: one old hole closed, three new holes
added. The determinant computation and all projection clauses other than the
first-exponent conjugacy step are complete Lean proofs from existing declarations.
No definition contains a hole. The three unresolved statements each have the source,
a complete natural-language argument, a node, and an exact Lean signature.

Edge cases checked when stating the split: r=0 gives vacuous jet assertions and
empty determinant 1; the geometry uses an affine neighborhood with no new equations;
t=0 allows the same coefficient tests; an empty earlier-generator subset is
represented by Fin 0; an empty test family makes every input a kernel element;
residue fields need not be algebraically closed and the center need not be closed.

Validation: all five sandbox Lean files compiled through lcompile.py without
warnings; timings were 20.1, 4.5, 4.6, 4.5, and 5.8 seconds. The delivery tool
checks the final packet and axioms independently.

## No longer needed

No mathematical dependency from the old proof plan is pruned: its implicit Taylor
calculus, formal coefficient operators, finite-type Noetherianity and power-series
Noetherianity all remain needed, either in the combining proof or in a split step.
The original data imports are retained as public imports of the reexported data
module. The item's direct proof import of `Mathlib.RingTheory.FiniteType` is moved
to the geometric-chart step, where finite-type Noetherianity is required. No module
is withdrawn. No source-library declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was weakened or disputed. The existing seven-step proof
plan leaves substantial glue unstated: initial jets, the projection-free common
chart, and first-exponent conjugacy. These are now separate items; the rest is
explicit Lean. The generic ideal-correction theorem takes a Fin-indexed family,
whereas this item uses a bounded subset of the original generators; the private
finite-subset enumeration bridges these interfaces.

The paper was read online at
https://mahalex.net/teaching/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf
(printed pp.279--281, (9.7)--(9.8), Remarks 9.9--9.11). The algebraic interpretation
at arbitrary residue fields and stored-operator refinement follow the existing
parent node's argument; neither is claimed to be a literal theorem of BM. The
current blueprint unit and its realized route are unchanged.

## New nodes

`def-trf-block-straightening-data` attaches the existing concrete block definitions
and structures at their new module, and the projection-free geometric structure.
There is no unproved data construction.

`lem-trf-block-straightening-initial-jet` isolates step 1, before determinant
calculation. `lem-trf-block-straightening-geometric-chart` isolates steps 2--5 and
the affine/Noetherian part of step 6, excluding operator assertions.
`lem-trf-block-projection-first-transport` isolates the conjugacy calculation of
step 7. All inherit the original chapter, unit and blueprint ancestry. The parent
node records the actual combining proof and its dependencies.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
