## What changed

Proved the formal adjunction argument in `Sheaf.Paper.EtaleSystemCofinalMate`:
`cofinalMate_hom`, `cofinalMate_counit`, `cofinalMate_conjugate`,
`cofinalAdjunction_comp_assoc`, `cofinalCompositor_conjugate`, `cofinalMate_comp`,
and `cofinalSupport_mates` are complete private proofs. They derive the Hom formula,
counit identity and rho cocycle from geometric support data and its h cocycle.
The original theorem now combines these proofs with two separate geometric lemmas.

Moved the original interface prefix verbatim to `EtaleSystemCofinalData`, re-exported
publicly from the original module, to allow the geometric lemmas to import their
interfaces without a cycle. All public signatures and definition bodies are unchanged.
The earlier quotient-tower/local-field proof remains proved. See
`coord/changes/C9-etale-cofinal-geometric-extraction.md`.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Etale.SystemProjection.etaleSystemCofinalMate`
from the two geometric statements, using the complete formal proof described above.
The item module has zero sorry. This is a decomposition, not a net proof: one hole
closed and two added (net minus one). The new holes are:

- `AlgebraicGeometry.Etale.SystemProjection.etaleCofinalSupport_realization`, node
  `lem-pur-etale-cofinal-support-realization`: geometric existence and evaluation
  normalization, retaining the projection invertibility and coefficient cocycle.
- `AlgebraicGeometry.Etale.SystemProjection.etaleCofinalSupport_composition`, node
  `lem-pur-etale-cofinal-support-composition`: geometric h cocycle from the recorded
  normalizations and the explicitly assumed projection cocycle.

Each is one public named theorem in its own module, with a complete source-based
natural-language proof. Neither states any right-adjoint mate formula or rho equation.
The first is an existence result, the second a compatibility result for supplied data.
No data definition is chosen from either unproved theorem; the main result is a
proposition and merely eliminates the existential.

Validation: the generic mate proof compiled independently, then the original full
item compiled with those proofs. The extracted modules and main reduction compile;
the original consumer declarations were checked unchanged. An independent consumer compile
set, containing these same four packet modules, has been submitted; an earlier consumer
attempt timed out without a Lean error. Final delivery preflight is required.

## No longer needed

No mathematical dependency of the parent is pruned globally. Geometric dependencies
now belong to the two new items. The main proof uses Mathlib conjugateEquiv composition
and whiskering instead of an elementwise expansion of concatenated Hom chains.
All original public imports remain visible through the data module. No source-library
module or declaration is removed. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing `Theory` structure records normalized constructions but does not contain
coefficient-projection invertibility or its cocycle. The geometric composition split
therefore takes both hypotheses explicitly, and realization retains them from the
projection theorem. Inferring the cocycle from `Theory` alone would be unjustified.

The two geometric steps remain substantial transport and derived-functor arguments;
Mathlib adjoint uniqueness closes only the formal steps. Equality after evaluating a
derived morphism is not used as a faithfulness principle. The composition proof uses
actual natural transformations and conjugateEquiv.

## New nodes

`def-pur-etale-system-cofinal-data` records ownership of the unchanged extracted
interfaces. `lem-pur-etale-cofinal-support-realization` isolates parent proof steps
1--2. `lem-pur-etale-cofinal-support-composition` isolates parent step 3. The original
node now follows those steps by the completed formal mate proof and the existing
local-field proof. The positive-ramification definition attachment points to its new
module. Unit routes are unchanged: no unit statement or step is bypassed.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
