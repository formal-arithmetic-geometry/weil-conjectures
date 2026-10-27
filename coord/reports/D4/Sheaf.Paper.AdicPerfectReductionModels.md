## What changed

The original theorem `AlgebraicGeometry.Scheme.adicPerfectReductionModels` now has
a complete conjunction proof. Its K-projectivity component is proved by
`adicPerfectReductionModels_kprojective`: additive termwise realization preserves
the upper bound, and Mathlib's bounded-above projective-complex criterion applies.
The concrete term-projectivity and normalized comparison calculations are isolated
as two separately stated obligations.

The five existing ordinary-complex definitions and the proved scalar cone equation
are relocated verbatim to `Sheaf.Paper.AdicPerfectReductionModelComplexes`, publicly
reexported by the assigned module. This permits the new proof modules to import
the definitions without a cycle. Their names, signatures, bodies and visibility
are unchanged. The change record is
`coord/changes/D4-adic-perfect-reduction-definition-module.md`.

## Proved and sorry left

The one original hole is closed in
`AlgebraicGeometry.Scheme.adicPerfectReductionModels`. The new theorem
`AlgebraicGeometry.Scheme.adicPerfectReductionModels_kprojective` is proved from
termwise projectivity, preservation of the upper bound, and
`CochainComplex.isKProjective_of_projective`.

Two new holes remain, so this delivery is a decomposition, not a net proof:

- `AlgebraicGeometry.Scheme.adicPerfectQuotientComplex_terms_projective`, node
  `lem-sfb-adic-perfect-quotient-terms-projective`, in
  `Sheaf.Paper.AdicPerfectQuotientTermsProjective`. It asserts only termwise
  projectivity, with no boundedness or derived comparison.
- `AlgebraicGeometry.Scheme.adicPerfectReductionModels_compatibility`, node
  `lem-sfb-adic-perfect-reduction-models-compatibility`, in
  `Sheaf.Paper.AdicPerfectReductionModelsCompatibility`. It asserts the concrete
  object comparisons and their normalized successor square, without K-projectivity.

Actual counts: one original hole closed, two holes added, zero holes in the
assigned module, two holes in the delivery. Both remaining statements have full
proofs in words and include the zero-complex, zero-ring, unit-ideal and empty-slice
edge cases. No data is chosen from an unproved existence theorem.

## No longer needed

No mathematical module or unit-route node is pruned. The original public import
`Sheaf.Paper.AdicResidueLiftComparisons` moves to the definitions module and
remains publicly visible through it. The original public Mathlib K-projectivity
import stays in the assigned module.

The assigned theorem directly needs only the new K-projectivity and comparison
lemmas. Its old K-flat, derived-change, exact-evaluation and scalar-composition
proof dependencies are assigned to the appropriate new nodes, not discarded.
Mathlib directly supplies the bounded-above criterion; no duplicate of that
criterion is introduced. No source-library declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The exact coefficient-slice
term-projectivity calculation is not supplied by the existing large pro-etale
site projectivity theorem without additional transport. The existing residue
comparison isomorphisms also do not by themselves assert the normalized successor
square. Those two concrete calculations are the remaining obligations.

## New nodes

`lem-sfb-adic-perfect-reduction-models-kprojective` records the proved reduction
from termwise projectivity and the preserved upper bound to K-projectivity.

`lem-sfb-adic-perfect-quotient-terms-projective` records projectivity of the actual
quotient terms on the weakly contractible coefficient slice. It has no finite
bounds and no derived assertion.

`lem-sfb-adic-perfect-reduction-models-compatibility` records only the coherent
K-flat computation of the completed constant model's derived reductions.

The existing definitions node's Lean attachment follows its verbatim relocation.
The existing parent node's proof dependencies follow the new conjunction proof.
Change record: `coord/changes/D4-adic-perfect-reduction-definition-module.md`.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
