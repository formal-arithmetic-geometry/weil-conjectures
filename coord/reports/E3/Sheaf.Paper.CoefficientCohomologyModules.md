## What changed

Filled all six proof holes of `Sheaf.Paper.CoefficientCohomologyModules` without changing
any declaration's type or any definition. The first three proofs project the appropriate
finiteness clause from membership. Qbar cohomology finiteness uses
`Module.Finite.base_change`. The stage-map formula uses naturality and inverse cancellation.
The change-of-stage formula uses `fieldDerivedHomologyIso_tower` and inverse cancellation.

Recorded these arguments in the existing node's proof fields. Removed the unused public
import `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and made
`Mathlib.RingTheory.TensorProduct.Finite` a proof-only import. Change record:
`coord/changes/E3-coefficient-cohomology-imports.md`. The downstream scan finds no consumers.
The original algebraic-closure parameters are explicitly retained in the three Qbar proofs.

## Proved and sorry left

Closed 6 of 6 holes, all attached to `def-weil-coefficient-cohomology-modules`:

- `DerivedCategory.coefficientFiniteCohomology_finite`
- `DerivedCategory.coefficientFgCohomology_finite`
- `DerivedCategory.coefficientFdCohomology_finite`
- `DerivedCategory.coefficientQbarCohomology_finite`
- `DerivedCategory.coefficientQbarCohomology_map_stage`
- `DerivedCategory.coefficientQbarCohomology_changeStage`

Holes added: 0. Split off: 0. Sorries left in delivered Lean: none. This proves the module
from its existing dependencies; the normalized derived comparison and its tower theorem
remain the already stated dependencies of the library, rather than new obligations here.

## No longer needed

Removed the import of `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: no finite-ring
cardinality result is needed, since the finite cohomology theorem is part of subcategory
membership. The node `def-weil-l-adic-coefficient-extension` remains a statement dependency
for its coefficient-ring constructions, already imported through `FiniteFieldFiber`.

Privatized the import of `Mathlib.RingTheory.TensorProduct.Finite`, used only by a proof.
No other import or declared dependency is pruned: the coefficient subcategories,
finite-stage category, cohomology comparison, and tensor tower comparison are all used.
The proof does not use the common-stage Hom-colimit theorem, shift lemmas, or triangulated
structure, but their containing module still supplies required stage-category definitions.
No unit statement or unit proof step is bypassed; the unit has empty realized lists.

## Where the brief, the DAG or earlier work was wrong

The existing node had empty proof and proof_deps fields although its Lean module had six
proof obligations with complete plans in their docstrings. Those plans suffice, and the
node now records the actual Lean argument and dependencies. No mathematical statement or
definition repair was necessary. In the last proof the composite inclusion is definitionally
the direct inclusion; `erw` is needed to expose this equality when rewriting the tower law.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
