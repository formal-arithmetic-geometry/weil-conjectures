## What changed

Replaced the hole in `Sheaf.Paper.CompletedConstantFiniteModuleComparison` by the
canonical limit-map construction and its finite projection identities. The theorem's
signature is unchanged. Added `Sheaf.Paper.CompletedConstantResidueData`,
`Sheaf.Paper.CompletedConstantFiniteProjection`, and
`Sheaf.Paper.CompletedConstantProjectionMaps`, constructing
the actual residue morphisms from scalar extension, their pure-tensor formula, scalar
linearity, module-map naturality and successor compatibility, for arbitrary completion
modules. Its compatible cone defines the fixed tensor-to-limit map. All these
constructions and identities have complete Lean proofs; none is chosen from an
unproved existence theorem.

Added `Sheaf.Paper.CompletedConstantComparisonIsIso` for the remaining invertibility
step. This step does not assert naturality or scalar-linearity and does not supply
maps or isomorphisms as unspecified witnesses. It concerns the map already constructed
independently of finiteness. The item's proof takes `asIso` of this map, rewrites its
finite projections, and applies the proved identities.

## Proved and sorry left

Closed the original body hole of
`AlgebraicGeometry.Scheme.completed_constant_finite_module_comparison` by a decomposition.
Added one hole:
`AlgebraicGeometry.Scheme.completedConstantComparisonMap_isIso`, node
`lem-weil-pbc-completed-constant-comparison-is-iso`.
Thus one original hole is replaced by one strictly narrower invertibility obligation;
this is a decomposition, not a net proof or a fully proved finite-module comparison.
No holes occur in definitions or in the projection construction.

Validation: `lcompile.py --all` accepted all five delivered modules in import order,
with no errors or warnings and with the compiler enforcing its per-file limit.
All profiling options were removed. The item signature was compared textually with
the repository version and is unchanged.

Proved `completedConstantProjection_exists`, `completedConstantProjection_spec`,
`completedConstantProjection_naturality`, `completedConstantProjection_step` and
`completedConstantComparisonMap_π`, with their construction and extensionality
helpers, including `constantScalar_compatibility` and `realization_hom_ext`.
These supply the actual map and all compatibility formulas without the
residual invertibility theorem.

## No longer needed

No existing module is withdrawn. No public import of the item is removed. The item now
uses only the projection-construction node and the invertibility node directly.
Completion Noetherianity, finite presentation, constant-section properties and
`ModuleCat.limit_flat_of_flat_quotients` remain needed by the invertibility step and are
retained in that node's proof dependencies; they are not pruned from the project.
The old direct dependencies
`lem-weil-pbc-adic-completion-noetherian`,
`lem-sc-noetherian-finite-module-finite-presentation`,
`lem-weil-pbc-constant-module-section-properties`, and
`lem-weil-pbc-limit-flat-modules` move to the residual invertibility node.
`lem-weil-pbc-adic-completion-mod-power` is used by the new projection construction
and retained for invertibility. `def-weil-pbc-completed-constant-realization-data`
is used by the construction as well as the unchanged statement.
`def-pur-sheaf-tensor-product` and its cochain-tensor module are not directly needed:
the proof uses the ordinary scalar-extension adjunction and pure tensors already
available in `CompletedConstantSheafReduction`. This removes only the old planned
direct dependency; it does not withdraw that shared tensor API or any declaration.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The earlier proof plan did not supply the explicit
semilinear maps, the scalar-ring comparison between the two quotient-module sheaves,
or the tensor-local extensionality argument needed to construct the comparison in
Lean. These parts are now implemented. Invertibility remains the finite-presentation
and tensor-limit step described in the original plan, with all its existing declared
ingredients retained. This delivery does not claim that finding those ingredients
alone proves that step.

The initial combined construction exceeded 60 seconds. Profiling led to replacing its
large two-field specification structure by a conjunction, using direct equality
composition instead of repeated unfolding, and making proved helpers locally
irreducible after their computation lemmas. The remaining independent parts were
split into the three modules above. The constant scalar-action identity was then
factored into a generic two-ring lemma, so its quotient specialization does not
repeat expensive scalar-structure conversions. No shared definition or existing interface was
changed for performance.

## New nodes

`def-weil-pbc-completed-constant-residue-data` records the quotient-ring action,
evaluation-semilinear residue map, generic sheafified constant-module maps, and the
local tensor extensionality lemma. All are proved.

`def-weil-pbc-completed-constant-finite-projections` constructs the actual finite
projections and proves their pure-tensor and completed-scalar formulas, for arbitrary
completion modules. All are proved.

`def-weil-pbc-completed-constant-projection-maps` records naturality, successor
compatibility, and the limit lift of the previously constructed finite projections. It contains
constructions and proved properties, with no hole.

`lem-weil-pbc-completed-constant-comparison-is-iso` records only invertibility of that
fixed map for finite completion modules. Its docstring and node give the full
finite-presentation, quotient-section and inverse-limit argument, including the
identification with the already constructed map. It has one public theorem hole.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
