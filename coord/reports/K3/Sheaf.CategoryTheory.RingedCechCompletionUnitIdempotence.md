## What changed

Replaced the hole in `CategoryTheory.ringed_cech_completion_unit_idempotence` by the
K-flat tensor/Hom argument, keeping its statement and public imports unchanged.
The private helpers prove bounded-flat K-flatness of the ring complex and each
localization factor, inductive K-flatness of the ordered Cech tensor, invertibility
of the specified derived Hom unit, the cone-to-projection comparison, and the
categorical implication from tensor projections to both specified completion-unit
maps. The last implication uses naturality of the existing proved
`CategoryTheory.KFlatRHom.curryIso`, with each augmentation in turn; it does not
assume a new compatibility theorem for the unit.

Added `Sheaf.CategoryTheory.RingedCechTensorIdempotence` with the single remaining
ordinary tensor-cone acyclicity statement, and updated the parent DAG proof route.
The new statement removes all derived target objects and unit maps: it is exactly
the concrete localization-contraction and finite-filtration step, strictly a part
of the old obligation. Its docstring and node describe the contraction signs,
cancellation of the ring-term pair, finite filtration, and empty-list case.

## Proved and sorry left

Closed the original body hole of
`CategoryTheory.ringed_cech_completion_unit_idempotence` (one original hole).
There are zero holes in the item module and no holes in its private helpers.
Added one hole:
`CategoryTheory.ringed_cech_tensor_augmentation_cone_acyclic`, in
`Sheaf.CategoryTheory.RingedCechTensorIdempotence`, node
`lem-weil-pbc-ringed-cech-tensor-idempotence`.

This is a decomposition: one hole closed, one strictly smaller hole added, net zero
holes removed. The actual tensor-cone calculation remains unproved. No definitions
are changed, no data are chosen from an unproved existence result, and no axioms
are added.

Validation: the server compiled the new tensor-cone module in 13.4 seconds and
the complete item module in 44.5 seconds, with no errors or warnings. The new
statement explicitly binds the native colimit and tensor-totalization instances
to keep typeclass search independent of the expanded Cech expression. All DAG
proof-dependency unions and verbatim Lean statement records were checked.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the existing currying
  theorem already has the required universe-polymorphic derived interface.
- `WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality`: naturality
  of currying suffices; no separate identification of units through currying is used.
- `WeilConjectures.Algebra.Homology.HomTensorTotal`: use the existing proved
  `Sheaf.Algebra.Homology.KFlatRHomCurrying` interface.
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`: this is encapsulated by currying.
- `Sheaf.CategoryTheory.RingedExtendedCech`: already publicly reexported through
  the unchanged `RingedKoszulSystem` statement import.
- `Sheaf.Paper.RingedLocalizationRHomCalculus`: its large restriction-coherence
  interface is unnecessary; only proved localization flatness from
  `RingedLocalizationModels` and natural K-flat currying are used.

The parent no longer directly uses these old proof dependencies:
`lem-weil-pbc-ringed-localization-rhom-calculus`,
`lem-sc-derived-hom-tensor-total`,
`lem-sc-hom-complex-unit-evaluation-naturality`,
`def-pur-derived-internal-hom`, and `lem-pur-hom-kflat-into-kinjective`.
The last two remain needed transitively by the public definitions and currying;
this delivery makes no claim that these modules can be withdrawn globally.
No module is deleted or withdrawn. No blueprint unit statement or realized step
is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or definition repair. The original plan can be shortened
at the derived categorical stage: invertibility of the two specified unit maps
requires only naturality of the proved currying isomorphism and invertibility of
the existing ring-Hom unit; a separately formalized evaluation-normalization
coherence square is unnecessary. The finite localization argument remains a real
unproved step and is reported as such.

## New nodes

`lem-weil-pbc-ringed-cech-tensor-idempotence`, module
`Sheaf.CategoryTheory.RingedCechTensorIdempotence`, states acyclicity of the ordinary
total tensor of the actual Cech complex with its augmentation cone. It is the
concrete first step of the parent proof, with no derived-category instance or
test-object parameter. The empty list, zero and invertible generators, zero ring,
and empty site satisfy the stated contraction/filtration argument. The private elaboration-context change is recorded in
`coord/changes/K3-cech-idempotence-proof-context.md`; no existing signature or
definition was changed.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
