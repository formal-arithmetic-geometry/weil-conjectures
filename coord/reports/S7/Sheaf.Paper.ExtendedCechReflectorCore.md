## What changed

Replaced the hole in `Sheaf.Paper.ExtendedCechReflectorCore` by a reduction using the
independent finite-Cech unit-idempotence theorem. Proved exact-cover conservativity for
morphisms of unbounded derived module sheaves, normalized augmented-RHom restriction,
transport of both idempotence maps, and the universal mapping bijection by functoriality
and inverse units. Naturality is reproduced as a private proved calculation to avoid an
import cycle through the parent completion model.

Added `Sheaf.Paper.ExtendedCechCompleteUnitCriterion`, isolating the single-object geometric
criterion that local completeness is equivalent to invertibility of its actual completion
unit. Its docstring and node give the positive-localization filtration and localized
contraction proof, including empty lists, zero and unit ideals, zero rings and empty covers.

Updated the core node to follow the actual proof. The change record is
`coord/changes/extended-cech-reflector-fixed-objects.md`. No existing declaration signature,
definition, instance, target, or public import changes, and no consumer adaptation is needed.

Validation: the criterion compiled in 9.5 seconds; the final assigned module compiled in
53.6 seconds with no errors or warnings through `lcompile.py`. Import-direction checks
confirm that the finite-Cech idempotence, RHom restriction and finite generating-cover
dependencies do not reach the assigned core. A text comparison confirms that the original
public theorem signature is preserved verbatim.

## Proved and sorry left

Closed the original hole in `CategoryTheory.ringedExtendedCech_reflector_core` (node
`lem-weil-pbc-extended-cech-reflector-core`) by a complete proof from the new criterion and
existing declarations. The item now contains zero holes.

Added one hole: `CategoryTheory.ringedExtendedCech_complete_iff_unit_isIso`, in
`Sheaf.Paper.ExtendedCechCompleteUnitCriterion`, node
`lem-weil-pbc-extended-cech-complete-unit-criterion`. Its entire proof is `by sorry`.
This is a decomposition: one hole closed, one hole added, net zero. The remaining statement
is a criterion for a single object and contains neither completeness of all completion
values nor the universal mapping bijection; the item proves those from the criterion using
independently established idempotence and an explicit categorical argument.

The finite-Cech idempotence theorem is already proved in its own module; its existing
remaining tensor-cone dependency is unchanged. No hole is inserted in a definition.

## No longer needed

No existing imports were removed, no modules withdrawn, and no pre-existing dependency
nodes pruned: the original core had no proof dependencies. Its new proof only imports the
criterion, finite ideal generating cover, finite-Cech unit idempotence, RHom restriction,
evaluation naturality and the ordinary sheaf/derived isomorphism criteria it actually uses.

The core does not need the derived-global-sections mapping argument proposed in the older
parent report: its universal mapping bijection follows directly from naturality,
idempotence and invertibility of the target's unit. No import of
`Sheaf.Algebra.Homology.RhomGlobalSections` is needed. The parent completion model,
`RingedCechCompletionHomInjective`, `RingedCechCompletionRestriction`,
`RingedKoszulCompletionReflector` and `UnitPowerCompleteness` are not used to prove this
core, as they reach it and would introduce a cycle. Their declarations remain intact.
The fixed-object criterion still needs localization contraction and the finite positive
filtration, so no mathematical dependency of that geometric argument is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The core's proof plan had no declared dependencies, although an independent finite-Cech
idempotence theorem and a finite generating cover have since been proved. These provide a
substantial part of the argument. Several newer apparent reflector criteria import the
parent and cannot serve as dependencies of this core. The reduction explicitly avoids
that circular route and retains the unit's actual augmentation normalization.

The existing node's geometric proof is retained in the new criterion, rather than replaced
by a new assertion of the same reflector property. The universal mapping clause is now
proved by the formula `F.map f ≫ inv (eta L)` and by cancellation after applying F.
The fixed unit-level route is preserved.

## New nodes

`lem-weil-pbc-extended-cech-complete-unit-criterion` states the single-object fixed-unit
criterion from Stacks Tags 099B and 099F. The new module has one named theorem and one hole.
LeanSearch, LeanFinder, Loogle, library/Mathlib grep and blueprint search found no usable
independent declaration. The change record is
`coord/changes/extended-cech-reflector-fixed-objects.md`.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
