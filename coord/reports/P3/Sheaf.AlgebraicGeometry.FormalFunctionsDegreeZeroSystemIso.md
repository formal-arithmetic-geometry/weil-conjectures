## What changed

Proved `AlgebraicGeometry.formalFunctions_degreeZero_systemIso` with its signature unchanged.
The proof constructs a canonical comparison at each level from Mathlib's
`rightDerivedZeroIsoSelf`, sections of `tensorPullbackObjUnitToUnit`, and restriction
of scalars. Private proved helpers establish compatibility of the unit maps with
composition and the infinitesimal transitions, and naturality on sections.
`NatTrans.ofOpSequence` assembles the comparisons and componentwise invertibility
makes the resulting transformation an isomorphism.

Reused the existing proof-only import `ModuleCohomologyFMapZeroAugmentation`
and added `SchemeModulesEnoughInjectives`. Specializing
`Scheme.Modules.ModuleCohomologyFMapData.map_zero_augmentation` to the data chosen
by `moduleCohomologyFMap` gives the canonical augmentation square. The top restriction
is the identity by `presheaf.map_id`. The duplicate augmentation module and node
from the returned delivery have been removed, and the item's DAG step 3 and
proof dependencies now name the existing zero-augmentation obligation.
No existing statement, definition, or public import changed. The unit's route is kept.
The proof-elaboration commands are recorded in
`coord/changes/formalFunctions_degreeZero_systemIso-proof-scope.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.formalFunctions_degreeZero_systemIso`
(node `lem-weil-pbc-formal-functions-degree-zero-system-iso`).

No new hole is added and no `sorry` remains in the delivered module.
All private helpers are proved. The proof reuses the existing obligation
`AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_zero_augmentation`
(node `lem-weil-pbc-module-cohomology-fmap-zero-augmentation`).
Existing dependency holes are unchanged. One original hole is closed, zero are added.

## No longer needed

Removed the direct proof import `Sheaf.Paper.HigherDirectImagePresheaf`
(node `lem-weil-pbc-higher-direct-image-presheaf`): the system comparison involves no
higher-direct-image presheaf or stalk identification. It remains transitively present
through the statement module, so this does not claim that the whole target closure
prunes it.

Removed the direct proof import `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties`
(node `lem-weil-pbc-module-cohomology-fmap-basic-properties`) and the corresponding
item proof edge: the degree-zero comparison now uses canonical augmentation instead
of unrelated existential isomorphisms. This module remains transitively needed for
linearity in `FormalFibreCohomology`; it is not globally pruned by this delivery.

The tensor-pullback structure-sheaf node, tensor pullback definition, and formal fibre
system definition remain needed. No other planned node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The stated degree-zero clause of `moduleCohomologyFMap_basic_properties` quantifies
existential comparison isomorphisms separately for each h-map. It does not identify
them with the canonical augmentation or ensure coherence across adjacent transitions.
Thus its current signature cannot directly justify the DAG's instruction to assemble
the identifications into an inverse-system isomorphism. The existing `ModuleCohomologyFMapData.map_zero_augmentation` supplies
that canonical square after specialization to the chosen resolution data and
simplification of the identity restriction at top. The previous delivery unnecessarily
duplicated this obligation; reviewer X-308a9 identified the reusable declaration.
No existing interface was changed.

The source files are not populated under this clone's literature directory. Read
Stacks `cohomology.tex` (Remark 01FB, Equation 01FC) from the existing local literature
copy under `/home/ubuntu/work-bp/sheaf/literature/stacks-project/`.

Edge cases: the canonical level construction and square apply to zero modules and
empty schemes and impose no properness, finite generation, or nonzero-ring hypothesis.
The natural index starts at zero (positive infinitesimal level one), and naturality is
proved at every adjacent index without assuming stabilization.

## New nodes

None. Removed the returned delivery's duplicate node
`lem-weil-pbc-module-cohomology-fmap-degree-zero-augmentation` and its module
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapDegreeZeroAugmentation`.
The existing zero-augmentation node is reused. The proof-elaboration command record is
`coord/changes/formalFunctions_degreeZero_systemIso-proof-scope.md`.
No forced adaptations are needed.

## Earlier second reading (a previous round; superseded)

The previous second reading approved a duplicate augmentation obligation and is
superseded by the maintainer's return X-308a9. Repair C5 removes that module and node,
uses the existing zero-augmentation theorem specialized to the chosen resolution
data, and proves the restriction at top is the identity. No new node or hole is added.
The target signature and unit route are unchanged. A fresh independent second reading
of the repaired delivery remains pending.

## Second reading by P3

1. **Diff and interfaces.** Compared the delivered module with the repository version.
   The target theorem's signature and all existing public declaration signatures are
   unchanged; the added options, local instance, and private helpers affect only proof
   elaboration. The DAG node changes only its recorded proof route and dependencies.
   Verdict: passes.

2. **Compilation and axioms.** Compiled the delivered module with the mandated
   `lcompile.py` command. It has no errors, no warnings, no `sorry`, and no forbidden
   declarations. The construction uses canonical derived-functor and tensor-pullback
   isomorphisms; no data is selected from an underdetermined existence theorem.
   Verdict: passes.

3. **Statements and split-offs.** There are no new statements or split-off holes.
   The existing zero-augmentation theorem is used at the exact chosen resolution data;
   the identity restriction at the top open is proved by `map_id`. The level maps and
   their transition square are therefore true with exactly the needed strength, and
   the edge cases (zero modules, empty schemes, and level zero) impose no extra
   hypotheses. Verdict: passes.

4. **Pruning and route.** The proof uses the canonical augmentation dependency and
   removes the direct imports of higher-direct-image and basic-properties modules that
   it does not use. The remaining tensor-pullback, formal-fibre, and zero-degree
   resolution dependencies agree with the unit route; the corresponding node
   `proof_deps` and `proof` fields match the Lean proof. Verdict: passes.

5. **Delivery metadata.** The report lists one original hole closed and no holes
   added, records the removed duplicate obligation, and includes the proof-scope
   change record. No definition or target statement changed, and no forced adaptation
   is present. Verdict: passes.

I changed only this report section during the second reading; the proof and DAG are
otherwise accepted as delivered.
