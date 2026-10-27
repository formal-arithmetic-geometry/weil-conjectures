## What changed

Proved `AlgebraicGeometry.ProEtale.ModuleRingedComparison.section_tensor_representative_exists`
in `Sheaf.Paper.SectionDerivedRealization`. The proof builds the prescribed natural composite
on internal complex pairs, extends it by fully faithful precomposition with the termwise section
equivalence, transfers K-flat invertibility along its counit, and localizes the ordinary regular-unit
comparison. The signed-total map is constructed canonically from the ordinary natural comparison.
Its defining summand equations and the existing uniqueness theorem identify it with
the previously chosen normalized total isomorphism.

Used the proved ordinary naturality helper from `Sheaf.Paper.ProEtaleSectionModuleFunctors`
and the K-flat comparison helper from `Sheaf.CategoryTheory.InternalSectionTensorComparison`
through proof imports of their private declarations. Existing public imports and target statements are preserved.
The existing pullback descent proof now uses explicit resolution and naturality terms, reuses
its resolution witness, and uses a named specification for the uniquely selected qTensor.

In the unclaimed `Sheaf.Paper.SectionDerivedTensorData`, exposed actual-map APIs for the native
localization tensorator, total comparison and exact localization factor, including their component and normalization equations. The additivity theorem is public and used as a local instance.
These APIs keep large chosen constructions from repeatedly unfolding. The derived equivalence and conjugate tensor retain their original bodies.
The total functor now has a direct object field and the original maps and functor laws;
cochainTotalFunctor_eq proves by reflexivity that the whole functor is unchanged.
The existing flat-resolution proof uses the proved tensor-isomorphism helpers directly.

Factored the existing representative condition into its original normalization, either-argument
K-flat invertibility and regular-unit clauses. Expressed tensorUnit as its definitionally identical
regular single complex. Removed identity transports from localizedTotalComparison and
totalPullComparison; their old and new composites are equal by category identity laws.
The change record contains the old/new definitions and all direct declaration consumers:
`coord/changes/D7-section-total-comparison-identities.md`.

The original unclaimed SectionKFlatTensorComparison consumer failed on the equality between
the cached tensorator component and native μ. Its existing rewrite now also uses
internalLocalizationTensorMap_app; no signature changes. SectionTensorRightComputation
also needs that component equation and the proved canonical-total comparison equation
in its existing representative and localized-total calculations.

All five changed modules passed lcompile.py: SectionDerivedTensorData,
SectionDerivedRealization, SectionKFlatTensorComparison, SectionTensorRightComputation
and SectionDerivedTensorNormalization. SectionDerivedRepresentativeSquare and
SectionResolvingOplaxConstraintData compiled unchanged and are not included in the packet.
The normalized-total consumer needed its obsolete identity rewrites replaced by
unfolding the two canonical maps and reflexivity. All consumer signatures are preserved.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.section_tensor_representative_exists`
(node `lem-pd-section-tensor-representatives-exists`).

Added zero holes and split off zero statements. There are zero remaining sorry declarations
in any of the five changed modules. No new modules are added. This closes the item proof
from the existing library inputs; it does not claim their entire transitive axiom closure is closed.

## No longer needed

No imports, modules or declarations are withdrawn. The proof no longer needs these dependencies
of the expanded node plan:

- `lem-pd-conjugate-tensor-localization-counit`: the actual natural composite and fully faithful
  precomposition supply the normalization directly.
- `lem-pd-ringed-kflat-native-model-identification`: use the native internal localization tensorator
  on either K-flat argument, then transfer by the counit.
- `lem-trf-exact-tensor-equivalence-kflat-homotopy`: the existing termwise equivalence and its
  counit suffice; no separate inverse tensor or homotopy package is required. Removed only its
  obsolete top-level tool_uses entry, retaining the others in order.

These are removals from this node's proof dependencies only. The existing modules remain
available to their other consumers. The signed-total and derived-monoidal unit inputs remain
used, and the blueprint unit route is preserved. Quarantined parents and their attachments are
preserved; no withdrawal is inferred from a missing current Lean file.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. A concurrent stage-1 delivery expanded the existence node
during this session. Refreshed its statement and review metadata, then updated only its Lean
proof route and obsolete tool use. The new route proves the same three clauses, including the
all-unbounded representative equation, either-argument K-flat invertibility and regular unit.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
