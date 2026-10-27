## What changed

Replaced the body of
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints.section_resolving_oplax_unit_models`
with a complete Lean proof from the existing representative hypotheses and one
new localization-unit lemma. The public signature and public imports are unchanged.

Private, proved helpers establish naturality of the regular-unit arrows, all
six unit-edge squares and both opposite branches, the eight vertex-isomorphism
clauses, and resolving membership of the degree-zero regular module. The second
vertices are invertible by the third edges and cancellation of mapped unitors;
the first vertices then follow from the second edges and the invertible scalar
unit. This avoids needing a resolving-preservation theorem for pullback.

Added proof imports of
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`,
`Sheaf.Paper.SectionRepresentativeTensorArrow`, and the new
`Sheaf.Paper.SectionLocalizationUnitConstraints`. The first identifies independent
and canonical tensorRight functors for the termwise flatness test; the second
supplies tensorator naturality and the scalar-unit comparison.

Server compilation succeeded for both modules: 19.4 seconds for the item and
3.9 seconds for the new statement module. No shared interface or consumer changes
are required. The two DAG records describe the actual dependency route.

## Proved and sorry left

Closed the original local hole in
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints.section_resolving_oplax_unit_models`.
Its proof is complete and has no embedded sorry.

Added one public theorem with `:= by sorry`:
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints.section_localization_unit_constraints`,
node `lem-pd-section-localization-unit-constraints`, in
`Sheaf.Paper.SectionLocalizationUnitConstraints`. It states the two fixed
localization-tensorator unitor equations for a single scheme and complex. Its
source and complete mathematical proof are recorded in the docstring and node.

This is a decomposition, not a net proof: one original hole removed, one strictly
smaller hole added; zero holes remain in the item, one in the delivery. All private
helpers are proved. There are no new definitions containing holes and no axioms.

## No longer needed

No existing imports were removed: the item originally had only its public data
import, which its unchanged statement still requires. No existing module is
withdrawn and no global pruning is claimed.

The item's direct proof no longer needs:

- `lem-weil-pbc-ringed-topos-kflat-pullback`
  (`Sheaf.Paper.KFlatRingedToposPullback`): cancellation of the unit edges proves
  invertibility of target vertices without resolving membership of the pullback.
- `lem-weil-pbc-site-derived-tensor-descent`
  (`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`):
  generic monoidal naturality and the explicit localization-unit equations suffice
  for these edge identities; no transformation-extension argument is used here.
- `lem-pd-section-kflat-tensor-comparison` as a direct proof dependency of the item:
  the regular unit is shown resolving directly, and representative invertibility
  comes from `tensor_representatives`. This node is still needed below the new
  normalization lemma, for its fixed derived-equivalence constraint laws, and
  remains part of the statement-data import closure.

No unit statement or realized unit step is bypassed. The parent still receives
exactly the same sixteen-clause `SectionUnitEdges` statement.

## Where the brief, the DAG or earlier work was wrong

The old plan invokes normalized modelTensor unitor equations, but neither cited
interface states them. `SectionKFlatTensorComparison.UnitCondition` identifies the
regular object and gives the constraint laws of the derived equivalence's theta;
it does not give unit laws for qTensor. `TensorRepresentativeCondition` gives the
binary normalization, one-sided invertibility, and existence of a unit isomorphism,
without a qTensor unitor clause. Naturality alone cannot supply that missing
normalization. The new lemma isolates precisely this calculation, with the
specified regular comparison retained.

The old invertibility route also needlessly requested resolving preservation for
the pullback. The formal cancellation argument eliminates that direct dependency.
No existing statement is disputed or changed.

## New nodes

`lem-pd-section-localization-unit-constraints` is attached to
`Sheaf.Paper.SectionLocalizationUnitConstraints.section_localization_unit_constraints`
(with the full namespace recorded in its Lean attachment). It isolates the source
and target modelTensor normalization equations already invoked in Steps 2–3 of
the original node. Unlike the assigned theorem it has no scheme morphism, pullback,
derived-pullback tensor arrow, proposed scalar arrow, representative hypothesis,
resolving hypothesis, or vertex clauses. The item uses it at the source and target
and proves the actual edge identifications and invertibility by real Lean
composition, naturality, tensor interchange, and cancellation. The zero complex,
the unit complex and the zero ring require no extra hypotheses: the proposed
proof is the same unit/naturality computation in each case.

No change records are needed: only the assigned module, its own proof record,
and this new module and node change.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
