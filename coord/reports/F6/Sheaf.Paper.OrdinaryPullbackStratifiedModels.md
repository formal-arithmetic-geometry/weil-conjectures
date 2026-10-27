## What changed

Restored Sheaf.Paper.OrdinaryPullbackStratifiedModels from the quarantine path recorded in
coord/rework.tsv. All archived public declarations, signatures and data constructions stay.
The item now imports OrdinaryIntegralPullbackConstruction directly instead of its quarantined
parent theorem module. The needed finite-projective flatness is proved locally from the
existing scalar-unit and finite-free-retract APIs, removing the proof import of the
quarantined FiniteProjectiveModelPullback module.

Proved immersionExact and weaklyEtaleExact. First take adjunction mates of the completed
coefficient projection equations and forget commutativity. Projection uniqueness identifies
the chart structural map with ordinaryIntegralDirectRingMap. The induced pushforward
isomorphism gives the module-pullback isomorphism by conjugation of adjunctions. Transfer
ordinaryCompletedPullbackExact across it; the original adjunction supplies finite colimits.
The exact functor inverts homotopy quasi-isomorphisms after localization, so its universal
left-derived counit is invertible. The specified cochain computation map is a composite of
that counit with canonical localization isomorphisms. Both exact-restriction statements
follow with their original binders and original counit.

The perfect-model proof retains the original flat-term K-flat route. A private abbreviation
of the existing scalarPerfectFunctor realizes finite free modules as finite products of the
coefficient unit. Finite projective scalar modules are retracts of these, hence their
realizations are flat. The original model object specification and identity-component
presheaf isomorphism transfer this flatness to modelModule. No existing public model changes.
The splitting argument includes the zero module and rank zero. The exactness/counit proof
works for every complex, including zero complexes, without completeness assumptions.

The new proof import has broad abelian/derived instances with an independent universe.
The module disables these and the generic Subterminal sheafification
instances, retaining the existing canonical structures. It restores the fixed-universe
sheafification choices used by the removed dependency, scoped to the private proof helpers;
no new private instance is selected in a public signature or public definition. No instance declaration changes.

Textual comparison against the archive confirms all 15 public definition bodies and all
10 public theorem signatures are unchanged. The import closure was checked recursively
against the live source tree: no missing Sheaf or WeilConjectures source module remains.

Updated the item's DAG proof and proof dependencies. No other existing Lean module or node
is changed, no new public statement is introduced, and no declaration is removed.
Change record: coord/changes/F6-ordinary-stratified-models-restoration.md.

Validation: the complete proof version compiled through lcompile.py in 29.7 seconds,
below the unchanged 60-second limit. The delivery checks the final scoped instance
selections with its compilation and axiom probe before pushing.

Searches: msearch LeanFinder for exact-functor derived counits, Loogle for
IsLeftDerivedFunctor/IsIso, msearch grep for pullbackComp and the counit theorem, and local rg
in Mathlib and both library roots. Mathlib's
Functor.isIso_of_isLeftDerivedFunctor_of_inverts supplies the universal counit step.

## Proved and sorry left

Closed two of the archived module's five holes; added zero holes; split off zero statements.
These are proofs from existing declared dependencies, not a decomposition.

Closed (namespace WeilConjectures.OrdinaryStratifiedModels):

- immersionExact.
- weaklyEtaleExact.

The three remaining named theorem holes, unchanged and attached to
lem-tw-ordinary-pullback-stratified-models with their source and proof docstrings, are:

- modelPullback_existsUnique.
- moduleSquare_existsUnique.
- derivedSquare_existsUnique.

The already proved coefficientMap_comp, modelModule_additive, modelModule_obj,
perfectModelPullback and ordinaryPullbackStratifiedModels remain proved.
OrdinaryCompletedPullbackExact is an existing dependency with its own named hole and DAG
node; this delivery does not claim a sorry-free transitive axiom closure.
No definition contains a hole.

## No longer needed

Removed direct imports:

- Sheaf.Paper.OrdinaryCompletedIntegralPullback: its ordinary construction is already extracted
  into OrdinaryIntegralPullbackConstruction, now imported directly. The completion comparison
  and constructibility theorem are not used here.
- Sheaf.Paper.FiniteProjectiveModelPullback: its model-flatness calculation is supplied directly
  by existing scalar-unit and finite-free-retract APIs, with a complete local proof. Its other
  normalized model assertions were not used by the archived proof.

Removed lem-tw-finite-projective-model-pullback from this item's proof_deps. The private
finite-free-retract helper is owned by lem-weil-pbc-strict-perfect-ringed-pullback-model;
the scalar-unit helpers are owned by lem-sfb-scalar-perfect-chart-finite-free. These replace
that direct dependency. No module is withdrawn, no upstream declaration changes, and the
CompletionUnitFiniteMateComparison archive is untouched. Other consumers can still need
all these modules; no global pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because of quarantine, not because its mathematics or
attachment was withdrawn. The archive contains five holes and an already proved main
geometric assembly. Restoring a copy alone would not be a proof repair: this delivery
also closes the two exact-restriction holes and removes the unnecessary quarantined imports.

The original module imported the parent theorem rather than the independently extracted
ordinary construction. The recorded projection-normalized exactness theorem uses another
presentation of the same structural map and chosen left adjoint; it cannot be applied by
name alone. chartRingMap and chartPullIso prove the required identifications before exactness
is transported. The universal counit argument retains the specified ordinary counit.

No statement change, no new node, and no departure from a blueprint unit's route.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
