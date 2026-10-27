## What changed

Replaced the single `sorry` in
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_constant_presentation_lifting`
by a proof from two separate steps of its existing finite-matrix plan. Its statement,
including the specified ranks, arbitrary coefficient isomorphism c, and all universes,
is unchanged. All original public imports remain unchanged. Added private proof imports
for the two steps, module pullback coherence, and Mathlib cokernel preservation.

The first step, `constant_slice_internal_presentation`, transports a constant slice
presentation into an internal finite free presentation on the underlying scheme of U.
It is stated for any commutative condensed coefficient ring with the given c; it neither
asserts local descent nor constructs a point model. The second step,
`discrete_internal_matrix_local_lifting`, treats only an arbitrary internal finite free
morphism over discrete coefficients and its local descent to a point morphism. It has
no N, f, c, k, trivialization or cokernel. Its conclusion is an arrow isomorphism,
including the actual matrix square, rather than the desired module isomorphism.

The completed private argument lifts the point inverse-image adjunction to module
objects to obtain finite-colimit preservation. It applies `cokernel.mapIso` to each
matrix square, composes the two `PreservesCokernel.iso` comparisons, pulls back the
internal presentation, and uses restriction congruence and `upperStarComp` with the site
morphism triangle to identify the source with the specified restriction of N.
No data is selected in a definition from an unproved existence assertion.

The existing generic APIs were read first: FiniteLocalSectionLifts,
InternalAbelianSheafModuleEquivalence, ConstantRingModuleSheaves,
InternalModuleOperationsTransport, ScalarNormalizedConstantModels, the constant-sheaf
scheme comparison and weakly-etale localization. They provide the components but do
not directly assert either remaining comparison. The normalized-comparison theorem
requires extra normalization data, so applying it directly to arbitrary c is invalid.

## Proved and sorry left

One existing hole closed, by name:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_constant_presentation_lifting`
(node `lem-sfb-discrete-constant-presentation-lifting`). Its proof is complete relative
to the following two new statements. This is a decomposition, not a completed proof of
the entire original mathematical obligation: one hole closed and two holes added,
for net minus one hole closed.

Exactly two `sorry` declarations remain in this delivery, one per new module:

- `AlgebraicGeometry.ProEtale.IntegralModelsStacks.constant_slice_internal_presentation`
  (`lem-sfb-constant-slice-internal-presentation`,
  `Sheaf.AlgebraicGeometry.ConstantSliceInternalPresentation`).
- `AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_internal_matrix_local_lifting`
  (`lem-sfb-discrete-internal-matrix-local-lifting`,
  `Sheaf.AlgebraicGeometry.DiscreteInternalMatrixLocalLifting`).

Each is a genuine separate step of the original plan, with its source and full proof
in words in its docstring and node. Neither states the original local point-model
conclusion with the same hypotheses. There are no holes in definitions or private
helpers and no axiom declarations. The statements were checked on zero source rank,
zero target rank, the zero ring, and empty schemes: empty index sets use finite
biproducts of rank zero, while empty covering sieves need no witnesses. No
Noetherianity or nonemptiness assumption was introduced.

## No longer needed

No imports removed and no whole module pruned. The item's old direct proof dependencies
have been replaced by the two explicit steps. Constant-sheaf comparison, finite local
section lifting, section reconstruction and weakly-etale localization remain in the
plans of those steps; this is not a claim that their modules are globally unnecessary.
The generic final cokernel calculation does not need a separate finite-constant-local-
model criterion. All statement dependencies and the unit route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan is mathematically sound, but its first step hides the
compatibility of internal scheme inverse image, fixed-scalar inverse image, AsSmall
transport and slice localization. Its second step hides the regular-module and
finite-biproduct comparisons that turn section lifts into a square of actual internal
module morphisms. The two new statements expose these distinct obligations.

The typed point pullback wrapper has no exported finite-colimit preservation instance.
The proof supplies this locally from the actual point inverse-image adjunction.
Large coefficient constructions must stay abstract in the cokernel calculation;
private generic helpers and local irreducibility avoid unfolding their Kan extensions.
The actual kernel timeout was caused by inferring a scheme as the image under the comma
identity functor rather than its underlying object. Explicit Z := U.left and W := V.left
in the triangle comparison remove that expensive dependent instance conversion. The
complete item then compiled in 5 seconds with profiling, with no kernel errors. The
final version removes profiling options. A final lcompile.py --all run compiled all
three files without errors or warnings: ConstantSliceInternalPresentation 29.2 s,
DiscreteInternalMatrixLocalLifting 26.3 s, and the item 31.9 s, all below 60 s.
No shared definition, statement, instance or public interface was changed.

## New nodes

`lem-sfb-constant-slice-internal-presentation` records the encoding transport in the
original node's step 1. The explicit matrix is internal on U.left, with the original
ranks; this step does not claim any point descent. Its component dependencies include
the section-module operation comparison, constant-ring module equivalence and
weakly-etale localization.

`lem-sfb-discrete-internal-matrix-local-lifting` records the free-morphism part of
step 2. It descends a finite matrix to the discrete point after a covering refinement,
and records the commuting square as an arrow isomorphism. Its proof uses the
constant-sheaf scheme comparison and the existing simultaneous finite-section lifts.
There are no new change records: no other existing module or another module's node
is changed.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
