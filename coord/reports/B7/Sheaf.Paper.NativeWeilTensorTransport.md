## What changed

Replaced the body of
`AlgebraicGeometry.ProEtaleWeilSheaf.native_tensor_transport` by a reduction
with unchanged signature and public imports. The proof first constructs the
ordinary normalized closed structure, then lifts it over Frobenius. It assembles
`NativeClosedComparison` with `homModels` definitionally equal to the supplied
`M` and `homComparison` definitionally equal to the supplied `η`.

The Hom-arrow identity is proved by applying the normalized uncurry equation to
the identity of `M.weilHom.obj (op K, L)`, using the adjunction counit identity,
and applying injectivity of ordinary uncurrying. Associativity and symmetry
are taken from the generic `TensorCoherence` fields. The proof rewrites its unit
by the supplied normalization and reverses its two unit equations to match
`NativeTensorCoherence`, with precisely `C.unitComparison`.

Added two modules, each with one named theorem and one node:
`Sheaf.Paper.NativeOrdinaryClosedTensorModels` and
`Sheaf.Paper.NativeWeilTensorLift`. Their statements separate the ordinary
construction from the equivariant lift. The ordinary theorem uses no Weil
category, forgetful comparison, finite-type hypothesis or boundedness assumption.
The lift takes an already constructed ordinary tensor with its canonical
monoidal structure and normalized adjunction; it supplies the equivariant data,
coefficient-unit identifications, generic tensor coherence and full uncurry law.
Neither theorem restates the entire item under another name.

The item node now records those two dependencies and the formal assembly.
No existing declaration signature, definition, target, unit route or consumer
was changed. The current item source and Lean attachment were preserved despite
the historical quarantine entry in `coord/rework.tsv`.

## Proved and sorry left

This is a decomposition, not a completed proof of the underlying transport
obligation. One existing hole was replaced and two holes were added. The item
module has zero literal holes; the delivery has two. Net holes closed minus
added is -1, before any effect of the shared closure ledger.

Reduced, with a complete Lean proof from the two named intermediate statements:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_tensor_transport`
(node `lem-sf-weil-native-tensor-transport`).

Remaining holes, each the entire body `:= by sorry` of a public theorem:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_closed_tensor_models`
  (node `lem-sf-native-ordinary-closed-tensor-models`).
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_lift`
  (node `lem-sf-native-weil-tensor-lift`).

Both carry their source and full mathematical construction in their docstrings
and nodes. There are no new data definitions, arbitrary selected witnesses,
anonymous holes, axioms or modified shared interfaces.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.Paper.WeilFrobeniusActionResolutions` and
`Sheaf.Algebra.Homology.RingedForgetTensorTransposition`. The item instead imports
the two strictly intermediate modules. The original five planned dependencies
remain needed for the intermediate constructions: the Frobenius resolution,
ringed closed symmetric monoidal, normalized tensor-Hom adjunction,
two-injective Hom comparison and forgetful tensor transposition nodes. They
have been assigned to the corresponding new proof steps, not declared globally
unused. No module is withdrawn or globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan combines a genuinely nontrivial passage from ringed-site
models to specified native Hom representatives with its final formal assembly.
The available ringed declarations do not directly state that passage for the
supplied native functors and representatives. The new nodes expose its ordinary
and equivariant parts while the item discharges the formal assembly.

An unrestricted lift over an arbitrary ordinary unit isomorphism would be too
strong: that isomorphism need not have the appropriate Frobenius normalization.
The delivered intermediate statements avoid that issue. The ordinary theorem
retains the library's canonical derived module monoidal structure, and the lift
constructs both coefficient-unit identifications. The original item statement
is unchanged. The normalized Hom representatives and signed swap prevent
independent choices of incompatible adjunctions or symmetries.

Edge cases checked in the mathematical statements: zero objects and the empty
scheme still use the same adjunction, unit and localization equations; the
ordinary statement permits arbitrary unbounded complexes and all schemes;
characteristic two only specializes the same sign formulas. No identification
of derived fixed pairs with fixed pairs in the derived category is assumed.

## New nodes

`lem-sf-native-ordinary-closed-tensor-models` is the ordinary part of native
transport step 1: forget redundant ambient scalars, use the section-ring module
equivalence, transfer the ringed closed adjunction to the canonical derived
tensor, identify Hom using the supplied representatives, and retain unsigned
row-sign uncurrying and Koszul symmetry. Its statement requires no equivariance.

`lem-sf-native-weil-tensor-lift` is the action-site part of steps 1--2 over that
fixed ordinary tensor: lift the native closed structure and compare tensors,
retain generic coherence with the actual coefficient-unit equation, and
transport the full normalized uncurry law. The item proves the Hom-arrow
identity from this law rather than postulating that identity again.

Both inherit the parent chapter, unit and source paragraph. Searches used
LeanSearch, LeanFinder/Loogle, and repository/Mathlib grep. General monoidal
transport and adjoint uniqueness exist; no search result supplies these native
representative normalizations. No change record is needed because only the
item proof, new theorem modules and their node records are changed.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
