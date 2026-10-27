## What changed

Filled `WeilConjectures.commonProjectionProperFactor` without changing its signature.
The item now proves the support-identification square from the coefficient comparison's
composition, open-identification and proper-identity laws. It transports the proper
projection through the proved general adjunction mate theorem, then pastes the two
squares using tensor and projection naturality. All equality transports at the supplied
stage endpoints are accounted for by proved private helpers.

Added `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility`, containing the actual
functor-equality transport and currying constructions and one tensor/pullback square.
This square contains neither the support identification nor a projection mate nor the
counit computation. Its two inputs are arbitrary rational objects on the target of the
proper factor; it is exactly the finite-representative step of the old proof plan.
The item imports this module privately. The item's DAG proof now follows this argument.

## Proved and sorry left

Closed the item's one hole, `WeilConjectures.commonProjectionProperFactor`
(`lem-sf-common-projection-proper-factor`), by a complete proof from the smaller square.
No `sorry` remains in the item, and all private helpers are proved.

Added one hole, `WeilConjectures.commonProjectionPullbackTensorCompatibility`
(`lem-sf-common-projection-pullback-tensor-compatibility`). It remains to expand the
canonical common-stage representative formula and the two inclusion tensorators and
cancel the prescribed transition and scalar-unit comparisons. The new declaration's
source and complete proof in words are in its docstring and matching DAG node.

This delivery is a decomposition: one upper hole closed, one strictly smaller hole
added, net zero holes closed. It does not claim an axiom-free proof of the transitive
coefficient theory. No data definition contains a hole.

## No longer needed

No existing imports or modules are removed. In particular, the canonical completed
pullback/tensor comparison remains needed by the smaller square, so it is not pruned.
The item itself no longer performs its finite-representative calculation directly;
that part is the new dependency, rather than an asserted preservation of the entire
proper factor under another name. The open projection map and its compatibility are
not used in this proof. The unit has no realized statement or proof-step node assigned
to this factor, and its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The old one-step DAG proof concealed two distinct operations: the support comparison
calculation and the tensor/pullback calculation needed before the counit mate can be
transported. The former and the mate calculation are now formal Lean proofs. The latter
is isolated precisely, without adding a preservation hypothesis to the item or changing
any existing statement or definition.

Searches used Lean Finder (ordinary tensor base-change results only), Loogle (the local
projection declaration is not in its index), and local source searches. The useful
existing result is `CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`
in the adopted source library; the existing coefficient counit equation identifies its
mate with the prescribed direct-image comparison. Its existing DAG attachment is
`lem-sp-categorical-projection-mate-square`, which is included in the updated route.
`commonProjectionProperTensorCompatibility` existentially supplies a tensorator and
therefore does not give the square for this item's fixed canonical tensorator.
No adopted source file is modified.

## New nodes

`lem-sf-common-projection-pullback-tensor-compatibility` realizes only the canonical
tensor/pullback square. Its helpers transport the specified comparison along functor
equalities and curry the specified tensorator; these are explicit constructions.
The statement is valid for zero inputs, empty schemes and identity maps, using the same
canonical representative formula. The node inherits the item's chapter and unit and
records all three searches. There are no change records or consumer adaptations because
all existing interfaces are preserved.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
