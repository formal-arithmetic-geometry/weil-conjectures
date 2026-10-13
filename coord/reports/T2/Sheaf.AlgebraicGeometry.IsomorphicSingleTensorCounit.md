## What changed

Repaired reviewer X-09060's E2 point. The equation theorem no longer quantifies over an arbitrary natural isomorphism. Its `t` is the witness from the transport theorem, which now fixes every inverse component by a concrete formula: the selected derived adjunction unit on `(p^*M)[0]`, followed by direct image of the pinned single tensor counit for `e` and the canonical underived tensor composition comparison. This determines the natural isomorphism uniquely. There is no data chosen from unconstrained existence. The target uses that same witness; its signature is unchanged.

The equation module publicly imports the transport module because its statement uses it. Both modules have source/proof documentation, and all three nodes track this repaired route. The change is recorded in `coord/changes/IsomorphicSingleTensorCounitImports.md`.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_isomorphic_single_tensor_counit` (one original hole), by existential introduction and application of the equation for the characterized witness.

Split off and still sorry: `AlgebraicGeometry.exists_isomorphic_single_tensor_counit_transport` (`lem-pc-isomorphic-single-tensor-counit-transport`) and `AlgebraicGeometry.isomorphic_single_tensor_counit_transport_equation` (`lem-pc-isomorphic-single-tensor-counit-equation`). These are two parts of the argument: invertibility/naturality of the explicit transport, then compatibility with the composition-pinned counit. This is a decomposition, not a claim that the full argument is proved without sorry dependencies. No definition contains a hole.

## No longer needed

The earlier `Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitParts` factorization helper and its node remain removed and unused. No library module is pruned in this repair; the transport and equation modules are both required.
The original proof dependencies `lem-pc-ringed-spaces-derived-pullback-composition`,
`def-pc-derived-base-change-map`, `lem-pc-module-pullback-adjunction`, and
`lem-pc-pinned-single-tensor-shifts` are no longer direct proof dependencies of
this item: they are used through the split statements and their signatures.
`PinnedSingleTensorShifts` remains a public signature import.
The redundant direct transport import in the item and redundant direct
`PinnedSingleTensorShifts` import in the equation module were removed;
the equation publicly imports transport, which publicly imports the signature API.

## Where the brief, the DAG or earlier work was wrong

E2 was correct: the previous equation statement was false for arbitrary natural isomorphisms, for example after composing with componentwise minus one over Spec Z. Merely selecting a witness from the former unconstrained existence theorem would not repair this. The transport theorem therefore now specifies the inverse components explicitly; the equation is tied to that uniquely characterized map. Minus one fails this inverse formula (except where it equals identity). Zero modules and empty schemes cause no problem: the formula uses natural units and canonical comparisons, and the equivalence remains valid.

## New nodes

`lem-pc-isomorphic-single-tensor-counit-transport`: transport invertibility and naturality for the explicit inverse-component formula, in `Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitTransport`.

`lem-pc-isomorphic-single-tensor-counit-equation`: counit compatibility for that canonical transport only, in `Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitEquation`. These are the existing split nodes of the returned delivery, repaired in place; no further nodes were introduced.


## Second reading by T2

1. Compared the item with the repository using `diff -u`: its existing theorem
signature is byte for byte unchanged. The two helper modules are new to the
repository, with their signatures recorded in their nodes. No definitions or
foreign modules changed. The change record describes the new helper interfaces.
2. Read all three files: exactly two holes remain, each the whole proof of a
public named theorem documented with its source, proof, and matching node.
There are no definitions, forbidden declarations, or hidden proof holes.
All three modules compiled. A scratch copy with `#print axioms` for all three
declarations reports only `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx`; the delivery probe independently checks every declaration; the original
item still depends on sorry through these two helpers and is a decomposition.
3. Checked both split statements mathematically. For an isomorphism e,
tensor pullback and direct image are exact inverse equivalences, so the derived
unit and the pinned single comparison are invertible. The displayed inverse
components are natural and determine t uniquely (natural transformations are
determined componentwise, and an inverse determines an isomorphism). This
legitimizes the chosen witness. Naturality of the unit and the composition
counit factorization give the equation before cancellation with t.hom.
For e the identity, it reduces to the selected unit/counit triangle and the
composition comparison; for zero modules and empty schemes it remains the
same functorial identity. No flatness of p or M is used. A sign twist fails
the specified inverse formula. Neither helper restates the existential target:
one constructs the canonical transport, the other proves its compatibility.
Repeated semantic, Loogle, and grep searches with new queries and searched both
library roots. Exact-functor single comparisons and leftDerived_fac are
constituents, not this scheme-level pinned comparison; nearby exact-composition
lemmas use different functors/comparisons. Neither helper closes in a few minutes.
4. Checked the route from the target downward. Existential introduction followed
by the canonical equation is the direct reduction to the two mathematical
parts. Removed two redundant imports; all remaining imports serve signatures
or the proof. Listed all four old direct proof dependencies above. The unit
`sk-thm-picard-f-representable` has empty statement/step realization lists;
this below-unit reduction bypasses no realized unit or chapter step.
5. Checked all node statements and Lean records against the files, and proof
steps against proof_deps and proof_origin. The original node names exactly the
two helper declarations used in its proof. New nodes have matching source,
creation, blueprint, chapter, unit, Lean record, and search fields.

Second reading changes: removed the redundant item transport import and equation
signature import; replaced unrelated copied searches in both split nodes with
actual searches about exact derived comparisons and derived factorization;
completed the old-dependency pruning inventory and this independent review.
No theorem statements or proof bodies were changed by the second reading.
