## What changed

Filled `CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_descent`
without changing its signature or `TensorComparison`. The private helpers construct
its chain comparison using the adopted source-library `mapBifunctorComparison` API,
including naturality and the prescribed coproduct-summand equation.

The existing independent-coefficient K-flat resolution theorem supplies
flat-term representatives. Its tensor-right flatness is identified with
`IsFlatOnSite` by `siteSheafTensorRightIso`. The proved public theorem
`CategoryTheory.derivedResolvingPairRestriction` then makes restriction to pairs
of these representatives fully faithful. The source and target tensor-model
comparisons, exact-functor factors and chain comparison define a natural
isomorphism on the representatives. The already proved generic
`CategoryTheory.tensorComparisonDescent` theorem lifts it and proves its
representative square. A separate faithfulness and cancellation argument proves
uniqueness even for arbitrary natural transformations, as the original item
requires.

Added the single smaller obligation `RingedForgetTensorCoherence`, which assumes
these constructions and proves only structural coherence and unit normalization.
Its declaration has a source, a complete proof in words, and a new DAG node. All
new proof imports of the item are private; its existing public import is unchanged.
No existing module other than the assigned item was changed. Local irreducibility
attributes keep the chosen internal-Hom and derived-functor constructions behind
their APIs during elaboration; they do not alter any imported module or any
attribute visible to consumers.

## Proved and sorry left

Original holes: 1. Closed:
`CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_descent`.
The item now has zero `sorry` occurrences. Its chain construction, derived
extension, representative equation and uniqueness argument are proved in Lean.

Added holes: 1, in
`CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_coherence`
(node `lem-sf-ringed-forget-tensor-coherence`, module
`Sheaf.Algebra.Homology.RingedForgetTensorCoherence`). This is the original node's
structural-constraint step, assuming the already constructed chain and derived
isomorphisms and their representative square. It asserts neither the existence
nor the uniqueness of those isomorphisms. The source and full argument are in
its docstring and node. The mathematical edge-case review checks identity U
with identical tensor presentations and identity comparisons, zero inputs, and degree-zero tensor
units. Complexes concentrated in arbitrary degrees test the Koszul factor
(-1)^(pq); additivity preserves it. No hypothesis about global generation by
pure tensors is used.

This delivery is a decomposition: one hole closed and one strictly smaller hole
added, for net zero holes closed. No private helper or definition has a hole.

## No longer needed

No original Lean import was removed and no module is withdrawn or globally
pruned. The direct proof dependency
`lem-weil-pbc-site-derived-tensor-descent` is replaced by the public
`derivedResolvingPairRestriction` and `tensorComparisonDescent` APIs, applied to
the existing K-flat resolutions. No functorial resolution or import of private
resolution constructions is needed. This is not a claim that the project can
prune the site-derived-tensor-descent module, whose definitions are still used.

The main proof no longer directly uses
`lem-sf-ringed-derived-closed-symmetric-monoidal`,
`lem-pur-kflat-total-tensor-model` or `lem-pc-kflat-resolution` to establish
structural coherence; they remain dependencies of the smaller coherence node.
The existing K-flat resolution is also used directly for fully faithful
restriction in the main proof. The main node's `proof`, `proof_deps` and
`proof_origin` record the actual route, including the new coherence node.
The blueprint unit and all of its realized statements and steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The earlier plan's tensor
extension can be implemented directly by the existing resolving-pair restriction
and generic comparison-descent APIs; ordinary flat-term K-flat resolutions
suffice, and no functorial choice or closure assumption is needed for descent.
The adopted source already supplies the chain comparison and its summand and naturality formulas. A further library search
found the proved generic `TensorPullbackRepresentativeDescent` theorem, whose
unrestricted category universes fit this item; it supplies existence of the
derived isomorphism and its square. These need no new mathematical obligation.
The remaining structural comparison needs the fixed models' associator, unitor and symmetry equations; it is not an
existence theorem for the tensor comparison under another name.

## New nodes

`lem-sf-ringed-forget-tensor-coherence`, at
`dag/nodes/sec-six-functors/lem-sf-ringed-forget-tensor-coherence.json`, records
structural coherence of a GIVEN normalized derived tensor comparison. It is
step 4 of the original node, sourced to Stacks Tags 0FPT, 06YS, 06YU and 0G7D.
The chain isomorphism, derived extension and representative square are hypotheses;
the conclusion only supplies the structural equations and the normalized unit.
The whole-blueprint search `blueprint_refs.py search "tensor coherence"` found
zero matching blueprint nodes. Other existing coherence declarations were read:
`ResolvingTensorSignedCoherence` requires a geometric pullback and a common
coefficient universe, and `FiniteDerivedComparisonNormalization` requires an
actual ringed pullback in one common site/derived universe. They do not apply to
the arbitrary specified exact U with independent universes in this item.
No change record is needed: existing statements, definitions and public imports
are unchanged, and only the assigned module and its node plus the new child and
its node are delivered.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
