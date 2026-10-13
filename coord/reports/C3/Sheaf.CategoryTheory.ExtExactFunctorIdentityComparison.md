## What changed

Replaced the independent proof of
`CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison` by the identity specialization
of the existing `exactFunctorCompositionComparison` compatibility declaration
for `mapExactFunctor_comp_mk₀_eq`, imported proof-only from
`Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison`. The pinned Mathlib lacks
`mapExactFunctor_eq_of_iso` and `mapExactFunctor_id`; the identity action is proved locally
from the existing localization comparison API, without adding a public declaration.
The public signature, visibility, and existing docstrings are unchanged.
The private `commShift_of_localization` helper is retained because
`Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity` refers to it.
Updated the existing node's proof route, dependencies, and origin to match the Lean proof.

## Proved and sorry left

`CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison` is completely proved by the
new specialization argument. The repository baseline already proves it: holes closed 0,
holes added 0, holes remaining 0. This is the explicitly assigned upstream-review repair,
not a claim of sorry-count progress. The replacement proof's axiom check reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No existing imports removed. The separate construction of the localized comparison for
an arbitrary functor F is removed from this proof; it uses the existing composition
comparison instead. The former proof dependency `def-weil-abstract-derived-category`
is no longer needed directly by this node. No entire module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox deleted the public theorem without adapting its four callers.
This repair restores the theorem with its unchanged signature and derives it from the
existing comparison, as the identity-specific review requests. No caller adaptation is
necessary. The named Mathlib lemmas in the upstream review are absent in the pinned
sources; the existing generalized composition comparison and a proved local identity
calculation supply the same argument. The published build still exposes the
composition comparison under its compatibility name, so the proof calls that name.


## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. The public theorem statement and the private helper signature are unchanged; the only proof-facing import added is the plain import of the existing composition comparison module. Verdict: pass.

2. Compiled the module with the pinned launcher. It compiles without errors or warnings. The axiom check for `CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison` reports only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. Verdict: pass.

3. The proof introduces no split-off statements or new nodes. The identity calculation is a local helper strictly inside the target proof, and the existing composition comparison is used rather than restated. The changed DAG proof route names the declarations actually used. Verdict: pass.

4. The shortest available route is the existing `exactFunctorCompositionComparison` specialization, with a local proof of the identity action because the pinned Mathlib does not provide the newer identity lemmas. No imports were removed; the old direct localization construction is pruned from the proof. Verdict: pass.

5. The DAG node's proof, `proof_deps`, and `proof_origin` agree with the delivered Lean proof. The unit route remains through the composition comparison node, and the target statement is unchanged. Verdict: pass.

Changed the target proof to use the identity specialization of the existing composition comparison, retaining the localization helper for its downstream caller, and updated the node route and dependencies accordingly.

## Second reading by C3

1. Compared the delivered module with the repository version. The public theorem and private helper signatures are byte-for-byte unchanged; only the proof body and proof-only import are delivered. Verdict: pass.

2. Compiled the module with the pinned launcher. It compiles without errors or warnings, contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and the axiom check for `CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison` reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. No statements were split off and no new nodes were added. The local identity calculation is an internal helper, while the target is proved by the existing composition comparison; the target statement is unchanged. Verdict: pass.

4. The proof uses the shortest available route: specialize `exactFunctorCompositionComparison` to identity functors and prove the pinned Mathlib identity action locally. The former direct localization construction is removed from the target proof, while the retained helper remains needed by its downstream caller. Verdict: pass.

5. The node's proof steps, `proof_deps`, and `proof_origin` match the declarations used by the Lean proof, and the unit route through the composition comparison is preserved. Verdict: pass.

Changed only the target proof route and corresponding DAG proof metadata; no statements, definitions, or public imports changed.
