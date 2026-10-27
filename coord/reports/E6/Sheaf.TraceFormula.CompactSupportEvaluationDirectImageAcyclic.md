## What changed

Proved `WeilConjectures.compactSupportEvaluationDirectImage_acyclic` with its signature unchanged. The proof restricts scalars to the constant integral ring system, resolves there, and uses the explicit constant-system/diagram equivalence. Evaluation of constant systems preserves K-injectives because its coproduct left adjoint is exact. A homotopy comparison and scalar-restriction section acyclicity show that any finite-level K-injective resolution is sectionwise a quasi-isomorphism. Geometric direct image therefore preserves this resolution map, and naturality identifies its derived unit as an isomorphism.

Only the item module and its own DAG node change. Added private, fully proved construction and comparison helpers and private proof imports. The existing `tower_evaluation_isKInjective` theorem supplies the constant-system evaluation step. The scalar cone is constructed in commutative rings before forgetting to rings, so the transition maps agree with the actual coefficient tower. The generic constant-system constructions are reused from `NativeConstantRestrictionAcyclicity` through `import all`; no shared interface changes. The node and theorem proof description record the sectionwise route.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.compactSupportEvaluationDirectImage_acyclic` (`lem-trf-compact-support-evaluation-direct-image-acyclic`). No holes added, no split-off statements, and no `sorry` remains in the delivered Lean module. This is a proof rather than a decomposition. The diagnostic revision compiled on the server in 34.4 seconds. `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`; there is no inherited `sorryAx`. Profiling and axiom-print commands were removed before delivery.

## No longer needed

No original imports were removed: the two public imports supply the unchanged statement and its derived-unit API. The following planned proof dependencies are unnecessary for this proof and are removed from this node's `proof_deps` and proof-step `uses`:

- `lem-pur-system-single-derived-extension`, module `Sheaf.CategoryTheory.SystemSingleDerivedExtension`: no derived finite left extension is constructed.
- `lem-pur-system-singleton-geometric-pullback`, module `Sheaf.CategoryTheory.SystemSingletonGeometricPullback`: the proof uses the actual sectionwise geometric direct image rather than a singleton pullback comparison.
- `lem-pc-pre-derived-adjoint-functors-general`, module `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`: ordinary homotopy comparison and naturality of the existing derived unit suffice.

These are pruned from this item's argument only; no assertion is made that their other consumers disappear. The statement dependency `def-trf-compact-support-system-evaluation-diagram` remains. The unit's `realized` lists are empty and no prescribed unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned derived-tensor/adjunction route is unnecessary for this acyclicity substep. Existing scalar-restriction section acyclicity, the constant-system equivalence, and the K-injective comparison principle close it directly. Evaluation is used to preserve K-injectives only after restricting to constant integral scalars; no such assertion is made for the varying quotient coefficient rings. No statement or definition repair was needed.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
