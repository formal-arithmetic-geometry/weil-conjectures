## What changed

Proved `AlgebraicGeometry.ordinaryEvaluation_source_biproduct` without changing its
signature or public imports. Four proved private helpers handle zero internal Hom,
zero dual degrees, transport of biproduct indices, and the finite-support tensor
coproduct calculation. The isomorphism is constructed with `biproduct.desc` and
`HomologicalComplex.mapBifunctorDesc`; both inverse identities and all specified
inclusion equations are proved. The construction covers the empty interval and
requires no boundedness of F. Updated the existing node's proof to match this route.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ordinaryEvaluation_source_biproduct`
(node `lem-pc-ordinary-evaluation-source-biproduct`). No holes added or split off.
No `sorry` remains in the delivered module. The actual module compiles without
warnings against the unchanged `OrdinaryEvaluationData` source compiled locally
through `lcompile.py` into the sandbox's `.lbuild`. The dependency source was
removed from the delivery after verification; no dependency is changed or added.
The required `deliver3.py --no-push` printed OK: local compilation and preflight
passed, including the axiom probe. Nothing was pushed. The second reading remains
for the next worker.

## No longer needed

None. No imports or dependency modules are pruned. All four existing proof
dependencies remain used. The stronger intermediate identification of each dual
degree with a single internal Hom is unnecessary: only vanishing outside the
interval is needed, and it follows directly from the product-limit fan.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The shared compiled cache still lacks
`OrdinaryEvaluationData.olean`, although its unchanged source compiles. Local
verification used the prescribed multi-file `lcompile.py` support to compile
that exact dependency into the sandbox's `.lbuild`, then verified the actual
item with its original imports. The delivery contains only the item and its
updated node, not the dependency. The earlier scratch import of
`BoundedOrdinaryEvaluationAssembly` is not used for this verification or delivery.

## Second reading by F1

1. Compared the delivered module and node with the repository versions. The public theorem
   signature and existing declarations are unchanged; the node records only proof and
   proof-origin updates. Verdict: pass.
2. Compiled the module and the sandbox import closure with `lcompile.py`. The module has no
   `sorry`, forbidden declarations, or hollow definitions. An axiom probe reports only
   `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Searched the library and Mathlib-facing search records for an existing finite tensor
   biproduct result. No duplicate split-off statement or shorter available declaration was
   found; no statements were split off. Verdict: pass.
4. Read the proof from the target downward. It uses the stated product-projection and
   tensor-closure dependencies, constructs both inverse maps explicitly, and handles empty
   intervals and unbounded F. All original proof dependencies remain used, so no pruning is
   available. Verdict: pass.
5. Checked the node proof steps, dependencies, origin, and unit route against the Lean proof.
   The unit `sk-thm-picard-duality` remains realized through this target and the node's
   route matches the implementation. Verdict: pass.

Changed nothing during second reading; the delivered proof and node were already correct.
