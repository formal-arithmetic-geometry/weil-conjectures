## What changed

Proved `Scheme.NoetherianApproximation.exists_smooth_affine_model` by applying the existing affine-limit smooth-stage theorem to the Noetherian approximation diagram, then choosing the pullback itself as the stage model and the identity comparison isomorphism. Added the proof-only import `Sheaf.AlgebraicGeometry.Morphisms.AffineLimitSmoothStage`.

## Proved and sorry left

The declaration `Scheme.NoetherianApproximation.exists_smooth_affine_model` is proved. No new `sorry` declarations were added.

## No longer needed

The originally planned smooth-algebra filtered-colimit descent and spreading-out nodes are not needed by this proof: `lem-weil-pbc-smooth-algebra-filtered-colimit-descent` and `thm-pd-spreading-out`.

## Where the brief, the DAG or earlier work was wrong

The original DAG route expanded the affine descent argument, but the library already contains the more general affine-limit smooth-stage theorem, which directly supplies the required smooth pullback model.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader; the proof compiles and preserves the target signature.

## Second reading by M3

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged; the only module change is the proof-only import and proof body. Verdict: pass.
2. Compiled the module with `lcompile.py`; it is error-free and contains no new `sorry`, axiom, unsafe, opaque, implemented_by, or extern. The theorem's only `sorryAx` dependency is the imported open affine-limit theorem. Verdict: pass.
3. Checked the proof route and searched the library for duplicate declarations. The proof directly applies `Scheme.exists_smooth_stage_of_affine_limit`, then uses the canonical pullback projection and reflexive isomorphism; no new split-off statement was added. Verdict: pass.
4. Confirmed the shorter route and pruning: the old filtered-colimit descent and spreading-out dependencies are unused, while `AffineLimitSmoothStage` is proof-only imported. The node proof and `proof_deps` now match the Lean proof. Verdict: pass.
5. Confirmed the unit route remains realized through `lem-sbc-affine-limit-smooth-stage`; the target statement and definitions are unchanged. Verdict: pass.

Changed the report and synchronized the node's proof, proof dependencies, and proof text with the implemented route. No holes were added; one target theorem was closed.
