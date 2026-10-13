## What changed
Added a complete proof of `etale_limit_affine_stage_eventual_zero` by moving an index to the affine tail and composing transitions. Added the strictly smaller tail lemma `etale_limit_affine_stage_eventual_zero_tail` as an explicit remaining subproblem.

## Proved and sorry left
Proved: `AlgebraicGeometry.Etale.etale_limit_affine_stage_eventual_zero`.
Sorry left: `AlgebraicGeometry.Etale.etale_limit_affine_stage_eventual_zero_tail` (node `lem-weil-pbc-etale-limit-affine-stage-eventual-zero-tail`).

## No longer needed
The original direct cofinal-reindexing proof route and imports used only by it are no longer needed in this module; the proof uses the existing affine eventual-zero theorem and the tail lemma.

## Where the brief, the DAG or earlier work was wrong
The earlier direct proof exceeded the 60 second compiler limit. Splitting off the affine-tail comparison isolates the expensive geometric argument while the original theorem's finite-stage transport is fully proved.

## New nodes
`lem-weil-pbc-etale-limit-affine-stage-eventual-zero-tail`: tail-restricted affine comparison statement, with its Lean declaration in this module.

## Second reading by Y2
1. The delivered module was compared with the repository version. The existing target theorem signature is unchanged byte for byte; the added declaration is the separately recorded tail statement. Verdict: pass.
2. The file compiles cleanly. The target theorem has no `sorry`; the only remaining `sorry` is the named tail theorem, which has a matching DAG node and source/docstring proof sketch. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. The tail statement is strictly stronger in its hypotheses than the target (it assumes `i₀ ≤ i`) and is the kernel-detection subproblem needed by the target proof. It does not duplicate the target. The DAG node matches the Lean declaration. Verdict: pass.
4. The proof uses the cofinal affine-tail reduction described by the unit route; the target proof transports to the tail and composes maps. The expensive geometric argument remains explicitly isolated in the tail theorem. Verdict: pass.
5. Imports were checked against the proof and no additional proof-only import is exposed. The target node's route and dependencies remain intact; the new tail node records its own dependency and source. Verdict: pass.

Changed: added the second-reading record only; no Lean proof or statement was altered during this reading.
