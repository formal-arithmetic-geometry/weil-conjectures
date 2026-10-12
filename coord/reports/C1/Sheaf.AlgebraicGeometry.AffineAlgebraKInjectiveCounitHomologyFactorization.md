## What changed

The main theorem now reduces its existential and equality to two named intermediate theorems.
Two new modules state the affine K-injective cohomology comparison and its counit
compatibility. The main module imports them and combines them with `obtain` and `exact`.

## Proved and sorry left

The main declaration `affine_algebra_kinjective_counit_homology_factorization` is proved from
its two intermediate declarations. The declarations `affine_algebra_kinjective_cohomology_comparison`
and `affine_algebra_kinjective_counit_compatibility` remain `sorry`, each with a dedicated DAG node.
The existing `affine_algebra_kinjective_homology_comparison_iso` is proved by `infer_instance`.

## No longer needed

The unused exact-functor comparison module and its import were removed; the remaining imports are used by the statements or proof route.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped at the affine comparison. The stage-3 requirement permits that
substantive work to be split into strict intermediate statements; the main theorem can then be
proved by real Lean composition.

## New nodes

`new-affine-algebra-kinjective-cohomology-comparison` and
`new-affine-algebra-kinjective-counit-compatibility` are added under `dag/nodes/sec-picard-framework`.

## Second reading by C1

1. **Visible changes and signatures.** Compared the delivered main module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only two proof-only imports and the proof body were added. The two new theorem modules are separate split-off statements.

2. **Compilation and axioms.** Compiled all four sandbox modules with `lcompile.py --all`; they compile successfully. There are no definitions containing `sorry`, axioms, unsafe declarations, or forbidden implementation mechanisms. The two split-off theorems are the only remaining `sorry`s and are named in the report above.

3. **Statements and split-off nodes.** The split-off comparison and counit-compatibility statements are the exact intermediate results used by the main proof, with the same hypotheses and conclusion required by the composition. Their sources and proof descriptions are recorded in their DAG nodes; searches were run with grep, Loogle, and LeanSearch (LeanSearch was unavailable).

4. **Pruning and route.** The main theorem follows the recorded route: obtain the affine cohomology comparison and apply counit compatibility. Imports needed by the statements remain public, while the two new imports in the main module are proof-only. The unit route is unchanged; this item does not realize a unit step.

5. **Proof dependency agreement.** The main node's proof and `proof_deps` agree with the two theorem applications in the Lean proof. The split-off nodes are marked `split` and carry their source, blueprint, and Lean declaration records.

**Changes made during second reading:** corrected the new-node module metadata to the actual cohomology-comparison module path and removed an unused exact-functor comparison module that was not needed by the proof. No mathematical statement or target signature was changed.
