## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.picardDirectImageBaseChangeMap_counit` to two strictly smaller statements: tensor-square conjugacy and factorization of the canonical coefficient map. The item's proof contains complete inverse-mate calculations, arbitrary coefficient counit naturality, specialization to the Picard square, and isomorphism-level comparison equalities lifted by typed congrArg. All existing public signatures, definition bodies, and docstrings are unchanged. Updated the parent proof route and added the two new nodes. The three modules compile individually in import order (2.6 s, 3.1 s, 8.0 s). This is a decomposition, not a net sorry reduction.

## Proved and sorry left

Original hole closed by decomposition: `AlgebraicGeometry.Scheme.Modules.picardDirectImageBaseChangeMap_counit`, node `lem-sc-picard-base-change-counit` (one of one original holes). No sorry remains in the item's module. Its private `baseSquare_app`, `square_counit`, and `baseChange_postcompose_counit` are fully proved.

Two holes added: `AlgebraicGeometry.Scheme.Modules.picardTensorSquareConjugacy`, node `lem-sc-picard-tensor-square-conjugacy`; `AlgebraicGeometry.Scheme.Modules.picardDirectImageBaseChangeMap_factorization`, node `lem-sc-picard-base-change-factorization`. Both are public theorems in separate modules, each with its whole proof `by sorry`, source, and complete natural-language proof. Conjugacy concerns only a square of functors; factorization concerns only the canonical map's two factors, with no counit conclusion. Neither restates the original theorem. No definitions contain sorry; no arbitrary data is chosen from a new existence hole.

## No longer needed

Removed redundant direct imports `Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction` and `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`: their declarations remain available through the unchanged public canonical-comparison import and are used by the proof. No underlying module or node is globally pruned. The original parent's direct proof dependency `lem-weil-pbc-conjugate-iso-unit-equation` is delegated to the tensor-square-conjugacy node rather than used by the parent directly. The cube unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt did not close the original hole. Direct simplification of the comparison homs and rfl on the concrete canonical-map normalization cause expensive kernel definitional equality and repeatedly exceed the 60-second compile limit. Isomorphism-level equality and typed congrArg make the square comparison compile quickly. The remaining canonical coefficient-map factorization is isolated as a strictly smaller step, not assumed as a counit identity. This decomposition needs a later worker to establish that factorization efficiently; the current mathematical counit assembly is complete and compiles without changing the definitions or increasing the time limit. All experimental definition changes, auxiliary-declaration references, local irreducibility attributes, diagnostic options, and heartbeat increases have been removed from the delivered files. The scratchpad preserves the experiments outside the delivery tree.

## New nodes

`lem-sc-picard-tensor-square-conjugacy` (`Sheaf.AlgebraicGeometry.PicardTensorSquareConjugacy`) isolates composition-comparison coherence under inverse conjugation for an arbitrary commuting scheme square. It involves no base-change morphism or counit formula. Its conclusion uses the hom of the composite isomorphism so the parent need not normalize equality-transport homs.

`lem-sc-picard-base-change-factorization` (`Sheaf.AlgebraicGeometry.PicardBaseChangeFactorization`) isolates identification of the canonical map with the square mate followed by the pushforward of its coefficient-composition comparison. Its isomorphism parameter is pinned by equality to the actual constructed comparison. Its proof is definition expansion, Iso.trans_hom, the pullback projection identity, and proof irrelevance. It contains no counit, inverse mate, or conjugacy assertion. The statement was checked for zero modules and empty schemes; no nonzero or invertibility hypothesis on base change is added. There are no change records or forced adaptations.

## Second reading by D2

1. I compared the delivered counit module with the repository version. The public
   statement and all existing declaration signatures are unchanged; the two added
   modules introduce only the split-off declarations recorded in their nodes.
   Verdict: pass.

2. I compiled all three modules with `lcompile.py --all`. There are no errors,
   forbidden declarations, or sorrys in the item's counit theorem; the two
   split-off theorem proofs are exactly `by sorry` and are named in the report.
   Verdict: pass, with the documented split holes.

3. I checked both split-off statements against their definitions and edge cases
   (zero coefficients and empty schemes). Each is strictly smaller than the
   counit target and neither duplicates the target statement. Verdict: pass.

4. I checked the proof route and imports. The counit proof uses the tensor-square
   conjugacy and coefficient-factorization nodes, and removes the two redundant
   direct imports. The unit route remains the cube unit route. Verdict: pass.

5. I checked that the DAG node declarations, proof dependencies, proof origins,
   and module statements match the Lean files. Verdict: pass.

I changed only the report for this second reading; no further Lean repair was
needed.
