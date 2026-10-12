## What changed

Replaced the proof of `AlgebraicGeometry.IsConnectedCurve.isProper_or_isAffine` with a
compactification argument. The proof uses `exists_smooth_properCompactification`, splits on
whether the complement of the open immersion is empty, transfers properness across the resulting
isomorphism in the empty case, and applies `isAffine_of_ne_top` plus `isoOpensRange` in the
nonempty case.

## Proved and sorry left

`AlgebraicGeometry.IsConnectedCurve.isProper_or_isAffine` is proved. No `sorry` remains.

## No longer needed

None; both stated proof dependencies (`lem-sc-compactification` and
`lem-sc-affine-open-proper`) are used through their Lean declarations.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was correct. The Lean proof packages the open subscheme as
`c.i.opensRange` and uses its canonical isomorphism to the source curve.


## Second reading by W2

1. Diff check: the theorem signature and all existing declarations match the repository; only the
   proof body and the restored documentation are present. Verdict: pass.
2. Proof check: the module compiles cleanly with no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern`; the target's remaining `sorryAx` comes only from imported open
   declarations. Verdict: pass.
3. Statement check: the target statement is unchanged, and no split-off statements or new nodes
   were introduced. Verdict: pass.
4. Pruning check: both compactification and affine-open dependencies are used by the proof, and
   no import or dependency can be removed. Verdict: pass.
5. DAG check: the existing node's proof route and `proof_deps` agree with the Lean proof, and the
   unit route remains the compactification plus empty/nonempty boundary split. Verdict: pass.

I restored the repository's copyright and module documentation that the first delivery omitted.
No mathematical or signature changes were needed.
