## What changed

Added the affine-open basis proof and split the local cohomological vanishing into a named intermediate theorem.

## Proved and sorry left

`affineBasisRestrictedLowerTail_local_bound` is proved from the affine-open basis theorem and the intermediate local vanishing theorem. The intermediate theorem `affineBasisRestrictedLowerTail_local_vanishing` remains `sorry`.

## No longer needed

Removed proof-only imports `Sheaf.AlgebraicGeometry.OpenModuleCohomologyComparison`, `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and `Mathlib.Algebra.Homology.Embedding.CochainComplex`; the target now depends only on the auxiliary node.

## Where the brief, the DAG or earlier work was wrong

The planned local vanishing step requires substantial derived restriction and cohomology comparison arguments; it was split into a strictly simpler per-affine-open theorem.

## New nodes

`lem-sc-affine-basis-restricted-lower-tail-local-bound-aux` — local vanishing on each affine open, with source and proof plan recorded in its module docstring.

## Earlier second reading (a previous round; superseded)

The target proof compiles in the sandbox. The remaining sorry is isolated in the strictly simpler local vanishing theorem.

## Second reading by B4

1. The target module was diffed against the repository version. The theorem signature and all existing declarations are unchanged; only the proof body, the auxiliary import, and proof-only imports differ. Verdict: pass.
2. Both delivered modules compile with `lcompile.py --all`; the only remaining `sorry` is the explicitly named auxiliary theorem `affineBasisRestrictedLowerTail_local_vanishing`, which has a matching split node and source docstring. No definitions contain `sorry`, and no forbidden declarations occur. Verdict: pass.
3. The auxiliary statement is a strict per-affine-open local vanishing reduction, is true under the parent hypotheses, and is needed by the target proof. Searches recorded in the node found no existing equivalent declaration. Verdict: pass.
4. The target uses the affine-open basis route and applies the auxiliary theorem for each basis element. The unit route is preserved. Verdict: pass.
5. The DAG proof and dependency records match the Lean proof: the target uses the auxiliary node, and the auxiliary node records the imported planned dependencies. Verdict: pass.

Changed the target proof to choose `V.toScheme.affineOpens`, removed unused proof-only imports from both modules, and retained the local vanishing theorem as the sole documented split-off hole. No statement or definition was changed.
