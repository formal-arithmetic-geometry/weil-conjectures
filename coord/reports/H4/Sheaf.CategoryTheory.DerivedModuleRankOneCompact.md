## What changed

The target now introduces the family and combines injectivity and surjectivity of its canonical
additive comparison. Its existing signature, visibility, and docstring are unchanged. The second
reader proved injectivity directly by coproduct projections and removed the unnecessary bijectivity
wrapper module and node. The only remaining obligation is the rank-one surjectivity calculation.
All proof dependencies use plain imports; the original public imports are unchanged.

## Proved and sorry left

Hole closed in the existing module: `CategoryTheory.derivedModule_rankOne_compact`, node
`new-stage3-derived-module-rank-one-compact`.

New theorem proved without holes: `CategoryTheory.derivedModule_rankOne_comparison_injective`, node
`new-stage3-derived-module-rank-one-compact-injective`. Its proof uses only `propext`,
`Classical.choice`, and `Quot.sound`.

Hole added and left: `CategoryTheory.derivedModule_rankOne_comparison_surjective`, node
`new-stage3-derived-module-rank-one-compact-surjective`. This named theorem has a source and complete
natural-language proof in its docstring. There are no other holes in the delivered files.
The target still depends on this hole, so this delivery is a decomposition (one existing hole
closed, one new hole added; net zero), not a completed compactness proof. The target and
surjectivity axiom checks include `sorryAx` in addition to the allowed standard axioms.

## No longer needed

Removed `Sheaf.CategoryTheory.DerivedModuleDirectSums` from the target's direct imports and
`lem-pc-derived-module-direct-sums` from its direct `proof_deps`. It remains a dependency of the
surjectivity calculation and is imported there, so it is not pruned from the target closure.
No existing library module or node is claimed pruned.

Removed the undelivered redundant wrapper `Sheaf.CategoryTheory.DerivedModuleRankOneCompactAux`,
its declaration `CategoryTheory.derivedModule_rankOne_comparison`, and its new node
`new-stage3-derived-module-rank-one-compact-comparison`.

## Where the brief, the DAG or earlier work was wrong

The first draft unnecessarily left injectivity open and used the same cycles-and-boundaries
explanation for both components. Injectivity needs no rank-one or derived-category calculation:
coproduct projections recover every coordinate. The first draft's node records still described
an old route and credited Q2 rather than H4 for the new proofs. Those records now follow the
actual proofs. The target's unit `sk-prop-sf-cbc` has empty `realized` statement and step lists;
no realized unit step is bypassed. Its direct-sum route remains below the surjectivity obligation.

## New nodes

`new-stage3-derived-module-rank-one-compact-injective`: proved coordinate recovery for the explicit
rank-one comparison, with no proof dependencies. Module
`Sheaf.CategoryTheory.DerivedModuleRankOneCompactInjective`.

`new-stage3-derived-module-rank-one-compact-surjective`: the remaining finite-support zero-cycle
calculation, using `lem-pc-derived-module-direct-sums`. Module
`Sheaf.CategoryTheory.DerivedModuleRankOneCompactSurjective`.

The existing target node has updated `proof`, `proof_deps`, and `proof_origin` only. No existing
statement or definition changes; no change record is needed.

## Second reading by H4

1. Compared the existing module with the repository using `diff -u`: only plain proof imports and
   the proof body changed. The existing declaration signature and docstring are byte-for-byte
   unchanged. The other two modules and nodes are new; no other existing module is delivered.
2. All three delivered modules compile locally in import order. Scanning finds exactly the one
   named surjectivity `sorry`, no definitions with holes, and no forbidden declarations or kernel
   bypasses. Scratch `#print axioms` checks show standard axioms only for injectivity and additionally
   `sorryAx` for the target and the remaining surjectivity theorem.
3. Checked the two one-sided statements: injectivity follows for every preadditive source by
   projections; surjectivity follows for this free rank-one source by K-projectivity, H^0, and finite
   support. Empty families, singleton families, noncommutative rings, and the zero ring cause no
   exception. No arbitrary data is chosen from a holed existence theorem. Repeated searches using
   LeanFinder (coproduct Hom injectivity), Loogle (`DirectSum.toAddMonoid`), and `rg` (rank-one,
   single complexes, and comparison maps) found no matching public result. A private coordinate
   calculation in `CompactHomHocolim` confirms the same elementary projection argument but is not
   reusable as a public lemma. Verified Stacks Tag 0F5X explicitly asserts that R is compact in D(R).
4. The shortest available route proves injectivity immediately and leaves only surjectivity.
   Removed the wrapper and moved the direct-sum proof import to where the remaining argument needs
   it. All public imports supply types or instances used by the signatures. The old direct
   dependency and the redundant new module/node are listed above. The unit's realized route is kept.
5. Checked and repaired the DAG records: the target uses exactly the two component nodes;
   injectivity has an elementary projection proof with no dependencies; surjectivity uses the
   derived direct-sum node. New nodes have self-contained statements, exact Lean signatures, sources,
   search records, creation and blueprint metadata, matching modules, and H4 proof origins.

Changed on second reading: closed injectivity; expanded the remaining hole's proof docstring;
removed the comparison wrapper; moved the direct-sum import; corrected dependency records,
self-contained node statements, exact Lean signature records, and the progress accounting.
