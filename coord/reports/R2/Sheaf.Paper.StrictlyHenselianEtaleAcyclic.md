## What changed

Proved `strictlyHenselian_etale_acyclic` with its signature unchanged. Global sections preserve epimorphisms by the proved source-library instance in `WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian`, transported from terminal evaluation. Mathlib then supplies exactness. The proved total-derived-functor homology comparison gives positive-degree vanishing from the degree-zero single complex. Added proof-only imports of that source module, `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`, and `Mathlib.CategoryTheory.Abelian.Exact`. Updated the node's proof, proof dependencies and proof origin. No definition or statement changed. The node is below the unit's realized steps, which this delivery leaves intact.

Read Stacks [03QO](https://stacks.math.columbia.edu/tag/03QO) and [015F](https://stacks.math.columbia.edu/tag/015F) online because the literature tex files are absent on this machine. The source-library exactness route uses the same sections of etale neighbourhoods underlying 03QO. LeanFinder and Loogle searches ran through msearch; local searches found both needed source-library interfaces. Local compilation succeeds without warnings.

## Proved and sorry left

Proved `strictlyHenselian_etale_acyclic` (node `lem-weil-pbc-strictly-henselian-etale-acyclic`): 1 of 1 original sorries removed. No sorries remain in the item's module. No new modules or sorries added. The delivery dry run checks the transitive axioms as well as local and server compilation.

## No longer needed

Removed proof-only imports `Sheaf.AlgebraicGeometry.KInjectiveResolutions` and `Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`.

The proof no longer needs these original proof dependencies: `def-weil-affine-spectrum`, `def-weil-algebraic-closure`, `def-weil-geometric-point`, `lem-weil-pbc-strictly-henselian-sections-stalk`, `prop-weil-pbc-geometric-stalks-exact`, `lem-sp-exact-functor-preserves-homology`, and `def-weil-pbc-kinjective-resolutions`. The definitions used by the unchanged signature remain available through the public imports; removing a proof edge does not remove a statement dependency. In particular, the proof does not construct a geometric point or explicitly choose a K-injective resolution. The source-library total-derived-functor comparison already handles resolutions and commutation with homology. `lem-weil-pbc-exact-functor-complex-cohomology` remains the generic tool underlying that comparison.

No other import was removed. No unit statement or realized unit step was bypassed. These are dependencies pruned from this item only; other target paths may still reach them.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid, but does not mention the already proved source-library preservation-of-epimorphisms instance or the total-derived-functor homology comparison. Those declarations allow a complete proof without adding any intermediate theorem or explicitly rebuilding the stalk comparison and resolution argument. The source-library sheaf-cohomology vanishing theorem uses Ext indexing and is not directly the item's derived-category cohomology; this delivery uses the total-derived-functor comparison instead.

## Second reading by R2

1. **Visible changes and statements.** I diffed the delivered module against the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body changed. The delivered node changes only its proof metadata and proof dependencies, consistently with those edits.

2. **Compilation and proof status.** The sandbox import-order compilation completed successfully with no errors. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses the source-library strictly henselian epimorphism instance, transport along the terminal evaluation isomorphism, exactness of global sections, and the total right-derived homology comparison. `#print axioms strictlyHenselian_etale_acyclic` in a scratch copy reports exactly `propext`, `Classical.choice`, and `Quot.sound`; both the server compile and delivery checks passed in the dry run.

3. **Statements and dependencies.** No statement was split off or weakened, and no new node was added. The unchanged target statement is exactly the original one. The revised proof dependencies name the declarations used by the proof (strictly henselian terminology, abelian étale sheaves, étale cohomology, derived-category infrastructure, and exact-functor complex cohomology); the removed geometric-point, stalk, and explicit K-injective-resolution edges are not needed by this route. I independently searched the repository for the exactness and derived-comparison interfaces, and used msearch grep with the alternative single-functor comparison and source cohomology-vanishing names. The latter vanishing theorem uses Ext indexing; the existing homology comparison used here directly matches the target. No split-off statement needs an edge-case test; in the existing proof, p = 1 is covered by p > 0, degree zero is deliberately excluded, and the zero sheaf is covered without an additional hypothesis.

4. **Pruning and imports.** The two former proof-only imports for stalks and K-injective resolutions were removed. The three added imports are used by the proof. The corresponding old proof dependencies are listed under `## No longer needed`, and the unit route remains represented by the item's existing unit and node; the proof is a below-unit simplification using already proved source-library interfaces.

5. **DAG agreement and route.** I checked the updated node's Lean declaration, proof steps, `proof_deps`, and `proof_origin` against the delivered code. The first step matches the preservation-of-epimorphisms and exactness construction; the second matches the right-derived homology comparison and positive-degree single-complex vanishing. The unit's realized statement and steps are unchanged.

I changed only this report section during second reading; no Lean source or DAG repair was necessary.
