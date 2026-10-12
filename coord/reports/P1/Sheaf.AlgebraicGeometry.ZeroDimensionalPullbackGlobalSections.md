## What changed

Replaced the author's proposed product-factorization split with a genuine stalk-by-stalk reduction in `Sheaf.AlgebraicGeometry.ZeroDimensionalPullbackGlobalSections`. Its existing theorem signature and original mathematical docstring are unchanged. The proof uses the existing `Scheme.zeroDimensional_sections_stalks` twice, `Pi.reindex`, `Pi.mapIso`, product projection identities, and the concrete-category isomorphism criterion.

Added two separate modules: `ZeroDimensionalBaseChangeGeometricPoints` states geometric data independently of any sheaf; `GlobalSectionsStalkComparison` states compatibility of the canonical global-sections pullback with a single geometric stalk. Each new statement is a strict part of the argument, not a replacement name for the target. The target imports all three proof dependencies privately. New modules publicly import only signature dependencies. Removed the unneeded `bijective_of_eq_comp_iso` helper, deprecated sheaf-value expressions, and the invalid proposed decomposition split.

## Proved and sorry left

- `AlgebraicGeometry.Etale.bijective_globalSectionsUpperStarMap_of_dim_zero` is proved by the reduction (1 of the 1 originally open declarations). Its proof depends on existing open lemmas and the two new split lemmas below; it is not yet axiom-free.
- `AlgebraicGeometry.zeroDimensional_baseChange_geometric_points` remains `sorry`, node `lem-weil-pbc-zero-dimensional-base-change-geometric-points`, in its own module. Its docstring proves the geometric data using the existing canonical base-change point description, Nullstellensatz, stability of separated finite type under base change, and transport to an arbitrary cartesian square.
- `AlgebraicGeometry.Etale.exists_globalSections_stalk_comparison` remains `sorry`, node `lem-weil-pbc-global-sections-stalk-comparison`, in its own module. Its docstring describes the terminal-evaluation specialization of `inverseImage_stalk_germ`, including the colimit relation for restriction along the terminal isomorphism.

All three modules compile locally without errors or warnings. Axiom inspection permits only the standard axioms and `sorryAx` from the explicitly open dependencies.

## No longer needed

None of the old repository proof dependencies is pruned: `lem-weil-pbc-zero-dimensional-sections-stalks` is used directly; `lem-weil-pbc-zero-dimensional-base-change-points` and `lem-pod-separated-finite-type-base-change` remain in the geometric split's proof plan; `lem-weil-pbc-inverse-image-stalk-germ` remains in the single-stalk split's plan. Thus the transitive route is retained. The author's unlanded `lem-weil-pbc-zero-dimensional-global-sections-product` and helper were removed from this delivery, not pruned from the repository.

## Where the brief, the DAG or earlier work was wrong

The author's decomposition remains equivalent to the target: take a singleton index and the identity étale object of C. Constraining an arbitrary group family to sheaf values does not avoid the restatement. Moreover, an object of C.Etale is an étale neighbourhood, not a geometric point or its stalk; the proposed docstring conflated these. Its DAG Lean statement was stale, still binding an arbitrary group family. The first report also incorrectly described the target as still containing sorry. The replacement proof actually invokes the existing stalk-product lemma and leaves only distinct geometric and single-stalk steps open.

## Second reading by P1

1. Compared every delivered module with the repository. The sole existing declaration's full signature is byte-for-byte unchanged. The two additional modules and nodes are new; no existing definition or public import was changed. Verdict: pass after removing the author's restatement.
2. Compiled the three modules in import order through lcompile.py with no warnings. The target has no sorry; the only new sorries are exactly the two named theorems above, each with a source, a natural-language proof and its node. No axiom, unsafe, opaque, extern, implemented_by or hollow definition is present. Verdict: pass, conditional on the named open dependencies, as recorded.
3. Checked the split statements on empty schemes, a single nonreduced Artinian point, and disjoint unions of points. The geometric split applies to arbitrary cartesian squares and contains no sheaf. The germ comparison applies to any morphism and compares only one stalk; it does not assert the global-sections map is an isomorphism. Repeated leanfinder, loogle and grep searches, and read the existing base-change point, stalk-product, inverse-image germ and global-sections map declarations. No duplicate of either interface was found. Verdict: pass.
4. Read the proof from the target downward. Both germ-product isomorphisms come from the existing theorem; the product equality is checked on projections and right-hand isomorphisms are cancelled. The old dependencies remain needed transitively. Read sk-thm-p1.json realized: this node lies below its fixed curve-calculation steps and does not bypass any unit realization. Imports were minimized in new modules and proof-only imports are private. Verdict: pass.
5. Matched every node's declaration, statement and proof route to the Lean. The target node names precisely the geometric split, existing stalk-product theorem and single-stalk split; the new nodes include source, dependency plan, origin, searches, creation and blueprint metadata. Verdict: pass.

Changed during this second reading: rejected and removed the proposed equivalent decomposition, removed the unnecessary helper, wrote the real stalk-product reduction, added two strictly partial statements in their own modules with matching nodes, eliminated compilation warnings, and rewrote the inaccurate report and proof metadata. No change record is needed because no existing signature or definition changes.

## New nodes

`lem-weil-pbc-zero-dimensional-base-change-geometric-points`: supplies dimension, curve structure, the projection point equivalence and rational geometric points for an arbitrary zero-dimensional field-base-change square; this is the geometric part of the old plan only.

`lem-weil-pbc-global-sections-stalk-comparison`: supplies the single-coordinate germ equation for the canonical global-sections map and an inverse-image stalk isomorphism; it specializes the neighbourhood-unit statement to global sections without asserting their invariance.
