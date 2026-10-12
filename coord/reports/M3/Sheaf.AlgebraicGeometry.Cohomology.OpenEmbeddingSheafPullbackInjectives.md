## What changed

Added the proof-only import `Sheaf.AlgebraicGeometry.Cohomology.OpenEmbeddingSheafPullbackAdjunction` and proved `Topology.isOpenEmbedding_sheafPullback_preservesInjectiveObjects` by applying the mono-preserving left-adjoint criterion. Added one intermediate statement module for the extension-by-zero adjunction.

## Proved and sorry left

Proved `Topology.isOpenEmbedding_sheafPullback_preservesInjectiveObjects`. The new theorem `Topology.isOpenEmbedding_sheafPullback_adjunction` remains sorry, with node `new-open-embedding-sheaf-pullback-adjunction`; it isolates construction and exactness of extension by zero.

## No longer needed

No imports removed. The dependency node `lem-sp-right-adjoint-preserves-injectives` is used conceptually through the Mathlib criterion, while no additional repository theorem is needed.

## Where the brief, the DAG or earlier work was wrong

The DAG plan omitted a Lean statement for the substantial extension-by-zero construction. It must be isolated as an intermediate theorem before the final adjunction criterion can be applied.

## New nodes

`new-open-embedding-sheaf-pullback-adjunction` is stated in `lean/Sheaf/AlgebraicGeometry/Cohomology/OpenEmbeddingSheafPullbackAdjunction.lean`; its proof is the extension-by-zero construction and mono preservation described in its docstring.

## Earlier second reading (a previous round; superseded)

The final theorem compiles and preserves the target signature. The new intermediate statement is strictly smaller: it isolates only the extension-by-zero construction, its mono preservation, and its adjunction to pullback; no unit route is bypassed.

## Second reading by M3

1. **Visibility and signatures.** Compared the delivered target module with the repository version. The existing theorem signature is unchanged; the only target-module change is a proof-only import and proof body. The new adjunction module and node are explicitly included in this delivery.
2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py --all`; both compile cleanly. The target theorem has no `sorry`; the named intermediate theorem is the sole remaining sorry and is documented with its source and construction. No forbidden declarations or hollow definitions occur.
3. **Statements and split.** Checked the new adjunction statement against the open-embedding extension-by-zero argument. It is strictly smaller than the target and supplies exactly the functor, monomorphism preservation, and adjunction required by the criterion. Repository and Mathlib searches found no duplicate declaration.
4. **Pruning and route.** The final proof follows the stated route: obtain the extension-by-zero adjunction, install its monomorphism-preservation instance, and apply Mathlib's right-adjoint criterion. No existing imports can be removed without losing the criterion or the sheaf definitions; the unit route is retained.
5. **DAG agreement.** Verified the target and new node records match the declarations, proof dependency, source, chapter, and unit. The new node is marked split with a complete proof plan and docstring.

Changed during second reading: added this review record only; no Lean statements or proofs required repair.
