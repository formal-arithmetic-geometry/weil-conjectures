## What changed

Added two intermediate theorem modules and imported them into `IrreducibleLisseRefinement`.
The target theorem now combines an irreducible topological refinement with preservation of
finite local constancy along refinements.

## Proved and sorry left

`exists_irreducible_refinement` is proved by combining the two intermediate statements.
The following strictly smaller statements remain as documented `sorry`s:

- `exists_irreducible_refinement_topological` (lem-weil-pbc-irreducible-refinement-topological)
- `refinement_preserves_finite_lisse` (lem-weil-pbc-refinement-preserves-finite-lisse)

## No longer needed

No imports from the original item module were removed. Its proof uses both new intermediate
modules; its signature needs `Sheaf.AlgebraicGeometry.EtaleSheaves`.
Removed the redundant public import of `Sheaf.AlgebraicGeometry.EtaleSheaves` from the new
`IrreducibleStratificationRefinement` module: `Refinement` supplies everything in its signature.
The parent node no longer directly uses `lem-weil-pbc-noetherian-finite-components` or
`lem-weil-pbc-pullback-finite-locally-constant`; these old proof dependencies are replaced by
the two strictly smaller intermediate nodes. Finite components remains a dependency of the
topological helper, so that module/node is not globally pruned. The old pullback node has an
abelian-coefficient statement, insufficient for the helper's set-valued statement; its plan
now cites set-valued composition and stalk comparison and topological invariance instead.
No module is claimed to be globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The DAG's single geometric step was split into topological refinement and preservation.
Second reading found the parent node unchanged despite its new Lean route and repaired it.
The initial topological docstring incorrectly cited Stacks 005P and 005Q, which concern
quasi-compactness and proper maps; replaced by [0052](https://stacks.math.columbia.edu/tag/0052)
and [0BA8](https://stacks.math.columbia.edu/tag/0BA8).
The initial preservation proof silently assumed scheme factorization from image containment.
This fails, for example, for Spec k[epsilon]/(epsilon^2) mapping identically to itself versus
its reduced closed point. Replaced by the fibre-product/surjective-closed-immersion argument,
following [03SI](https://stacks.math.columbia.edu/tag/03SI), with
[095A](https://stacks.math.columbia.edu/tag/095A) for local constancy and
[03Q1 (3)](https://stacks.math.columbia.edu/tag/03Q1) for finite stalks.
The known upstream refinement lemma requires an abelian coefficient category and does not
apply to sheaves of sets. Neither intermediate closes in a short application of existing
lemmas: geometric assembly and the set-valued descent/trivialization argument remain open.

## New nodes

`lem-weil-pbc-irreducible-refinement-topological` and
`lem-weil-pbc-refinement-preserves-finite-lisse` are added under `sec-smooth-purity`.

## Earlier second reading (a previous round; superseded)

The target proof is unchanged in statement and combines two strictly smaller claims. The
new statements are exactly the topological and pullback components needed by the DAG route;
the unit's irreducible-refinement route is retained.

## Second reading by V2

1. Compared the original item's module with the repository using diff: the existing
   declaration signature and all original definition/interface text are byte-for-byte
   unchanged; only its proof and two plain proof imports are added. The other two modules
   are new. No target or existing definition changed; no change record is required.
2. Compiled all three modules locally in import order. Exactly two sorries remain, in
   the public named helper theorems listed above, each with its matching node and full
   docstring proof. No axiom, unsafe, opaque, implemented_by, extern, or hollow definition
   occurs. Explicit scratch #print axioms checks for all three declarations are recorded
   below; sorryAx is expected while these two dependencies remain open.
3. Checked the topological helper on empty X, empty original strata, a single component,
   and intersecting components: first-component allocation is disjoint, exhaustive and
   nonempty by component maximality. Checked preservation on identity refinements and
   unequal nilpotent scheme structures with the same image: the fibre product handles
   the latter without false factorization. Both statements are true and strictly smaller
   than the item (one is sheaf-independent; the other has no Noetherian or irreducibility
   assumptions). Repeated LeanFinder, Loogle and direct rg searches with new queries;
   recorded the hits and the abelian-versus-set-valued mismatch in the new nodes.
4. The item makes a genuine reduction by choosing T and combining its two properties.
   Kept the irreducible-refinement route; dag/units/sk-prop-sf-cbc.json has empty steps
   and empty realized arrays, so no realized step is bypassed or modified. Removed the
   redundant helper public import and completed No longer needed with both old parent
   proof dependencies. No shorter applicable full proof found.
5. Updated the parent node's proof, proof_deps and proof_origin to the two actual Lean
   helper applications. Corrected the new nodes' statement dependencies, source citations,
   proof plans, origins and multiline verbatim Lean signatures; all required new-node
   fields are present. The two helper plans describe the documented remaining work.

Changed: parent DAG metadata; both helper docstrings and node metadata/search evidence;
removed one redundant public import from the topological helper; completed this report.
The original theorem's proof itself needed no change.

Explicit scratch axiom checks: `exists_irreducible_refinement` uses only propext,
Classical.choice, Quot.sound and sorryAx; each helper uses the same four axioms. All three
scratch copies compiled; removed them before delivery.
