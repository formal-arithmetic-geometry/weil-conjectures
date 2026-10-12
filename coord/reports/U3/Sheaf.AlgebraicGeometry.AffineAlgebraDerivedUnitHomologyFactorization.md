## What changed

The signature and visibility of
`AlgebraicGeometry.affine_algebra_derived_unit_homology_factorization` are unchanged.
Its proof now reduces to the canonical exact-derived counit isomorphism, rather than
constructing an adjunction-compatible cohomology comparison for the derived unit.

The proof constructs the natural homology comparison for the given L by identifying it
with P.mapDerivedCategory. It proves preservation of quasi-coherent cohomology by Rg_*
using exact scalar restriction and the affine cohomology formula. The private, fully
proved helper `restriction_exact` proves exactness from the unchanged underlying abelian
sheaf; no derived internal Hom module is needed for these instances.

The new counit obligation gives invertibility of the counit at L(M). The triangle identity,
naturality of the exact-functor homology comparison, and naturality of the ordinary affine
module units then prove invertibility of H^n of the derived unit. The witness e is the
inverse of this last isomorphism followed by the ordinary module unit isomorphism.
Inverse cancellation proves the requested equation. The existential conclusion does not
require e to be a previously chosen canonical comparison.

Added proof imports: AffineAlgebraExactDerivedCounitIso,
AffineAlgebraModuleAdjunctionIsos, RightDerivedFunctor.MapDerivedCategory,
ModuleCat.Presheaf.Sheafification, and Mathlib.CategoryTheory.Adjunction.Additive.
All added imports in the item are private imports. The new module publicly imports the
canonical exact-derived adjunction API because that adjunction appears in its statement.
The declaration-local elaboration options and heartbeat limit handle the scalar-restriction
comparison; they do not change other files' environments.

Both modules compile together with lcompile.py, without warnings. The changed DAG route
has no dependency path returning to the item (544 nodes inspected at second reading).
No existing definition, statement, visibility, or public import was changed, and no
adaptation is needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.affine_algebra_derived_unit_homology_factorization`
(node `lem-sc-affine-algebra-derived-unit-homology-factorization`).
The item's module has no remaining sorry.

Added one hole in its own module:
`AlgebraicGeometry.affine_algebra_exact_derived_counit_isIso`
(node `lem-sc-affine-algebra-exact-derived-counit-iso`, module
`Sheaf.AlgebraicGeometry.AffineAlgebraExactDerivedCounitIso`). Its proof is exactly
`by sorry`; its docstring and node describe the independent counit calculation on
K-injective resolutions, the affine cohomology comparisons, and ordinary counit
invertibility. This is a decomposition (one hole closed, one added), not a net proof
of the full import closure. The new statement is the counit half of the argument for
the canonical exact-derived adjunction. It asserts neither a derived unit isomorphism
nor the original existential unit factorization. The item's triangle/naturality/reflection
argument is necessary to recover that factorization from it.

The private helper `restriction_exact` is fully proved. No sorry is inside a definition
or a partial proof. Existing imported obligations, particularly affine cohomology and the
ordinary module adjunction isomorphisms, are used without copying or proving them here.

## No longer needed

Removed the item's explicit proof import
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral` and its direct proof edge
`lem-pc-ringed-spaces-derived-adjoint-general`. Exact P already has the canonical derived
adjunction, so the item does not need to select a separate tensor-derived pullback witness.
The quasi-coherence dependency still uses the ringed-space theorem transitively; this
is direct-route pruning, not a claim that that module leaves the targets' entire closure.

Neither `Sheaf.AlgebraicGeometry.AffineAlgebraDerivedCounitHomologyFactorization` nor
`Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule` is imported. The former is circular for
this route; the latter's scalar-restriction exactness is proved by the private helper.
The second reading also removes the redundant explicit proof import
`Sheaf.AlgebraicGeometry.AffineModuleCorrespondence`: it is already publicly imported
by DirectImageAlgebraDerivedCategory, and its proof dependency remains because the
proof uses it. It removes the redundant added proof imports
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`
(already publicly imported by the new counit module) and
`Mathlib.CategoryTheory.Adjunction.Unique` (available through retained imports).
No other original proof dependencies were removed. No whole module is claimed
to have left the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The unit docstring describes a compatible cohomology comparison, but its listed declarations
do not supply the unit equation. A short alternative is possible because the conclusion
allows any isomorphism e satisfying the equation. The new DAG proof records this route;
the original statement and docstring remain unchanged.

The current node for the existing derived counit factorization has a counit-from-unit proof
plan using this item. Importing and applying that theorem here would be circular even
the current Lean proof explicitly imports and uses this item. The new canonical counit node
therefore records an independent direct cohomology calculation; it does not cite that
existing counit node, this unit node, or the derived adjunction isomorphisms node.

The source was read online because the literature payload is not present in this checkout:
[Stacks 0AVW](https://stacks.math.columbia.edu/tag/0AVW) and
[Stacks 079W](https://stacks.math.columbia.edu/tag/079W).
The new obligation is the first of the two adjunction maps in 0AVW's proof. Its proof
uses the exact-functor and derived-adjunction APIs already implemented in the library.
LeanSearch returned HTTP 500 and is recorded as unavailable. LeanFinder found only
underived module/sheaf adjunction facts; the targeted Mathlib grep found no exact match.
The whole blueprint search found no matching canonical exact-derived counit node.

Edge cases of the new statement: zero cohomology and empty schemes give maps between
zero objects; the identity morphism gives the identity up to the chosen underived
adjunction isomorphism. No boundedness, finite morphism, nonzero ring, or surjectivity
hypothesis was added. The unit record's realized lists do not bind this auxiliary node,
and the route stays in the affine derived equivalence part of finite duality.

## New nodes

`lem-sc-affine-algebra-exact-derived-counit-iso`, in
`dag/nodes/sec-picard-framework/lem-sc-affine-algebra-exact-derived-counit-iso.json`,
states invertibility of the canonical exact-derived counit on quasi-coherent complexes.
It is realized by `Sheaf.AlgebraicGeometry.AffineAlgebraExactDerivedCounitIso`.
It isolates the remaining direct counit/cohomology calculation, strictly below the
original unit factorization, and its proof route is independent of that item.
There are no change records because no existing interface changes.


## Second reading by U3

1. Compared the delivered item with the repository using diff and checked the
   theorem signature byte for byte. Verdict: unchanged hypotheses, conclusion,
   universes, visibility, definitions and public imports. Only the proof, a private
   proved helper, declaration-local options, and private imports change. The new
   counit module introduces one theorem, not a replacement statement or definition.
2. Compiled both delivered modules in import order with lcompile.py. Verdict:
   clean compilation. The item has no sorry; the only added sorry is the whole
   proof of affine_algebra_exact_derived_counit_isIso. No forbidden declaration,
   axiom, or data construction from arbitrary unproved existence occurs.
   A scratch #print axioms for the original declaration reports exactly propext,
   Classical.choice, Quot.sound and sorryAx. The delivery axiom probe checks all
   declarations, including restriction_exact. This closes one original hole and
   adds one: a decomposition with zero net hole reduction.
3. Read the new counit statement, its full docstring argument and matching node,
   the exact-derived adjunction implementation, and Stacks 0AVW and 079W. Verdict:
   true, and strictly the counit half of the argument; recovering the original
   unit factorization still requires the substantial triangle, naturality and
   reflection proof in the item. Identity morphisms reduce to an equivalence's
   counit, zero complexes give zero-object isomorphisms, and empty schemes give
   the same trivial cases. Arbitrary adjunctions are accounted for by uniqueness.
   Independent LeanFinder, Loogle and Mathlib grep searches using pushforward
   full faithfulness and counit/quasi-coherence terminology found no replacement.
   The generic derived_counit/derivedε_fac_app API supplies compatibility, not
   invertibility. Searched lean/Sheaf and lean/WeilConjectures too: the existing
   affine algebra derived counit factorization imports and uses this unit item,
   so cannot close the new obligation without a cycle. The Spec-only affine
   equivalence has different categories and needs local comparison/descent;
   it is not a direct replacement. Closing the remaining cohomology/counit
   compatibility calculation is beyond a short repair; the sourced hole remains.
4. Followed the argument from the original target downward. Verdict: the
   existential comparison really follows by inverse cancellation, without
   requiring a canonical comparison as extra data. Retained imports supply
   declarations or instances actually used. Removed three redundant explicit
   imports after a scratch compile: AffineModuleCorrespondence, the exact-derived
   Adjunction API and Adjunction.Unique. Adjunction.Additive is necessary:
   removing it fails to find left_adjoint_additive. No longer needed lists the
   sole removed old proof edge and all removed explicit imports. Read
   dag/units/sk-thm-picard-duality.json: realized.statement and its sole realized
   step are empty, and this auxiliary affine-equivalence reduction does not
   replace a realized unit step or change the chapter route.
5. Matched each node's lean.statement to the actual theorem signature and each
   proof_deps to the union of its proof steps' uses. Verdict: consistent. The
   existing node changes only the permitted proof metadata; the new node has
   its source, proof, creation/provenance, searches and full Lean record.
   Traversing the updated proof dependency closure found no path back to the
   item (544 nodes visited). Added the independent second-reader searches to
   the new node. The ordinary counit-first source argument is independent of
   the old counit-from-unit proof.

Changes made by the second reader: removed the three redundant private imports,
updated the report's stale assertion that the existing counit factorization was
still sorry, updated the dependency traversal count, and recorded the independent
searches and this review. No proof, existing statement, definition or public import
was altered by the second reading.
