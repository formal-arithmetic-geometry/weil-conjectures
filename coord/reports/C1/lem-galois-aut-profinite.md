# lem-galois-aut-profinite

## Files written

- `dag/nodes/sec-curve-estimates/lem-galois-aut-profinite.json`: split Stacks Tag 0BMR and made its topology and category-size conventions explicit.
- `dag/nodes/sec-curve-estimates/lem-galois-closed-subgroup-product-finite-groups.json`: one new Mathlib leaf, the group-topology fact used in the final step.
- `coord/reports/C1/lem-galois-aut-profinite.md`: this report.

## Attachments

None. `AlgebraicGeometry.Scheme.FiniteEtale.exists_isFundamentalGroup` at `WeilConjectures/AlgebraicGeometry/FundamentalGroup/Basic.lean:144` bears this blueprint id and is sorry-free, but assumes a connected scheme and proves existence of a profinite fundamental group. It does not state the closed evaluation embedding for an arbitrary set-valued functor. Mathlib's `CategoryTheory.PreGaloisCategory.autEmbedding_isClosedEmbedding` at `Mathlib/CategoryTheory/Galois/Topology.lean:107` treats finite-set-valued functors only.

## Wanted

None. I read Stacks Tags 0BMQ and 0BMR on the Stacks site; the local `literature/stacks-project/pione.tex` is not present in this checkout and is reconstructed by the project's literature-fetch process.

## Corrections

The imported statement omitted the set-of-objects convention and the topologies necessary to interpret its closedness claim. Section 0BMQ specifies the compact-open topology on permutations of each discrete fibre and the induced topology on `Aut(F)`; I put these in the statement. The imported `def-galois-fibre-functor` dependency concerns geometric fibres of schemes and is unrelated to this abstract lemma. The `def-galois-category` proof dependency is also unnecessary: 0BMR applies to every functor to sets, without Galois-category axioms. The source Lean theorem with the marker states a narrower result, so it cannot close this node.

## Source error

Stacks 0BMR writes the excluding neighbourhood as `U × U' × ∏_{X'' ≠ X,X'} Aut(F(X''))`; when `X=X'` (for an endomorphism), these are two conditions on the same coordinate and this notation is invalid. Step 2 uses the intersection of the two projection preimages. It remains open and excludes every natural automorphism by the same inequality, so the theorem itself is unchanged.

## Review by C1

I checked the item against Stacks Section 0BMQ, label `section-galois`, and Lemma 0BMR, label `lemma-aut-inverse-limit`. The source gives a set of objects and hom sets, compact-open topology on each permutation group, induced topology on `Aut(F)`, closed image, and profiniteness for finite fibres. The revised statement has exactly those hypotheses and conclusions. Its pointwise-convergence description agrees with compact-open convergence because compact subsets of a discrete space are finite. The child states only the final topological-group fact in 0BMR; it introduces the index set, finite groups, product topology and closed subgroup itself, and carries no proof sketch or unsupported notion.

For step 1 I checked that componentwise bijections satisfying every naturality square form a natural isomorphism, and that their inverses also satisfy naturality. Step 2 uses precisely that characterization: a failed square at `f` and `x` gives two open evaluation conditions whose intersection misses the image. The two conditions can concern the same object, as the text now handles. Step 3 checks finiteness makes each permutation group discrete, then applies the child to the product and the closed subgroup from step 2. The child's cited Mathlib constructors are `ProfiniteGrp.pi` (Basic.lean:214), `ofFiniteGrp` (:224), and `ofClosedSubgroup` (:249); I read their definitions and checked that the product and subgroup topologies are the stated ones. Thus the leaf's `how` specifies the specialization rather than treating a merely related theorem as an exact match.

Before adding the child I searched all DAG node statements for `ProfiniteGrp.pi`, `ofClosedSubgroup`, and the group-topology claim, and searched the whole blueprint with `tools/blueprint_refs.py search 'closed subgroup'`; no matching node existed. I searched Mathlib by LeanSearch/LeanFinder (recorded in the node) and source grep, and checked `Topology.lean:41-125` for the finite-fibre counterpart of the item. The child is strictly smaller than the item and introduces no cycle. The item is not a Mathlib leaf because its closedness clause allows arbitrary set-valued functors, whereas Mathlib's Galois topology file assumes finite fibres.

I checked empty categories and empty fibres: the products and automorphism groups are trivial, and the argument still works. For a one-object category with endomorphisms, step 2's intersection handles `X=X'`; for a one-index product, the child reduces to a closed subgroup of a finite discrete group. No Galois-category axiom is used. The earlier sandbox draft had left the statement ambiguous and reported a delivery blocker; inspection of `deliver.py` showed it permits an item statement edit, so I corrected the statement and removed that blocker from this report.
