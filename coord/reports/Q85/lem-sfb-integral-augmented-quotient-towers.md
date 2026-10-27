# Q85: lem-sfb-integral-augmented-quotient-towers

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-augmented-quotient-towers.json — statement split into six proof steps; Mathlib has module quotient ingredients, but no match for this sheaf-complex assertion with its specified comparisons and strict augmentations.
- citations.json — verbatim statement excerpts for every step/node citation.
- report.md — this report.

No new nodes and no new Mathlib leaves. searches.jsonl records the actual five new searches. The earlier imported search records are retained. write_split.py is sandbox scratch work only.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for augmented quotient / quotient tower terminology. The hits concern algebraic resolutions or unrelated completion constructions; none states every clause of this item. No Lean was written or compiled.

## Wanted literature

None. All sources used are available locally.

## Audit findings

The item statement is unchanged. Its proof was empty. There is no blueprint_update on this item. I read the fixed chapter and sk-lem-int-tensor unit before writing the split. The argument realizes the first paragraph and the comparison paragraph of det-lem-int-tensor-pullback, at the level of ordinary complexes; it does not import the source's derived cone argument into an ordinary tensor statement.

A necessary distinction is that a quotient of module sheaves is a sheaf cokernel. It must not be treated as a sectionwise quotient on every test object. The proof uses local lifts and local equalities, and then glues. In particular, the inverse of beta is justified for nonconstant sections of R, not only for constant scalars. Neither flatness nor K-flatness of H is invoked.

## Not duplicates

No new nodes were created. Whole-DAG and blueprint searches for quotient, augmented quotient, strict augmented, reduction scalar restriction, completion-flat and tensor-product-pullback found no blueprint statement equal to the item. Existing derived quotient/pullback coherence nodes concern localized derived comparisons and additional tensor equations, rather than the ordinary augmented towers here. The existing lem-sfb-integral-coefficient-square-normalization supplies precisely the common coefficient setup and the chain map d_H; it is used instead of creating a coefficient lemma. Constant sheaf exactness is reused as lem-weil-pbc-finite-type-constant-exact.

## Review by Q85

I read the item's actual blueprint proof file, literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-pullback.proof.md, together with its unit and chapter. I also read Stacks sites-modules.tex at Tag 093J (lemma-constant-exact), Tag 093M (lemma-completion-flat), and Tag 03EL (lemma-tensor-product-pullback). The source motivates the comparisons but does not write the strict ordinary cochain calculations; the proof is therefore marked agent-written. There are no new nodes whose sources need separate review.

Step 1 uses the statement of lem-sfb-integral-coefficient-square-normalization: it actually supplies R/pi^n R = S_n with the prescribed projection, exactness, and d_H with identity underlying map. Its prime, field characteristic, finite extension and scheme hypotheses are exactly those of this item. Constant sheaf exactness is taken from the explicit cokernel clause of lem-weil-pbc-finite-type-constant-exact, applied on the small site with ring A and the map multiplication by pi^n. It gives C/pi^n C = S_n, not a claim about evaluation preserving all cokernels. This generic off-unit tool use is declared in split_report.tool_uses.

Step 2 uses the actual sheafification definition of tensor in def-pur-sheaf-tensor-product and the unchanged-underlying-sheaf definition of def-pc-sheaf-restrict-scalars. Its quotient isomorphisms are proved by the two inverse formulas, with lift independence and balancing checked. For a nonconstant r, locally r-i(c)=pi^n t, so the extra term disappears already in the constant tensor. This is a direct elementary argument from the quotient identifications of step 1; it is not a hidden non-elementary change-of-rings theorem. The construction works in every degree independently.

Step 3 uses the explicit total differential in def-pc-tensor-complex-sheaves. Since S_n is concentrated in degree zero, the total has just one summand in each degree, so no unbounded sum interchange or sign comparison is hidden. The formula f(bh)=bf(h) proves naturality in H and all differentials. The quotient reductions and generators h tensor 1 prove naturality in n and the augmentation normalization.

Step 4 uses the exactness clause of lem-sfb-integral-coefficient-square-normalization to identify the actual pullback of a cokernel with the cokernel of the pulled-back multiplication map. Its coefficient square and prescribed coefficient identifications keep pi and both scalar actions fixed. This proves lambda and the constant analogue by cokernel uniqueness; the formula on inverse-image tensors follows by taking their quotient classes. It never uses a derived pullback theorem for a non-K-flat complex.

Step 5 uses the full natural chain isomorphism d_H of the coefficient-square node, not merely its underlying unbundled sheaf. Together with the beta proved in steps 2–3 it gives the displayed theta in the correct direction. Naturality with respect to P tensor S_m -> P tensor S_n and the quotient calculation prove strict tower naturality. Pointwise inverse maps then give the inverse tower transformations.

Step 6 uses the preceding proved steps: lambda sends h tensor 1 to itself, and naturality of d at the actual augmentation followed by beta inverse is exactly b_V d_P. Both assertions are equations of chain maps at every n, hence equations of augmented tower maps. No extra citation is needed for an internal application of the earlier proof steps.

I checked delivery-errors B through E point by point. Every cited statement was opened; citations.json copies actual statement substrings. The dependency traversal through all cited nodes does not reach this item, so there is no cycle. No clause is moved into a new node. All five elementary steps explicitly give the local tensor, quotient, naturality or augmentation calculation; no step exceeds 2000 characters. Statement dependencies are preserved because the statement is unchanged. Blueprint ancestry and same_as are filled and retained. The report and node preserve the original source, inherited searches and creation fields.

Small cases checked: H=0; H=R[0]; H=S_m[0] (nonflat), where both tensors are S_min(m,n); identity g; the empty scheme; n=1; composites m>=n of quotient reductions; and an arbitrary differential on a torsion complex. Each formula remains meaningful and gives the asserted strict equalities. Finite tensor complexes need no special argument because the construction is valid for every complex.

Mathlib searches were run through msearch.py, with two semantic phrasings as well as Loogle, LeanSearch and grep; all completed successfully. I read TensorProduct.tensorQuotEquivQuotSMul and its generator and augmentation formulas at Mathlib/LinearAlgebra/TensorProduct/Quotient.lean:164,207,218,227, and the presheaf tensor formula at Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean:80. These prove ordinary module facts only; passing to these particular coefficient sheaves, module inverse image, and strict augmented complex towers requires the argument above, so the item is not a Mathlib leaf. The other hits concern adic completion of finite modules or group homology and do not state this item.

The initial dry run rejected only the short exactness quote at step 4. I expanded each coefficient-square excerpt to include the actual coefficient quotients, identity comparison and exactness clauses, without changing the proof.

## Unfinished work

None in the split. Delivery validation and push are performed with the required deliver.py tool.
