## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-module-affine-bound.json`: statement, split into six proof steps; Mathlib searches found no match. Statement, statement dependencies, original provenance and inherited searches retained.
- `citations.json`: one verbatim statement quotation for each of the eleven step/node citations.
- `searches.jsonl`: actual search-command output records. No new nodes and no Mathlib leaves.

## Attachments

None. I searched the slopmaster2 project declarations by the item tag and by uniform/affine torsion-cohomology terminology, and checked the nearby `AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt` in `WeilConjectures/AlgebraicGeometry/Sites/CohomologicalDimension.lean:44–52`: it is an abelian-sheaf theorem with a field-bound hypothesis, not the module statement, and its own proof is `sorry`. Its specialization at lines 63–71 rests on it. The read-only upstream master search did not supply an exact finished declaration either. These are not attachments.

## WANTED

None. All source material needed for this split is in the supplied literature.

## Issues found and resolved

The imported item had no proof. The blueprint's `det-pe-unbounded-classical-unit`, Fixed-degree truncation paragraph, attributes the étale module bound to the abelian uniform bound without writing the coefficient comparisons. I filled precisely that inference using the constant one-object pro-étale presentation, Stacks 099W and 03FD. This reuses `det-pe-unbounded-classical-bounds` part (1), rather than reproducing its finite-field, dimension and affine-limit proofs. The source field bound and dimension control remain in that existing node's dependency closure.

For the final step I used `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison`, which explicitly applies to ordinary modules over a ring sheaf. The superficially similar `lem-weil-pbc-etale-module-cohomology-forget` is stated for ModuleCat-valued sheaves and would require an additional equivalence. This avoids silently identifying coefficient encodings. Constant-module inverse image is identified with underlying abelian inverse image by the statement of `lem-pe-constant-left-module-inverse-image`.

The chapter and unit route are unchanged. The ancestor remains `det-ctf-finite-comparison-localizing`, Step 1, through `lem-sfb-unbounded-site-comparison`, Step 5. The existing bounds theorem and the cohomology comparisons are declared in `split_report.tool_uses`, with their exact purposes. No maintainer-owned `tool_uses` field or unit realization was edited.

## Unfinished work

None in the one-level split. There are no new statement-only obligations. No Lean was written, no compiler/Lake/build command was run, and no shared repository file was changed.

## Not duplicates

No new nodes were created. Whole-DAG searches by uniform bounds, étale/module cohomology, 099W and 03FD found the existing comparison and bounds nodes used here. `tools/blueprint_refs.py search 'cohomology modules'` and `search 'uniform cohomological bounds'` found no blueprint node stating the item in the same coefficient category; the latter found `det-pe-unbounded-classical-bounds`, whose part (1) is used as an abelian input, not duplicated. `same_as` remains empty.

## Review by Q30

I read the current main-20261015 chapter and `sk-prop-ctf-finite-comparison` unit, the full statement and proof of `det-pe-unbounded-classical-unit`, and the statement and proof of `det-pe-unbounded-classical-bounds`. The latter explicitly includes empty schemes, arbitrary locally torsion abelian sheaves and small nonempty cofiltered affine presentations. I also opened the statement of every node cited by every step, not their titles alone. The mathematical source comparisons were read at Stacks `proetale.tex`, Tag 099W, label `lemma-compare-cohomology` (around line 3986); `sites-cohomology.tex`, Tag 03FD, label `lemma-cohomology-modules-abelian-agree` (around line 1862), including its injective-acyclicity proof; and `sites.tex`, Tag 00YV, label `proposition-functoriality-algebraic-structures-topoi` (around line 10473). The enough-injectives source is `injectives.tex`, Tag 01DU, label `theorem-sheaves-modules-injectives`. No SGA source is used. No new-node source needs review because there are no new nodes.

Step 1 uses the two actual definitions: the constant sheaf is sheafification of the constant ring presheaf, and a module sheaf has unital sectionwise actions. The image of the zero scalar N1 is zero, so N times every section is zero. This is elementary and proves exactly the local-torsion hypothesis that part (1) of the bounds theorem needs. In particular finiteness of section modules is never inferred from finiteness of A.

Step 2 uses clause (1) of `det-pe-morphisms-etale-comparison`, which says étale implies weakly étale; the pro-étale site definition then admits W. The presentation definition says the affine condition is on the schemes themselves. Here W is the affine étale test object from the item. The singleton category and identity transition satisfy all smallness, nonemptiness, cofilteredness and affine-transition requirements; a cone to the singleton diagram is exactly one map to W. No finite-presentation descent is hidden in this step.

Step 3 quotes precisely part (1) of `det-pe-unbounded-classical-bounds`. Its source is X, its torsion input is the underlying F from step 1, and its test presentation is step 2. The auxiliary Y and g can be X and its identity; the identity is finite type by the empty list of algebra generators. The theorem's d_X=0 for empty X is verbatim the convention of the item. Thus it supplies the pro-étale group in the step for all q>e_X, with no separatedness or constructibility hypothesis added.

Step 4 uses the statement of `lem-weil-pbc-comparison-pullback`, namely nu_W^* w_et^{-1} ≅ w_proet^{-1} nu_X^*, and Tag 099W's abelian cohomology comparison on W. The input sheaf on W is F_W=w_et^{-1}F, not F on X and not an unmentioned extension of F. Since e_X is nonnegative, q>e_X lies in the comparison's allowed nonnegative degrees. Cohomology takes the displayed coefficient isomorphism to a group isomorphism, so the zero group from step 3 is exactly the needed abelian group.

Step 5 uses the explicit forgetful-compatibility clause of `lem-pe-constant-left-module-inverse-image`, for the actual étale geometric morphism and the same A on both sides. Its canonical identification of pulled-back constant ring sheaves gives the ordinary left A_W-module structure, and its V f^* ≅ f_ab^{-1} V identifies M_ab with F_W. This is a non-elementary coefficient comparison, explicitly cited, not an assumption about inverse image preserving module structures.

Step 6 uses the statement of `lem-weil-pbc-module-sheaves-enough-injectives` on W, which covers both ordinary constant-ring modules and abelian sheaves. It then meets every hypothesis of the ringed-site evaluation comparison: the site is small in the common universe, A_W is its ring sheaf, M is an ordinary left module sheaf, and W→W is the terminal site object. The comparison is expressly computed by injective module resolutions. Forgetting the A-action on the section complex does not change kernels, images or the cohomology group, so the comparison identifies the statement's H_A^q with the vanished abelian cohomology. A trivial underlying abelian group is a trivial A-module. No flatness and no underlying-injective claim enter the proof.

I tested X empty (then every W→X is empty), W empty over nonempty X, X a point over either permitted field, A=0, A=Z/ell^2, and an infinite direct sum of coefficient sheaves. For an empty site object the empty covering forces every section to be zero, so the injective-resolution definition agrees with the uniform bound's empty convention. Over a finite field at dimension zero the stated bound is 1; over an algebraically closed field it is a harmless upper bound. The nonconstructible and nonflat cases use precisely the same annihilator and comparison. There is no statement dispute or weakened conclusion.

For B1–B10 there are no new-node obligations; the item's notions and statement dependencies were retained, TeX is single escaped after JSON decoding, the source labels were checked, and actual searches were logged. I inspected all Mathlib search hits: the affine-site equivalence and Grothendieck instances at `Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean:140–152` do not prove a cohomological-dimension bound, the étale/cotangent hits concern rings, and the abstract injective-dimension results require the vanishing they characterize. A second semantic phrasing was also run. These do not supply an exact match or one-line specialization. Under C1/C4 each non-elementary input is a named node with a verbatim quotation in citations.json. Under D there is neither a new restatement nor a moved whole proof; steps instantiate two existing general comparisons around a separately established abelian bound. I checked that no cited dependency has the item in its statement/proof closure, so the new edges are noncircular. All six steps are below 2000 characters (maximum 794); there is no long step hiding an additional lemma. Under E I checked each field, coefficient, universe, site, test-object and degree hypothesis as detailed above. The correction made while writing was selecting the ringed-site comparison rather than the ModuleCat-valued comparison, so the coefficient hypothesis now matches literally.
