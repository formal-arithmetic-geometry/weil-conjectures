# Stage-1 report: lem-sfb-homogeneous-scheme-finite-set-affine

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-scheme-finite-set-affine.json`: statement, split; follows Milne B.37 Step 2 with seven explicit steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-closed-set-rational-lifts.json`: statement, unsplit; simultaneous splitting and source lifts for a finite closed target set under a surjective morphism of finite-type schemes. No Mathlib match after two semantic phrasings, LeanSearch, Loogle and two source greps.
- `citations.json`: verbatim statement quotations for every citation of the item's proof.
- `searches.jsonl`: actual msearch command records. The pre-existing item's older search records were retained; current NV searches were appended.

One new node, zero Mathlib leaves. All node files use indent=1 with a final newline. No Lean files, compiler, Lake, repository write, or direct git command was used.

## Attachments

None. Searches of `lean/WeilConjectures/` by the item's blueprint tag and by homogeneous/finite-set/affine concepts found no declaration stating this item. The group-scheme source statements concern group translations or the algebraically closed base case; projective affine-neighbourhood results require quasi-projectivity. Neither supplies the hypotheses and conclusion of the present item. The source of `exists_descent_norm_affine_shrinking` was read and used only via its existing DAG node, not offered as an attachment for this item.

## WANTED

None. The Milne PDF and Stacks sources used were available locally.

## Corrections and scope

The imported mathematical statement is retained, including arbitrary fields, arbitrary finite point sets, nonreduced groups, and the given fppf orbit morphism. Its duplicated TeX backslashes were normalized, and `def-pc-rational-point` was added to identify the already-present notation $o\in Y(k)$. This is a notation/dependency repair, not a changed hypothesis. There is no STATEMENT-DISPUTED claim.

The source is Milne, *Algebraic Groups*, Appendix B, Theorem B.37, Step 2, printed p.605 (PDF page 617). I read the whole step and its surrounding Steps 1 and 3 and Remark B.38. The proof's initial quasi-projectivity assumption is used to obtain quotient existence in Step 1, not in the argument of Step 2 about an existing quotient. Here the given orbit map is enough: its equivariance follows from the stated action law and its openness from its actual flat-lfp hypotheses. We do not cite the surrounding quotient-existence theorem or any SGA source.

The proof replaces the source's implicit closed-point rationalization by a smaller reusable lemma, and replaces its reference to the proof of B.18 by the existing norm-shrinking statement. It also writes the reduction of nonclosed points to closed specializations and the finite-extension openness/density arguments. There is no proof hidden in any new statement. All steps are under 2000 characters.

## Supporting lemma: source and argument retained for its next worker

For `lem-sfb-finite-closed-set-rational-lifts`, I read Milne B.37 Step 2's second paragraph, and Stacks Tag 0478, `varieties.tex`, `lemma-locally-finite-type-Jacobson`. Its statement is more general than the orbit-map use: no action, dense open, affine neighbourhood, or flatness occurs in it.

An explicit proof route for that unsplit lemma is as follows. For each $s$ in the finite closed target set, the nonempty fibre $X_s$ is a finite-type scheme over the finite residue extension $\kappa(s)/k$. Choose a closed point of the fibre, hence a point $z_s$ of $X$ over $s$ with $\kappa(z_s)/\kappa(s)$ finite. The latter residue field is finite over $k$, so $z_s$ is closed in $X$ (Zariski's lemma / closed-point criterion). Choose a finite normal extension $K/k$ inside an algebraic closure that contains every conjugate of each of the finitely many $\kappa(z_s)$; include their inseparable parts as well. For any such field $E$, every prime quotient of $E\otimes_k K$ is $K$: for generators of $E/k$, their minimal polynomials split over $K$, and the possible inseparable factors contribute nilpotents, not larger residue fields. Therefore every point over $z_s$, and likewise over $s$, is $K$-rational. The map $\operatorname{Spec}(\kappa(z_s)\otimes_k K)\to\operatorname{Spec}(\kappa(s)\otimes_k K)$ is surjective (base change of the surjective field-spectrum map). Thus all the points over $s$ have one of these rational source lifts. There are finitely many because these tensor algebras are finite-dimensional over $K$. List the lifts. If the target set is empty, take $K=k$ and the empty list.

This is a real lemma: simultaneous splitting of all conjugate lifts and the residue analysis of inseparable tensor algebras is more than a two-line consequence of the nodes cited in the item. It is strictly smaller than the item and supplies no affine open. It must not be replaced by an unjustified assertion that a single embedding of a source residue field gives lifts above every conjugate target point.

## Not duplicates

The whole DAG and blueprint were searched for homogeneous schemes, affine neighbourhoods, dense affine opens, rational points, rational lifts, splitting closed points, finite extensions and simultaneous rational lifts. Existing group-finite-point affine neighbourhoods and the homogeneous orbit quotient result have algebraically closed-field and/or affine smooth connected-group restrictions, and the latter also depends on the item's parent; neither states the finite-extension rational-lift fact. The existing finite-scalar generic-point lemma gives finite-free scalar projections and residue descriptions, but does not split points or lift a finite target set.

lem-sfb-finite-closed-set-rational-lifts vs lem-coef-infinity-arrow-join-geometry: concerns quasicategory joins and has no statement about finite-type schemes or residue-field rationalization; its source tag coincidence is unrelated.

lem-sfb-finite-closed-set-rational-lifts vs lem-trf-closed-subscheme-field-stalk-test: tests unramifiedness of a given closed subscheme under field-stalk and separable-residue hypotheses, and constructs no field extension or source lifts.

lem-sfb-finite-closed-set-rational-lifts vs lem-sc-point-tangent-closed-fibre-singleton: assumes an algebraically closed field and injectivity on closed points and bounds fibre cardinality, rather than splitting arbitrary finite closed target sets under surjections.

lem-sfb-finite-closed-set-rational-lifts vs lem-sc-lft-over-field-jacobson-space: gives density of closed points, without rational source lifts or a simultaneous splitting field.

lem-sfb-finite-closed-set-rational-lifts vs lem-sc-finite-type-nonclosed-closure-closed-points: assumes an algebraically closed field and counts closed specializations of a nonclosed point; there is no surjective morphism or finite extension.

lem-sfb-finite-closed-set-rational-lifts vs lem-sc-positive-dimensional-locally-algebraic-closed-points: gives infinitely many closed points in positive-dimensional closed sets, not rational lifts under a surjective morphism.

lem-sfb-finite-closed-set-rational-lifts vs lem-sc-affine-maximal-points-closed-in-lft-scheme: identifies affine-chart closed points as globally closed; no simultaneous splitting or source lifting is asserted.

lem-sfb-finite-closed-set-rational-lifts vs lem-sc-integral-locally-algebraic-affine-opens-dimension: compares dimensions of affine opens of an integral scheme and says nothing about rationalizing finite closed sets.

lem-sfb-finite-closed-set-rational-lifts vs lem-per-sylow-simultaneous-field-sections: the latter constructs a prime-to-ell extension giving embeddings into possibly nontrivial field factors of the target residue tensor algebras. It does not make all target points rational over the chosen field, and imposes separability and degree hypotheses on its input field tower. The new lemma requires simultaneous splitting of every target point and actual rational source lifts, with no degree bound and allowing inseparable target residue fields.

## Review by NV

I read Milne B.37 Step 2 with the existing item and the proposed new statement open. The argument concerns the already-given homogeneous scheme; I checked that every translation of the orbit map used in the proof is justified by the action identity $q(gh)=gq(h)$. Thus no quotient existence or identification with a sheaf quotient is being borrowed from a definition. The new lemma's own source and proof route are given above; its conclusion contains no affine neighbourhood and so is not a renamed clause of the item.

In Step 1 I checked the actual Jacobson statement: it gives closed points of the ambient scheme inside each closed closure, so the chosen specialization is globally closed. Its field hypothesis is arbitrary, not algebraically closed. The finite-type-over-Noetherian node applies over the field spectrum, and the finite-components node then applies to the resulting Noetherian scheme. The qcqs-over-affine node supplies the exact quasi-separatedness hypothesis of the generic-point affine-neighbourhood lemma. That lemma's statement includes all selected generic points in one affine open; it does not require $Y$ integral. The chosen open is dense because it contains a generic point of every irreducible component. I read the source declaration `exists_isAffineOpen_mem_of_subset_genericPoints` as well as its node, and did not confuse it with an arbitrary finite-set affine-neighbourhood theorem.

In Step 2 the new node is applied only to the finite closed set just obtained and the given surjective orbit morphism. It requires no smoothness, separability or flatness beyond these data. I checked the all-points-over-S clause rather than taking just one arbitrary lift of each original target point; that clause is crucial for the saturation in Step 6.

In Step 3 I read the finite-scalar-extension generic-points node: its first clause explicitly supplies the affine tensor formula and finite-free flat map for every scheme, not just generic points or integral schemes. I use precisely that clause. The base-change-surjectivity node gives surjectivity of all relevant projections, and the flat-lfp-open node gives openness after every base change. For finite field extensions I wrote out finite presentation by a multiplication table instead of inferring it from mere flatness. For $q_K$, flatness and local finite presentation are the original hypotheses carried through the base change, exactly the scope of the cited openness statement. The inverse image of a dense open is asserted dense only with this openness argument, not merely from surjectivity.

In Step 4 the isomorphisms used are actual inversion and rational-point translations from the group axioms; they need no group smoothness. I wrote out why the intersection of the finitely many dense opens is dense and why it is nonempty (the group has its identity). The finite-type base-change node supplies the finite-type hypothesis before applying the Jacobson closed-point node over $K$. The closed-point-field node's clause (a), valid over any field, gives $[\kappa(b):K]<\infty$. Its clause (b), which requires a separably closed base, is not used. This avoids assuming that a nonempty open over a finite field already has a rational point.

Step 5 is elementary from the two explicit inverse isomorphisms and the action law. I checked the order $g=g_jv_j^{-1}$ implies $g_j=gv_j$, rather than the opposite multiplication order, and then checked $q(gv_j)=gq(v_j)$. I checked that every point above a $K$-rational point becomes the unique point of $\operatorname{Spec}L$ in that point's fibre. The affine tensor formula is cited for the base-changed dense affine open. No smoothness, reducedness, or separability is silently used here.

In Step 6 I opened the full statements of `def-pd-descent-datum`, `def-pc-fibre-product`, and `lem-pd-descent-norm-affine-shrinking`. I also read the source declaration `exists_descent_norm_affine_shrinking` and Stacks Tag 03JE, `groupoids.tex`, `lemma-find-invariant-affine`. I matched the variables carefully: the shrinking lemma's finite flat lfp base map is the field-spectrum map, while its scheme with datum is $Y_L$. Its relation is precisely $Y_L\times_Y Y_L$. The whole finite set is an inverse image under $p$, so source and target have identical inverse images of it. This is why the exact finite-saturated-set version of the existing node applies. I did not take the stronger finite-set claim from the single-orbit wording of the Stacks tag; the stronger claim is in the cited node's statement itself.

In Step 7 I read the entire invariant-open-image statement, including its cartesian identification, and matched its flat, surjective, quasi-compact hypotheses to the finite-free scalar projection. It supplies both the descended open and the exact base-change identification needed next. I read the fpqc covering definition and Stacks Tag 02L5, `descent.tex`, `lemma-descending-property-affine`; the field-spectrum map meets the covering definition by its single affine source, not by an unmentioned proper-descent theorem. Finally the affine-descent node is applied to $B\to\operatorname{Spec}k$, with affine base change $W\to\operatorname{Spec}L$.

For the B--E checklist I verified self-contained objects and all definition dependencies in the sole new node; it has no proof or proof dependencies. I searched before creating it and recorded only actual commands from the msearch log. The same-tag comparisons are individually distinguished above. Every use in the item is supported by a literal quotation from the cited statement in `citations.json`, which I checked for the exact part taken as described step by step here. The graph contains no reference to the parent quotient-existence theorem or any descendant depending on this item. No whole clause has been moved into a new node; the translate calculation and affine descent remain in the item's seven steps. No step exceeds the 2000-character review threshold.

I tested the empty set separately; repeated points cause no change; the nonempty group identity ensures the translate intersection is meaningful; reducible $Y$ is handled by including every component generic point; finite ground fields are handled by extending the closed intersection point's residue field; purely inseparable finite extensions are allowed and the tensor statement is about residue fields, not reduced fibres. Nonreduced finite groups and homogeneous schemes introduce no extra hypothesis anywhere. Nonclosed points are covered by the first specialization step. The datum is the actual scalar-extension datum of $Y$, rather than an unsupported existence of some quotient.

The off-unit statements are generic tools only: Jacobson closed points, closed-point residue fields, invariant affine shrinking, invariant-open descent and fpqc affine descent. These are declared in `split_report.tool_uses` where required; the unit's Milne finite-descent prerequisite is retained.

## Unfinished work

No part of this one-level split is left unfinished. The new rational-lifts statement remains intentionally unsplit for its own stage-1 worker. The unit's key theorem is not this item, so no unit realization fields are modified. The server-only preliminary review_split check passed. The first complete deliver.py --no-push also passed preflight at 71566a02f06. After final report typography and the explicit finite-dimensional wording in the supporting lemma, the final full dry run is repeated before the push.
