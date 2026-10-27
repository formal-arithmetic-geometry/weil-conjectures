# Stage-1 report: lem-sfb-rosenlicht-connected-almost-complement

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rosenlicht-connected-almost-complement.json`: statement unchanged; split into ten proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-subgroup-equivariant-multiple-map.json`: new statement, unsplit; no Mathlib match after LeanFinder, LeanSearch, Loogle and source grep, including a second phrasing.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `report.md`: this report. The local extraction `milne.txt`, search log `searches.jsonl` and generation script `make_split.py` are scratch/research material only.

## Attachments

None. Searches for the exact blueprint tag and Rosenlicht / almost-complement / abelian-subvariety terminology in `lean/WeilConjectures/` found no declaration proving this item. A project sorry declaration would not have counted as an attachment. No Lean file was written or compiled.

## WANTED

None. The source used is the local `literature/milne-algebraic-groups_iAG2017.pdf`, especially pp.152–153 (8.18–8.24), pp.16–18 (components), p.104 (5.23) and pp.28–29 (images). Stacks Groupoids Tags 0B7R and 047R were also read in `literature/stacks-project/groupoids.tex`. There is no Stacks tag for Rosenlicht decomposition or Proposition 8.23; the actual Milne proposition is cited instead of inventing one. No SGA source is used.

## What was wrong or missing

The imported item was statement-only, with no proof to audit. Its statement is correct and has been preserved verbatim. Taking a smooth almost-complement's identity component requires a surjectivity argument; it does not follow just from the definition of identity component. Steps 7–8 supply this using the finitely many components of the original kernel and irreducibility of G. Similarly, normality after reduction is checked as a morphism on G times N, not merely on rational points.

The existing multiple-retraction lemma `lem-sfb-abelian-inclusion-multiple-retraction` applies only when the ambient group is an abelian variety, so it cannot supply Proposition 8.23 for a possibly nonproper G. The new node states precisely the equivariant map of that proposition. It does not state any complement or any clause of the item's conclusion. Its future split can follow the generic quotient torsor, positive-weight torsor averaging and Weil extension already present in the DAG. I did not put that future proof in its statement or proof fields.

The inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor` explicitly returns None. I retained the supplied precise place and via chain and gave the new node the same ancestor with this item prepended to via. I read the current latest blueprint's direct-images proof (3); the algebraic-group argument is a subordinate input in the existing chain, not a change to a unit or chapter route. No unit realization record is due for this supporting lemma.

## Not duplicates

lem-sfb-abelian-subgroup-equivariant-multiple-map vs lem-sfb-abelian-inclusion-multiple-retraction: the existing statement requires both source and target to be abelian varieties; the new source is any smooth connected separated finite-type group. The new conclusion is an equivariant scheme morphism, before normalization and homomorphy.

lem-sfb-abelian-subgroup-equivariant-multiple-map vs lem-sfb-commutative-torsor-positive-weight: the existing statement concerns a torsor over a field under a commutative group and gives a map from that torsor; it does not extend a generic-fibre map over G or state a morphism from a general group to its abelian subgroup.

lem-sfb-abelian-subgroup-equivariant-multiple-map vs lem-sfb-abelian-product-axis-rigidity: the existing statement forces a supplied two-variable map with trivial axes to be trivial; it constructs no equivariant map or positive multiple.

lem-sfb-abelian-subgroup-equivariant-multiple-map vs lem-sfb-rosenlicht-connected-almost-complement: the new map theorem has no subgroup N, finite intersection, product surjection or dimension formula. The item's proof constructs those from its kernel. It therefore supplies a smaller input rather than moving the conclusion into a new node.

Whole-DAG searches included 8.23, 8.19, multiple-retraction, equivariant abelian maps, and abelian subvarieties. Whole imported-blueprint searches were made with `tools/blueprint_refs.py search` for Rosenlicht, almost complement, 8.23, retraction, equivariant map and abelian subvariety. The latest blueprint was also searched directly. No blueprint equivalent exists. All cited existing node statements were opened; specialized affine/matrix group results were deliberately not applied to G.

## Review by O1

I read Milne's proof of Theorem 8.24 and its immediate input Proposition 8.23 with Lemma 8.22. The latter's integer is positive: it is 1 when a rational point exists and otherwise the positive degree of the separable residue field. The new statement is a restriction of 8.23 to the algebraically closed case and to the stated central subgroup. No assumption that n is invertible in k is made. I also checked the component and reduction facts in Stacks 0B7R and 047R against the reused node statements. The report retains the current item statement and its actual hypotheses.

Step 1 uses exactly the new equivariant map, group operations, commutativity of an abelian variety, geometric irreducibility of a connected algebraic group and geometric reducedness from smoothness. The existing product-axis rigidity node has smooth separated geometrically integral factors and does not require proper factors; I verified those hypotheses for G before applying it to the normalized difference map. This avoids incorrectly applying the proper-source rigidity lemma directly to a general G.

Step 2 uses the non-affine homomorphism factorization node, whose statement actually supplies a closed normal kernel of finite type, and the locally algebraic identity-component node, whose statement supplies the smooth connected reduced neutral component. The closed-immersion composition node supplies closedness in G. A's properness supplies separatedness and finite type. No affine homomorphism theorem is used here.

Step 3 uses the same geometric irreducibility theorem for G and N, the geometrically irreducible product theorem, the open-factorization theorem and the perfect-reduced-tensor theorem. Its source is reduced on product affine charts; the algebraically closed field is perfect, including positive characteristic. The reduced-source factorization theorem therefore applies to the conjugation morphism into K^0. This gives normality on every test algebra as required by the subgroup definition. Neither a rational-point argument alone nor the definition of reduction is used as a substitute for this factorization.

Step 4 is the written two-line centrality calculation plus the affine-chart and diagonal checks for a product; the closed-immersion product theorem says exactly the latter. It is elementary relative to those statements, not an unstated product-image theorem.

Step 5 uses the closed-immersion base-change clause of proper-fp-permanence to obtain the intersection. I checked the factorization through A[n] and wrote the affine quotient argument showing it stays closed. The multiplication-isogeny node explicitly gives finite A[n], and closed immersions are finite and finite maps compose by the two quoted nodes. The displayed inverse pair identifies the entire kernel on all test algebras, including nonreduced algebras. It does not claim the finite intersection is reduced.

Step 6 applies the general finite-type homomorphism theorem to the separated finite-type product. Its quoted statement supplies a closed image and faithful flatness with finite presentation, not merely dominance or flatness. Step 7 uses the exact finite component and translation statement for possibly nonreduced, non-affine K. Its neutral component's k-points equal those of its reduction by reduced-source factorization. I replaced an unnecessary fibre-closed-point argument by the existing `lem-sc-isogeny-surjective`, whose statement is precisely surjectivity of [n] on A(k) over an algebraically closed field. Centrality moves a past the component representative. All hypotheses n>=1 and k algebraically closed have been checked.

Step 8 uses translations being isomorphisms, the rationality of closed points and their Jacobson density to turn the finite covering of rational points into a finite closed covering of |G|. Irreducibility then gives a full-support translate. The final passage from full support to an isomorphism uses reducedness of G and the cited reduced-source factorization theorem, rather than identifying closed subschemes solely from their support. The finite-union argument is written out and introduces no separate hidden lemma.

Step 9 uses only the finite-surjective dimension statement, applied to the nonempty finite F over Spec k; it therefore proves dim F=0 even for a nonreduced kernel. Step 10 checks the actual quotient convention in the homogeneous quotient dimension node. The homomorphism theorem supplies a represented fppf quotient; m is also fpqc, and fpqc descent of compatible morphisms supplies its fpqc coset universal property. The pointwise kernel identity gives precisely the descent relation. Thus the dimension theorem is applied to the quotient it states, not an unrelated per-fibre dimension formula. The existing product dimension node finishes the addition. The dimensions are finite by the quoted homogeneous quotient statement.

Every proof dependency equals a node actually used, and `citations.json` quotes the corresponding complete statement verbatim for each step. Generic off-unit tools are declared in `split_report.tool_uses` for the maintainer's review. I checked the new node is statement-only, self-contained, has all its notion dependencies, records actual logged searches with actual no-match verdicts, has no id collision and introduces no cycle through this item. No step exceeds 2000 characters. All non-elementary facts are supplied by named statements; the elementary algebra, affine quotient, finite closed-cover and inverse-pair arguments are written in their steps instead of becoming new nodes.

Small cases checked: A=1 gives r=0 and N=G; G=A permits N=1 and finite kernel. A product A times an arbitrary smooth connected affine group is covered. Positive characteristic with p dividing n is allowed: A[n] and ker r can be nonreduced, so reduction is applied only to the complement. A disconnected kernel has finitely many translated components, which is exactly the case handled in steps 7–8. The zero-dimensional G case reduces to the trivial smooth connected group. Dropping connectedness would break the irreducible finite-cover argument; the hypothesis is retained. The new equivariant-map statement also holds when A is trivial or equals G, so it has no small-case counterexample. No statement dispute was found.

## Unfinished work

The new equivariant-map node is intentionally left unsplit as required for a one-level stage-1 delivery. No part of this item's proof is left as an unlabelled assertion or an attachment claim.

## Validation

The preliminary server `review_split` returned PASS. The full required dry run and delivery follow after this report is written; their final outcomes are recorded in the delivery tool output.
