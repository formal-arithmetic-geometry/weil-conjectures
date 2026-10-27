## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite.json: statement, split; statement unchanged. Six proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-connected-semiabelian-subgroup.json: statement, unsplit; no Mathlib match. Statement only, with no proof, proof dependencies, or proof origin.
- citations.json: a verbatim statement quote for every proof-step citation.

## Attachments

None. Searches of lean/WeilConjectures by the item's blueprint tag, semiabelian terminology, and subgroup/torsion terminology found no exact declaration. Existing sorry-bearing Sheaf semiabelian constructions are not attachments.

## Wanted literature

WANTED: Brian Conrad, Semistable reduction for abelian varieties, Corollaries 3.2 and 3.3, printed p.8, for lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite and lem-sfb-smooth-connected-semiabelian-subgroup. The inherited local document path is not present. I read the author's PDF online at https://math.stanford.edu/~conrad/DarmonCM/2011Notes/SemistableReduction.pdf, including the full proof on p.8. I did not download it or write to literature/. The item proof is recorded as an agent expansion because the local source is missing and because the torus calculation is replaced by a direct geometric-series argument. No SGA source is used.

## Audit and corrections

There was no earlier sandbox split or report. I copied the live unsplit item and retained its statement, origin, citations, prior searches, and blueprint ancestry. There is no stage-1 repair note for this item. No statement dispute was found: invertibility of the prime is sufficient, and the conclusion is finiteness of the entire subgroup, not triviality of a possibly nonreduced or disconnected subgroup.

Conrad's printed reduction to the reduced identity component needed explanation for the full conclusion. I retained both the smooth reduced subgroup and the original subgroup throughout the proof, then used the existing component translation theorem and zero-dimensional closed-subscheme finiteness to recover the original object. I also avoided making the entire connected torsion argument a new node: the torus elimination and abelian dimension calculation remain actual proof steps of the item. No extra torus torsion-order node is necessary: a root of 1+X+...+X^(ell-1) gives a nonidentity ell-torsion point in any positive-rank split torus. The proof writes that calculation explicitly.

The sole new node is the subgroup-stability input of Conrad Corollary 3.2, stated concretely by a split torus kernel and fppf-locally surjective abelian quotient. This is strictly different from the item: there is no torsion hypothesis or finiteness conclusion. Its later split should follow the Chevalley-affine-part argument in Corollary 3.2; this argument belongs in that later split, not in this statement-only node. I read Corollary 3.2's proof immediately above Corollary 3.3. No SGA route has been imported from the earlier general quotient discussion.

## Blueprint and searches

Read the fixed chapter and unit records and the current latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability statement and proof. The item is a created local prerequisite in the inherited alteration/trait-homomorphism branch, not the unit's key statement, so no unit record is changed. blueprint_refs.py ancestor reports None for this item; the new node retains that value and prepends this item to the inherited via chain. Its from.place names the precise Corollary 3.3 use of Corollary 3.2. Whole blueprint searches for semiabelian, semi-abelian, semiabelian subgroup, semi-abelian subgroup, smooth connected subgroup and Corollary 3.2 found no matching blueprint theorem. Closed-subgroup and zero-dimensional searches were read and existing general tools reused.

I searched the entire DAG by semiabelian terminology, smooth connected subgroup terminology, Corollary 3.2/3.3 and the source title. Existing semiabelian multiplication, divisibility and density statements do not assert subgroup stability. Existing lem-sfb-abelian-closed-subgroup-reduced-component assumes an abelian ambient variety; it does not apply to a semiabelian ambient group with toric part. Its proof helped locate the existing component and zero-dimensional tools, which I reused directly.

All new-node Mathlib records are exact msearch.py queries present in this item's searches.jsonl, and I read their returned hit lists. Two semantic phrasings for subgroup stability return topological profinite groups, Lie groups and affine space, not algebraic subgroup-scheme results. Loogle's quoted semiabelian/subgroup search and the AlgebraicGeometry grep have zero hits. The item was also searched by two torsion/finiteness phrasings; abstract finitely generated torsion groups do not specialize to this scheme statement. None is a Mathlib leaf.

## Not duplicates

lem-sfb-smooth-connected-semiabelian-subgroup vs lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite: the new statement proves existence of a semiabelian extension structure for a smooth connected subgroup, with no torsion condition and no finiteness assertion; the item eliminates its torus and abelian dimensions under trivial prime torsion and recovers a possibly nonreduced disconnected subgroup.

lem-sfb-smooth-connected-semiabelian-subgroup vs lem-sfb-abelian-closed-subgroup-reduced-component: the existing statement assumes the ambient group is an abelian variety and concludes that the reduced identity component is an abelian variety; the new statement permits a nonproper semiabelian ambient group and a positive-rank torus in the resulting subgroup.

lem-sfb-smooth-connected-semiabelian-subgroup vs lem-sfb-geometric-semiabelian-split-quotient: the existing statement assumes its group is already geometrically semiabelian and descends/splits its torus after a finite Galois extension; the new statement establishes semiabelianity for a smooth connected closed subgroup whose extension structure is not assumed.

## Review by Q133

I read Conrad Corollaries 3.2 and 3.3 and their proofs, author PDF printed p.8, for both the item and the sole new statement. I read the statements of every cited DAG node and copied verbatim quotations to citations.json. I checked the underlying Stacks sources groupoids.tex Tags 047R (lemma-reduced-subgroup-scheme-perfect), 047P (lemma-reduced-group-scheme-prefect-field-characteristic-p-smooth), 03RP (proposition-review-abelian-varieties), 0BFG (lemma-degree-multiplication-by-d), and varieties.tex Tag 06LH (lemma-algebraic-scheme-dim-0). The identity-component node supplies the characteristic-zero companion 047N and Tag 0B7R. These are existing node inputs, not uncited black boxes in the item.

Step 1 uses the closed-immersion and finite-type definitions to obtain finite type for H by finite affine quotient covers. The existing locally-algebraic identity-component node expressly gives a clopen identity subgroup, its smooth connected finite-type reduction, and equality of their underlying spaces. The reduction definition expressly gives its closed immersion. The closed-immersion-products node expressly says closed immersions compose. Thus B is indeed a smooth connected closed subgroup of G, without assuming H reduced. I checked the subgroup operations are the inherited ones named by that component node.

Step 2 uses exactly the definition of subgroup as an injection on every algebra's points. A point killed in B maps to an H-torsion point and therefore to the identity, so injectivity forces it to be the identity. This is a functor calculation, not an inference from k-points to a nonreduced group scheme.

Step 3 uses the new subgroup-stability statement, whose hypotheses hold for B from step 1 and whose conclusion explicitly supplies the split torus, abelian variety and exact fppf sequence used subsequently. The new theorem has no torsion or finiteness clause and therefore does not relabel this item.

Step 4 uses algebraic closedness to obtain a root of the nonconstant geometric-series polynomial (ell is prime, so ell >= 2). Its value at 0 is 1 and at 1 is the nonzero image of ell. The root is a nonidentity unit whose ell-th power is 1. The split-torus definition identifies such coordinate tuples with torus points and the subgroup injection then contradicts step 2. Rank zero is handled explicitly by the empty-product convention; no torus order theorem is hidden in the step.

Step 5 removes the now trivial kernel by uniqueness of local lifts and the sheaf gluing axiom, writing the gluing argument and the representability identification. It then uses lem-sc-mult-n-finite-flat, whose statement explicitly gives finite kernel order ell^(2g), for the abelian variety B. The torsion scheme from step 2 has order one. This yields g=0 because ell >= 2. I checked that there is no use here of the false converse that every zero-dimensional group is the trivial scheme.

Step 6 uses the component node's topological equality and the translation node's exact statement that all components are clopen and isomorphic to the neutral component. The irreducible-chain argument is written out to obtain topological dimension zero for H. The final cited zero-dimensional closed-subscheme theorem assumes a closed subscheme of a finite-type scheme over any field and topological dimension at most zero, exactly what H inside G supplies. It explicitly asserts finiteness without reducedness. No properness assumption on G or H is used.

Small cases checked: H the identity; a finite constant subgroup of order prime to ell; H=mu_p in G_m in characteristic p with ell different from p; a positive-rank torus (its torsion violates the hypothesis); a positive-dimensional abelian subgroup (its ell-torsion order violates the hypothesis); rank-zero torus and zero-dimensional abelian quotient. The statement remains true in each case. The crucial invertibility condition was checked at P(1), so the elementary torus calculation does not silently assume characteristic zero.

Against delivery-errors B-E: the new node is self-contained and statement-only, each notion has a definition citation, no Mathlib match or attachment is claimed, no proof or proof dependency is placed in that node, all references have places and ancestry, and the item statement was retained. Every non-elementary proof input is a node citation with a matching statement; generic off-unit tools are declared in split_report.tool_uses. The new statement does not repeat the item or one of its conclusions. All steps are below 2000 characters and contain their elementary arguments. The component reduction and final finiteness avoid assuming smoothness or properness of H. The only unfinished work is the intentional future split of the one new statement-only node.

## Remaining work

None for this stage-1 delivery after the required dry run and push. One new statement-only prerequisite remains unsplit by design.
