# O1 stage-1 delivery: lem-sfb-affine-saturation-cartier-boundary

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-saturation-cartier-boundary.json: item, statement, split into eleven proof steps; no Mathlib match.
- citations.json: one literal statement quotation for every use in every item step.
- report.md: this report. The sandbox also retains the actual searches.jsonl, a read-only-source index and the script used to write the split. These auxiliary research files are not DAG deliveries.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched lean/WeilConjectures for the exact item id, Cartier boundary, saturation and the action terminology. The blowup boundary declarations concern changing a scheme by a blowup; they do not assert this item's boundary on an unchanged group saturation. There is no exact finished project declaration to attach. I did not compile or write Lean.

## Wanted literature

WANTED: Michel Brion, Algebraic group actions on normal varieties, arXiv:1703.09506v3, Section 3.2, Proposition 3.3, first proof paragraph, for lem-sfb-affine-saturation-cartier-boundary. The local PDF path in the item does not exist; I read the primary HTML at https://arxiv.org/html/1703.09506v3 online. Its Cartier argument uses the smooth action map and the fact that the boundary contains no action fibre, then restricts back along the identity. I implement that argument through the existing smooth affine-boundary criterion and descent of the specified ideal, without claiming ampleness.

WANTED: Ning Guo, Divisors on coherent schemes and homogeneous spaces, March 31, 2026, Proposition 3.3 (iii) implies (i)/(ii), printed pp.6--7, for the existing supporting node lem-sfb-smooth-normal-affine-boundary-cartier. The local PDF is absent. I read https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf, including its last proof paragraph invoking the Noetherian Ramanujam--Samuel result. The supporting node already states the needed locally Noetherian reduced-boundary specialization. I do not introduce another version or claim to prove that supporting node here.

## What needed correction or clarification

The imported item had no proof. Its mathematical statement is preserved, including disconnected normal schemes, the scheme-level invariance, omitted components and the empty divisor. I normalized doubled TeX backslashes in its statement; this changes rendering only. There is no mathematical statement dispute.

A pointwise equality hW=W for h in G(k) alone is not scheme-level invariance. Step 2 supplies the missing finite-type closed-point detection argument. Fibrewise density is checked for all residue fields, not just closed points. A Cartier divisor cannot in general be pulled back along an arbitrary section while retaining a non-zero-divisor. Instead steps 8--11 identify the actual smooth pullback of the reduced boundary and apply the existing fpqc ideal-reflection statement. This also avoids an implicit assertion that reduced structures commute with all base changes: only smooth pullback is used.

The item's blueprint.from.node is null in the current repository and the ancestor command returns None; I preserve that existing ancestry and its detailed place. The current blueprint latest points to main-20261024. I read the current sk-thm-sf-ctf-stability section and its direct-images proof, whose detailed proof identifies itself as det-thm-sf-ctf-stability-direct-images. This item is a supporting geometric input far below that proof, as its inherited place records, not the unit's key statement; no unit or chapter file is changed.

## Not duplicates

There are no new nodes. In particular, I reuse lem-sfb-smooth-normal-affine-boundary-cartier, rather than create a second Ramanujam--Samuel input. I reuse lem-trf-smooth-reduced-dense-pullback, lem-sfb-normal-locally-finite-components and lem-trf-fpqc-cartier-ideal-reflection for their existing statements. The affine-open codimension-one node does not itself imply Cartierness, and the invariant quasi-projective neighbourhood node depends on this item; neither is used as a substitute proof.

I searched the entire DAG by boundary/Cartier, smooth reducedness, normal components, group irreducibility and fpqc ideal descent, and searched the imported blueprint with blueprint_refs.py for Cartier, Ramanujam, saturation and smooth normal affine boundary. The only blueprint saturation hit was the unrelated affine scheme-image saturation lemma. No blueprint node states this assertion in another form, so same_as remains []. The precise source paragraph for this supporting item was already filled in blueprint.from.place and is retained.

## Mathlib searches

The historical item searches are preserved. I ran fresh msearch.py searches under O1 and this item, and read the returned hits:

- leanfinder: An affine open in a normal variety has Cartier boundary in its saturation under a smooth connected group action.
- loogle: AlgebraicGeometry.Scheme, "Cartier".
- grep in AlgebraicGeometry: Cartier.*saturat|saturat.*Cartier|Ramanujam|Sumihiro.
- leansearch: The complement of an affine open becomes an effective Cartier divisor after taking translates by a connected smooth algebraic group.

All services answered. Loogle and grep had zero hits. The semantic searches returned basic affine-open APIs, normalization-open APIs, a coborder-range definition, a group action complement identity and an affine-composition instance. None gives a Cartier divisor on an affine saturation, nor a one-line generalization of it. Both semantic phrasings were read before concluding no match. Exact queries and actual summaries are retained in searches.jsonl and mathlib_searches; no unavailable service is classified as a failed mathematical match.

## Review by O1

I checked this split against delivery-errors B--E with the item, every cited statement and the relevant primary source passages open. Brion Section 3.2 supplies the action-map route, and Guo Proposition 3.3 supplies the already recorded smooth-family criterion. The Stacks text I read includes groupoids.tex lemma-group-scheme-field-geometrically-irreducible (047M), descent.tex lemma-reduced-local-smooth (034E) and lemma-normal-local-smooth (034F), and morphisms.tex lemma-affine-permanence (01SG). There are no new statements whose hypotheses or data need to be reconstructed by another worker.

1. I checked that finite-type-over-Noetherian applies over Spec k and that the open-subscheme lemma gives quasi-compactness even for the infinite union of translates. The noetherian-open/closed finite-presentation statement applies with the closed immersion the identity. The quasi-compact-open finite-type and composition/base-change statements give finite type of W and products. Normality is equality of stalks on opens. Separatedness restricts the actual diagonal; the separated-over-affine lemma supplies the absolute separatedness needed later.

2. I read the Jacobson-space statement: it gives closed AMBIENT points in any nonempty closed subset, exactly the C used here. I read closed-point-field (a): the field is finite over k, so algebraic closedness makes it k. This gives a rational pair, not just two unrelated points of the product. The open-factorization statement gives the restricted scheme morphism; the monomorphism clause of noetherian-open/closed finite-presentation reflects the action identities. Thus no action for nonrational points is inferred solely from rational-point notation.

3. Smooth-geometrically-normal gives normality and reducedness of G. Open-subscheme-Noetherian and finite-components statements verify the locally finite-component hypothesis of normal-locally-finite-components on EVERY quasi-compact open. The latter node states disjoint clopen integral components and equality with their reduced structures. Connectedness forces one component. The last clause of group-local-minimal-prime gives geometric irreducibility of the reduced identity component, now G itself. This is stronger than irreducibility only over k and is what step 6 needs.

4. I verified the finite-presentation hypotheses explicitly: the affine smooth group is quasi-compact and separated, and smoothness includes local finite presentation. The base-change lemmas really give smoothness, separatedness and finite presentation of the projection. The inverse twist uses the morphism inverse in the group scheme, not an inverse on underlying closed points. The supplied isomorphism invariance of smoothness is in smooth-restrict-open-subschemes (c); diagonal and presentation data transport directly for the other properties.

5. The affine-opens-basis node supplies all T, not just a fixed cover chosen on rational points. The base-change statements retain the three required properties of Y_T/T. The fibre product of the affine G and U is affine by the explicit tensor-spectrum statement. I checked that affine-source-separated-target demands absolute separatedness, established in step 1. The definition of affine morphism then gives the affineness of V_T. I never infer an arbitrary intersection of quasi-separated affine opens is affine.

6. This step is elementary after steps 3--5: the displayed inverse fibre isomorphism is checked by the group identities. For an arbitrary topological t, membership in a rational translate produces a point over its own residue field through the canonical residue-field morphism and open factorization. A nonempty open of an irreducible fibre is dense. No condition that U meet every component of X is used.

7. I compared all hypotheses with the literal smooth-normal-affine-boundary-cartier statement: affine locally Noetherian normal base; smooth separated finite presentation map; affine source open; density in EVERY fibre. They all hold. The cited node states precisely that the reduced boundary is effective Cartier, not merely a Weil divisor or a Cartier divisor with an unspecified support.

8. The reduced-induced-closed-subscheme node gives a quasi-coherent ideal, a reduced closed scheme and its exact support. I checked proper-fp-permanence (c) for finite type of the closed immersion (proper includes finite type), then composition/base-change and finite-type-over-Noetherian give Noetherianity of D. Smooth base change and the reducedness clause of smooth-reduced-dense-pullback make G x D reduced. I use only its reducedness conclusion, not its density conclusion or any trace-formula assertion. Proper-fp-permanence (b) gives the closed pullback immersion.

9. The uniqueness clause (3) of reduced-induced-closed-subscheme states equality of ideal sheaves, which is exactly what is required to identify the Cartier ideal on each Y_T. This argument is not just equality of underlying sets. The local-generator definition of effective Cartier ideal allows these local conclusions to assemble without choosing or gluing arbitrary equations. The Y_T cover because affine T cover the action target W.

10. I checked the covering DEFINITION rather than assert that every surjective smooth map is fpqc. Smooth-flat gives flatness. G x T is one affine open of the source, and the identity section gives surjectivity onto T. This meets the finite affine-open image test in fpqc-covering verbatim, including empty T.

11. Fpqc-cartier-ideal-reflection takes an actual closed subscheme and its quasi-coherent ideal with inclusion; its hypothesis is exactly the Cartier ideal of its pulled-back closed subscheme. Step 9 supplies that hypothesis and step 10 the cover. Its conclusion explicitly permits the unit ideal, retains the ideal inclusion and gives local non-zero-divisor generators. Thus this step proves the stated scheme-theoretic divisor conclusion and the empty case.

Every use has a literal quote in citations.json. I compared the clause being used, not only node names or proofs. No cited definition is being used for an unstated theorem. All elementary steps write the short argument, and no non-elementary step exceeds 2000 characters. The proof contains no hidden generic-to-global identification: reducedness and the fpqc reflection have their own cited statements.

I checked small cases: U empty; X empty; U=W; a trivial group/action; P^1 with its transitive PGL_2 action and U=A^1; disconnected normal X with U meeting only one component; and U with several nonempty components. In the trivial action W=U and the ideal is the unit ideal. For a disconnected X, no ignored component is added to W, and the residue-field fibre argument still works verbatim. These cases also show why a general affine complement on a normal scheme is not simply declared Cartier: the fibrewise-density input is essential. No integrality of X, smoothness of X, or quasi-projectivity has been added.

The off-unit statements are listed as tool_uses in split_report. They are generic properties of schemes, algebraic groups, smooth pullback and rank-one ideal descent, not replacements for a six-functor unit step. The trace-formula-filed nodes are used only for those generic geometry statements; no trace formula, Poincare-duality route or SGA source is used. I created no restatement node, elementary node, duplicate or hidden proof in a statement-only node.

## Unfinished work

None for this one-level split. The already existing smooth affine-boundary input remains an unsplit DAG item, as allowed in a one-level split. Full independent maintainer review still follows delivery.
