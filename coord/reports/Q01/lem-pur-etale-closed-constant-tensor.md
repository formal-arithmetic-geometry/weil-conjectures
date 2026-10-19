## Worker report

Item: lem-pur-etale-closed-constant-tensor. Group: Q01. Stage 1 only.

Files written: dag/nodes/sec-smooth-purity/lem-pur-etale-closed-constant-tensor.json (split into nine steps, no Mathlib match), citations.json, and this report. searches.jsonl was written by the required msearch.py calls. No new nodes, no new Mathlib leaves, no Lean files, no compiler or build invocation.

Attachments: none. Searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint id and for closed/constant and tensor/stalk terminology. The relevant KummerClass.lean supported-class constructions and StalkMonoidal.lean tensor-stalk declarations do not state all the item's assertions, with its arbitrary commutative ring and arbitrary morphism hypotheses. They are not attachments for this item. The upstream master is reference material only.

WANTED: none.

The original item had a statement and no proof. Its statement is retained mathematically; the only textual additions are the missing definition citations for constant sheaves and derived tensor. Its source already explicitly identifies this as an agent-formulated refinement, so proof_origin remains agent-authored. I have not attributed multiplication, flatness or its compatibilities to 03Q1 alone.

All nine steps are complete. No new statement-only lemmas are needed: the substantive tools already have nodes, and the remaining arguments are evaluation, tensor universal properties, and the two-case calculation A or zero. The two steps marked elementary are the explicit adjunct-composition calculation and the associativity/commutativity calculation, rather than any stalk theorem.

## Existing nodes and blueprint search

Read the item's chapter and sk-prop-a1-kummer unit. Read the current main-20261015 frame-independence proof at sec-smooth-purity/sk-prop-an/lem-pur-frame-independence.proof.md and the already repaired DAG proof of that ancestor. This helper supplies the closed-support source calculus for lem-pur-supported-cup-functoriality; it replaces no step of the unit or the smooth-purity route. The ancestor's old false Smith-normal-form/constant-sheaf assertions are not used.

Ran blueprint_refs.py ancestor on the item: the nearest blueprint ancestor is lem-pur-frame-independence. Ran blueprint searches for 'stalk tensor', 'closed constant', '04FX', 'flat sheaf', 'tensor', and 'constant', and searched the full DAG by the same notions and by titles/ids. The flat-sheaf hit pur9-def-flat-sheaf is a coefficient-specific definition, not the theorem. The existing inverse-image-closed-pushforward-constant and closed-pushforward-constant-stalks nodes concern sheaves on topological spaces, not small etale sites. They were read and excluded as citations here. The existing etale closed-pushforward node lemma-openclosed-stalk-lowerstar is the right on-support comparison; the off-support case is the explicit empty-complement argument in step 2. No blueprint node states this complete closed-constant tensor and arbitrary-pullback theorem, so blueprint.same_as remains [].

## Mathlib searches

The searches run in this sandbox were exactly:

- leanfinder: closed immersion direct image constant etale module sheaf tensor intersection flat pullback
- leansearch: The direct image of a constant sheaf along a closed immersion is flat and tensor products correspond to intersections
- loogle: CategoryTheory.Sheaf
- grep: closed.*(constant|tensor)|constant.*closed (CategoryTheory/Sites)
- leanfinder: geometric stalks of closed immersion pushforward constant coefficients are the coefficient ring on the closed subscheme and zero outside

All services returned successfully. Read the returned types: they concern scheme-flatness, formally etale algebras, Zariski structure-sheaf stalks, constant-sheaf membership, or general sheaf categories. In particular Sheaf.tensorProd_isSheaf describes Cartesian tensor, not the module tensor in this item. None states the item or specializes to its full conclusion in one line. The grep returned no hits. These queries and verdicts are appended to the item's prior searches, and the required tool's own log is retained.

## Source correction in a dependency

lem-pc-bounded-above-flat-kflat-site has exactly the general ringed-site statement needed in step 9. Its source.place calls it 06YS. I checked the local tags/tags table and sites-cohomology.tex: the bounded-above-flat theorem is Tag 06YQ, label lemma-bounded-flat-K-flat, at lines 3119 onward; 06YS is lemma-K-flat-resolution. This is a source-label error in an existing dependency, not an error in its statement. Step 9 cites the correct source tag. I have not edited that other node.

## Not duplicates

No new nodes. In particular I did not create a separate node for any conclusion clause, for the elementary A-tensor calculation, for flatness from the two-case stalk formula, or for degree-zero localization of already proved equalities.

## Review by Q01

I read etale-cohomology.tex Tag 03P5 (remark-constant-locally-constant-maps), Tag 03Q1 (lemma-stalk-pullback, especially its explicit colimit formula in part 3), Tag 04FX (lemma-stalk-pushforward-closed-immersion, including the empty-complement case), and Tag 03PU (theorem-exactness-stalks). I also read sites-modules.tex Tag 03EL (lemma-tensor-product-pullback, including its adjunction/bilinear-map argument) and sites-cohomology.tex Tag 06YQ (lemma-bounded-flat-K-flat). These sources justify the tools; the refinement's actual maps and calculations are written in the item's steps, not asserted to occur in those sources. There are no new nodes whose source needs separate review.

1. Step 1 uses the statement of lem-weil-pbc-constant-module-locally-constant, which explicitly supplies the natural locally constant model with precomposition restrictions and postcomposition coefficient maps for every ring and module. It uses prop-weil-pbc-inverse-image-modules-exact clause (3), which supplies the module adjunction with the underlying abelian unit, and the closed-immersion base-change and composition statements, which supply the actual closed supports. I checked that none needs finite type or separatedness. The precomposition formula proves the proposed map is linear and natural; it is not an unnormalized existence claim.

2. Step 2 uses lemma-openclosed-stalk-lowerstar's initial neighbourhood functor, not a Zariski stalk theorem. This specifies the on-support stalk comparison by restriction of represented sections. The constant-sheaf-geometric-stalk node specifies constant germs and their bijection. The constant-module-sheaf-underlying node identifies the same underlying abelian constant sheaf, compatible with those germs. Its naturality makes the resulting comparisons A-linear. For the outside case I wrote the refinement by the actual open complement; the definition of geometric stalks then gives zero. The affine quotient in def-weil-closed-immersion proves factorization of the field-valued point, with no reducedness assumption on C.

3. Step 3 uses inverse-image-stalk-germ's actual unit-germ formula, and the module inverse-image proposition's compatibility with that unit and with the canonical constant-ring map. This is stronger than merely knowing some stalk isomorphism exists. The pulled-back function has value s(v x'), so the map is identity in the A case and zero in the zero case. The cited geometric-stalk-conservative statement is about all etale abelian sheaves, and applies to the underlying map; a linear bijection has a linear inverse. The restriction-square calculation uses the same canonical constant-ring identification, not an arbitrary automorphism of A.

4. Step 4 uses all the necessary unit equations in inverse-image-composition: direct-image comparison, the characterization of the inverse-image comparison, and the identity case. The module inverse-image proposition says its units are the same after forgetting. Both adjuncts send s to the same twice-precomposed function, so uniqueness of adjuncts proves the equality. This is a routine calculation from these stated equations, not an uncited coherence theorem.

5. Step 5 constructs multiplication by the balanced pairing before testing it. The tensor definition gives the factorization through sheafification. The etale-stalk-tensor-scalar node explicitly gives both the pure-tensor germ formula and naturality; it is applicable to arbitrary commutative A and ordinary etale module sheaves. I addressed the difference between tensoring sectionwise over A and over A_X(T): a locally constant scalar is constant after an etale open cover, so the additional balancing relations already hold locally and hence in the sheafification. I checked the A-case inverse a -> a tensor 1 and all zero-factor cases. Geometric-stalk conservativity then proves the actual constructed map is an isomorphism.

6. Step 6 uses the module-category statement for kernels/cokernels, exactness of geometric stalks, and the natural tensor-stalk comparison. It does not cite the definition of flatness as if it proved exactness. The short exact sequence becomes itself or zero on every stalk. I wrote how the kernel, middle homology, and cokernel vanish using exactness and conservativity, so no separate non-elementary flatness criterion is hidden here. The flatness definition is used only to name the resulting exact-functor property.

7. Step 7 uses only the sheaf-tensor universal property on the constructed section pairings. The two triple products are (ab)c and a(bc) on the actual triple fibre product; interchange gives ba=ab. Equality on section tensors determines sheaf maps. This step proves the claimed coherence, rather than citing a node for merely an unspecified tensor equivalence.

8. Step 8 uses canonical-ringed-tensor-comparison-construction together with the comparison definition. The former asserts existence for the specified pullback presentation, and the latter explicitly specifies the generalized pure-tensor normalization. The exact-module-pullback proposition supplies precisely that geometric inverse-image module functor and canonical ring identification. The inverse-image-germ node then identifies the stalk comparison on these specific unit images. On intersection stalks both paths multiply a and b; outside they vanish. Exact stalks and conservativity make the image of the difference zero, proving equality of maps. The source sites are taken in a universe in which their small skeletons and module sheaves exist, as permitted by the site/module-category definitions; no non-small colimit theorem is applied.

9. Step 9 uses the general ringed-site bounded-above-flat criterion, not the similarly named node restricted to ringed spaces. It also uses site-derived-tensor-descent's explicitly natural computation on flat-term K-flat models, the total-tensor definition, and exactness of module inverse image. Each complex is in degree zero, so its tensor has only one nonzero summand and zero differential. Its output P_I is again flat, allowing the same computation for the triple tensor. The canonical sign is 1, and localization preserves the already established equalities. Exact inverse image computes the derived inverse image termwise because it preserves kernels/cokernels and hence quasi-isomorphisms; its pulled-back terms are the flat terms identified in step 3. Thus the derived comparison is computed on the same specified models.

I checked all citations against the cited statements and copied their relevant statements verbatim into citations.json (one entry for every step/node pair). Generic tool uses outside the item's unit are declared in split_report.tool_uses, with the precise use and why they are generic; I set no maintainer-owned tool_uses field. These tools prove site, tensor, or localization facts and do not replace the unit's purity route.

Small cases checked: A=0; X empty; C empty; C=X; C and D disjoint; C=D; a third support empty; identity v; a v whose image misses C; and nonreduced closed subschemes such as V(epsilon) in Spec(k[epsilon]/epsilon^2). The formula yields only A or zero and remains true in all these cases. No step imposes a finite-type, separatedness, Cartier, nonzero-ring, or reducedness hypothesis. The maps are determined by actual functions, so nilpotent thickenings cause no additional identification assumption.

All proof steps are shorter than 2000 characters. I reviewed them for hidden comparisons and standard lemmas anyway: all non-elementary inputs are named; elementary identity/zero and multiplication calculations remain steps, not new nodes. I corrected the missing coefficient-model justification and the existing dependency's misprinted source tag in the account above. There is no statement dispute and no unresolved mathematical gap.
