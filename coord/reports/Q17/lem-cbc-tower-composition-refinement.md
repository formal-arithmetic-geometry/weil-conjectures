# Worker report: lem-cbc-tower-composition-refinement

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-tower-composition-refinement.json: statement item, now split into five explicit steps; all hypotheses and the conclusion are unchanged. Mathlib search found no match.
- citations.json: verbatim statement excerpts for every step/node citation, including separate horizontal and refinement-normalization excerpts for step 2.
- report.md: this report and signed self-review.

New nodes: 0. Mathlib leaves: 0. No unit record is changed: this item is a subsidiary consequence, not the unit's key statement.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 checkout by the exact blueprint tag, tower-composition names, compatible-tower wording, and proper/open interchange. I read LowerShriekComposition.lean, LowerShriekComparison/CompositionLaw.lean and the refinement-comparison formalism. The nearby rightDerivedLowerShriekPlusCompIso_hom_eq compares a cartesian compactification triangle with chosen compactifications, whereas the present statement quantifies over the supplied u,v,w and uses the normalized proper/open map for a possibly noncartesian square. The refinement composition law compares successive refinements of one morphism, rather than the two-morphism tower. Neither declaration states all of this item. No attachment claim is made.

## WANTED

None. All source material needed is present.

## Audit and changes

The imported node had a statement but no proof. Its statement is well-typed; the direction of alpha is from the coarser open extension into the proper direct image from the finer model. I retained that direction throughout, rather than inverting the refinement comparisons. There is no statement dispute or source-route departure.

I read Stacks more-etale.tex, labels lemma-shriek-proper-and-open (0F7B), lemma-shriek-proper-and-open-compose (0F7C), and lemma-shriek-proper-and-open-compose-horizontal (0F7D), including both composition formulas and their proofs. I also read the current main-20261015 thm-cbc-finite-torsion proof, the recorded chapter and sk-prop-sf-cbc unit. The parent proof's final pasting assertion is the place this argument supplies. The resulting tower equation is an agent-formulated pasting consequence of these source equations, so proof_origin is agent, not a claim that Stacks prints the tower equation verbatim.

I searched the whole DAG for 0F7C and 0F7D and tower/composition wording, and used blueprint_refs search for proper refinements, compactification towers, composition commutes and refinement. The existing noncartesian interchange node supplies the two pasting identities. The formal lem-sp-compactification-refinement-coherence also contains a tower consequence conditional on abstract data; I did not introduce another node for that consequence or simply cite it to replace this item's argument. The strict-tower and complete-proetale variants use different coefficient categories and are not substitutes for this ordinary small-etale D^+ assertion. blueprint.same_as is []: the imported composition theorem has field/coefficient and pro-etale-origin restrictions and does not state this item with its supplied data.

The item's original search records are retained. Five new searches were run with msearch.py and copied from searches.jsonl, without altering the log: LeanFinder in two different phrasings, Loogle, grep, and LeanSearch. I read all returned signatures. CompactlySupportedContinuousMap and OnePoint statements concern topological maps, ordinary sheaf-pushforward compositors do not include derived proper/open comparisons, and Scheme.Modules statements concern structure modules. None states this item or specializes to it in one line. Loogle returned zero hits. No service failure was recorded as absence.

## Review by Q17

I reviewed the item against the above Stacks labels and opened the complete statements of every proof dependency: lem-cbc-compactifiable-compatible-tower, lem-cbc-etale-derived-direct-image-coherence, lem-cbc-extension-zero-composition, lem-weil-pbc-extension-by-zero-exact, and lem-cbc-proper-open-interchange-coherence. I also opened the alpha definition and the derived category, module direct-image and open-extension definitions used by the statement. This review is my author self-check; the maintainer's independent reading remains the subsequent review.

Step 1 uses the compatible-tower node for b_nu and c_nu being open and p_Y,nu proper. It does not use the tower's proof to infer any extra map. The direct-image coherence statement explicitly supplies the triple-composition and identity equations, and the open-composition statement explicitly supplies the corresponding open equations. The exactness statement explicitly preserves complexes and quasi-isomorphisms, so these degreewise open compositors descend to D^+. This step fixes notation and specified identifications; it does not assert that functor composition is literally strict.

Step 2 uses the interchange node's statement, which expressly permits noncartesian commutative proper/open squares. In the square R the horizontal maps are b_1,b_2 and the proper verticals are w,v. The adjacent square has c_1,c_2 horizontally and id_X,w vertically, with wc_1=c_2. Its outer square has a_1,a_2 horizontally and id_X,v vertically, because b_nu c_nu=a_nu. The refinement-normalization clause identifies its comparisons with the actual alpha_w and alpha_v, not arbitrary isomorphisms. The horizontal equation in that same statement gives alpha_v=(delta c_1!)(b_2! alpha_w) with exactly the displayed direction. Both used clauses have verbatim citations.

Step 3 uses the vertical equation in the same cited statement twice. R above tower 2 and tower 1 above the u-refinement have exactly the same outer rectangle, by p_Y,2 w=p_Y,1 and p_2 v=u p_1. I checked the resulting map's source i_2! S_1 and target U P_1 b_1!. Every vertical map used is proper, including the identity. The formula is (P_2 delta)(gamma_2 W)=(U gamma_1)(alpha_u S_1). This is not a claim that R is cartesian. No separate proper base-change fact is silently applied.

Step 4 is the component naturality equation of the cited natural transformation gamma_2, evaluated at alpha_w,K. Its source and target are written explicitly; in particular alpha_w has target W c_1! rather than c_1!. Only naturality and substitution are used, so the elementary flag is appropriate.

Step 5 substitutes the previous three identities and the definitions into one chain. I checked each intermediate functor: gamma_2 W c_1! is followed by P_2 delta c_1!, which is the left side of step 3; i_2! S_2 alpha_w becomes H_2 C_f after Q_2; alpha_u S_1 c_1! becomes C_h F_1. Finally Q_2 U gamma_1 becomes Q_1 gamma_1. Direct-image triple coherence identifies Q_2 P_2 V with Q_2 U P_1 and Q_1 P_1; open coherence identifies b_nu! c_nu! with a_nu!. Those are exactly the two statements this step cites. This is a short functorial substitution argument, not an unproved comparison lemma.

For the hypotheses I checked finite constant Lambda and ordinary small-etale bounded-below module categories at every invocation of the interchange theorem. Nothing passes to an unbounded, strict-tower or adic category. All required proper maps and opens are supplied by the item and the compatible-tower statement. No qcqs, Noetherian, constructibility or coefficient-invertibility condition enters the argument. The only off-unit proof input, open-extension exactness, is declared as a generic tool use in split_report.

Small cases checked: Lambda=0 and X empty make all component equalities equalities of zero maps; u=v=w identities reduce the identity to naturality with identities using the cited unit laws. For a genuinely noncartesian R, take X=Y=Z=Spec(k), f=h=id, barY_1=barX_1=Y disjoint union Y, barY_2=barX_2=Y, p_1=p_2=id, i_1=a_1 the first-component inclusion, and i_2=a_2=id. Set u=v to the fold map and w=id on U_1=U_2=Y; q_1 is the fold and q_2=id. Every stipulated proper map and relation holds. Here b_1 is the first-component inclusion and b_2=id, so R is not cartesian: the pullback of b_2 along v is Y disjoint union Y, rather than U_1=Y. Its comparison delta is the identity on the selected-component sheaf under the support identification. This checks precisely the noncartesian application used in steps 2 and 3. All schemes in this example are finite unions of points; the general argument requires no such restriction.

No new statement needs a separate small-case audit, and there are no new-node pairs requiring a Not duplicates section. I checked B1-B10 (no new nodes, no invented searches, filled blueprint provenance), C1-C8 (all non-elementary uses stated and cited; generic exactness tool declared), D1-D5 (the item itself carries its pasting argument), and E1-E7 (all maps, coefficients, directions and source hypotheses checked). All proof steps are below 2000 characters; the maximum is 1100, with no hidden long comparison lemma.

## Unfinished work

None in the mathematical split. The required server dry run and delivery are performed after this report is written.
