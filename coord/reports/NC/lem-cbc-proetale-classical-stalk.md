## Files written

dag/nodes/sec-smooth-purity/lem-cbc-proetale-classical-stalk.json — statement item, split into six steps; no Mathlib match for the complete item.

No new nodes. citations.json records a verbatim statement for every dependency of every step. All writes were in this item's sandbox. No Lean was written or compiled.

## Attachments

None for the item. Searches by blueprint tag, geometric-stalk terminology and strict-henselization terminology in the project source found no declaration giving all clauses of this item. The upstream master is reference only.

The auxiliary affine equivalence is proved by AlgebraicGeometry.WeaklyEtale.Spec_iff in WeilConjectures/AlgebraicGeometry/Morphisms/WeaklyEtale.lean:55 (lines 53–56). Its entry in local/sorry_map_slopmaster2_7d675a26.jsonl.gz has s=false, ts=false. This does not attach the whole item. More importantly, def-weil-pbc-ind-etale-algebra already explicitly states that very equivalence, so a proposed new bridge node was removed before delivery as a duplicate. Its definition is not being cited for a theorem it fails to state: its final sentence expressly equates scheme weak etaleness with the two ring-flatness conditions.

## WANTED

None. Read local Stacks sources proetale.tex, more-morphisms.tex and etale-cohomology.tex.

## Errors and corrections

The item statement is unchanged and agrees with Tag 0993, lemma-classical-point, and the preceding geometric-stalk paragraph in section-points, Tag 0991. The printed source's X_proet in the lemma is a harmless typo for S_proet; our statement consistently uses T. Added the strict-henselization structural-map definition to stmt_deps because the statement names its canonical map.

The proof uses all pointed weakly etale neighbourhoods, not a claim that pointed etale neighbourhoods are cofinal among them. Exactness is proved by splitting covers through the closed point and applying the general-site epimorphism criterion. Neither the etale-only exact-stalk lemma nor exact sections just over an algebraically closed field supplies this general statement; neither is cited. The supplied unit is sk-prop-sf-comparison, and the item realizes the ancestor's strict-local evaluation in Proof Step 3 and point evaluation in Proof Step 4. No unit or chapter route changed.

## Unfinished

None for the stage-1 split. Proofs of existing cited DAG nodes remain their own items; this delivery does not alter them. The second reader must review and deliver; nothing has been pushed.

## Not duplicates

No new nodes remain. Searches of the whole DAG and blueprint for 0993, 094Q, 094S, weakly etale morphisms, strict henselizations and stalks found existing tools that were reused. The only putative new lemma, the affine ring/scheme equivalence, was already an explicit clause of def-weil-pbc-ind-etale-algebra. The source-locality node states only locality on opens, so it is used for that purpose, not for any local-ring assertion.

## Review by NC

I read proetale.tex, section-points and the proof of lemma-classical-point (0991/0993): strict henselization is a site object by its filtered etale construction, and Olivier supplies initiality among pointed weakly etale neighbourhoods. I expanded that initiality rather than introducing a node that restated the stalk formula. I read more-morphisms.tex, lemma-weakly-etale-characterize (094S), and its affine proof, and etale-cohomology.tex, lemma-describe-etale-local-ring (04HX), with its chart/triple identification. These agree with the existing affine-chart ind-etale and marked-point statements. I opened every cited node's statement; quotations in citations.json are their actual statements, not facts borrowed from their proofs.

Step 1 uses clause (1) of lem-weil-pbc-strict-henselization-functoriality: it gives strictly henselian locality AND the factorization of each marked geometric point through the closed point. The weaker local-structure node explicitly omits this factorization, so I did not use it instead. The limit and structural-map definitions supply the projection over an affine open through t; lem-weil-pbc-strict-henselization-affine-chart-ind-etale applies with identity affine presentation of L and this exact structural ring map. Ind-etale stability supplies weak etaleness and composition. The explicit equivalence in def-weil-pbc-ind-etale-algebra passes between affine rings and schemes. The open-immersion-etale theorem makes the affine-open inclusion etale; the first sentence of def-weil-pbc-site-comparison-morphism explicitly includes etale T-schemes among weakly etale T-schemes and gives exactly the required global assertion. This avoids an uncited target-locality inference from affine charts. The pro-etale-site definition identifies weakly etale bounded objects. All colimits and skeleta are those of the item, in its stated universes.

Step 2 uses ind-etale stability for weakly etale base change and ring composition, source-locality only to restrict a weakly etale morphism to an affine open, the explicit affine equivalence, and lem-weil-pbc-localization-ring-weakly-etale for B_q. The prime q contracts to the maximal ideal of A because the marked point on L is closed. Thus Olivier's node, thm-weil-pbc-weak-etale-strict-local, applies to a local map of local rings with strictly henselian source. Its statement really gives an isomorphism; I use no stronger lifting conclusion from it. I construct the section by the inverse, and extend B→Omega to B_q to check the equality of geometric morphisms. The fibre-product definition supplies the marked pair and the projection back to U. This works for arbitrary weakly etale U, not only affine or finite-presentation U.

Step 3 is elementary after step 2: an open containing the maximal ideal contains a basic open of a unit; ring maps for sections therefore factor through the same chart and its localization. The inverse of A→B_q is unique. This proves uniqueness, including marked endomorphisms, and compatibility with every neighbourhood arrow; there is no unproved appeal to a monomorphism of U→T.

Step 4 uses exactly the stalk colimit in def-weil-proetale-geometric-stalk. It writes a universal cocone using the unique maps from L, so it works for sets and abelian groups without needing a filtered-colimit element theorem or a small-category existence lemma. The displayed restriction naturality equation proves functoriality, rather than saying only that the construction transports.

Step 5 uses the site definition to find a member over the closed point and to know its arrows are weakly etale. The same affine/localization/Olivier statements as in step 2 give a section of that member, with no unassumed geometric lift or separable-residue-field theorem. The general-site node lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective applies to arbitrary pro-etale abelian sheaves and gives the local lifts. Pullback by the section turns one into a global lift. Clause (1) of lem-weil-pbc-sheafification-exact explicitly states sectionwise computation of kernels and limits; it is not just a definition of sheafification. It proves left exactness of evaluation here.

Step 6 is the elementary abelian-category passage from kernels and epimorphisms to cokernels: factor through the image, use the two surjections, and identify the quotient group. The finite-colimit presentation by finite sums and their cokernel gives the remaining preservation. def-weil-pbc-sites-and-cohomology states the abelian sheaf category and the sectionwise morphism convention; no derived-category or coefficient-ring hypotheses enter.

Small cases checked: for T=Spec of an algebraically closed field the construction reduces to the identity pointed neighbourhood, including geometric points with larger Omega; over a non-separably-closed field it instead gives its separable closure, so no erroneous evaluation on T was used. For a positive-dimensional strictly henselian local ring the argument still uses localization at the marked closed point, not an open etale section theorem. For disconnected or nonaffine U the selected affine chart contains the marked point and every candidate section's image; no global affineness is assumed. For empty T there is no geometric point, so the quantification is vacuous. The split-cover argument cannot use an empty family on L, because a local ring with a field-valued point has nonempty spectrum. Zero abelian sheaves and arbitrary coefficient-free abelian sheaves obey the same lifting argument. No constructibility, qcqs or finite-presentation hypotheses were added.

Mathlib searches ran only through msearch.py, with two semantic phrasings and Loogle/grep checks. LeanSearch returned Internal Server Error and is recorded unavailable. The hits were read: the pro-etale site exists, but does not give the strict-local stalk formula; the ring/scheme weak-etale bridge belongs to the project source rather than Mathlib. Removing the proposed duplicate bridge, adding the actual open-immersion statement citation, and replacing an implicit target-locality inference by the explicit etale-object inclusion statement were the corrections made during this self-review. The off-unit nodes are generic geometry and sheaf-category tools, declared in split_report.tool_uses; they do not replace any comparison-unit step.

## Dry run

The first dry run printed OK (not pushed). A final source check tightened step 1 to use the existing explicit etale-object inclusion instead of implicitly invoking target-locality; the final dry run follows this correction.

## Second reading by NC

Item: checked hypothesis by hypothesis against proetale.tex Tag 0993 (`lemma-classical-point`) and the preceding Tag 0991 geometric-stalk paragraph; strict-local membership, canonical natural isomorphism and exactness agree.

Step 1: read the strict-henselization functoriality, limit/structural-map, affine-chart ind-etale, stability, open-immersion-etale, comparison-morphism and site statements; they provide the marked closed point, factorization and weak-etale membership claimed. Checked the affine presentation against etale-cohomology.tex Tag 04HX (`lemma-describe-etale-local-ring`). Verdict: valid.

Step 2: read the stability, source-locality, affine ring criterion, localization, Olivier, fibre-product and affine-spectrum statements; A is strictly henselian and the prime contracts to its maximal ideal, exactly Olivier's local-map hypotheses. Checked more-morphisms.tex Tag 094S (`lemma-weakly-etale-characterize`) and more-algebra.tex Tag 092Z (`theorem-olivier`). The displayed extension to Omega checks the marked morphism, not only the point. Verdict: valid.

Step 3: checked the affine-spectrum statement and elementary local-spectrum basic-open argument against the section constructed in Step 2; factorization through B_q and uniqueness of the inverse prove initiality and arrow compatibility. Verdict: valid.

Step 4: opened the current geometric-stalk definition, whose opposite index category and fixed-ring module diagram give precisely this colimit. Checked the terminal-object universal cocone and restriction naturality equation. Verdict: valid after replacing its stale citation quotation.

Step 5: read the site, source-locality, affine criterion, localization, stability, Olivier, local-surjectivity and sheafification-exact statements; covering surjectivity provides a point over the closed point without a geometric lift, and the local-map hypotheses again hold. Sectionwise limits and local lifting supply the two exactness assertions. Verdict: valid; expanded the inverse-ring-map section explicitly.

Step 6: checked the abelian-category and sectionwise additive conventions in the sites-and-cohomology statement; the image factorization plus preservation of kernels and epimorphisms gives the quotient cokernel, and finite sums/cokernels give finite colimits. Verdict: elementary and valid.

New nodes: none, so B1–B7 and independent Mathlib searches for new nodes are vacuous. Read every cited node's current statement, and searched the DAG source tags 0993/094S and the slopmaster2 strict-henselization/stalk vocabulary. No replacement or additional node is needed; the affine weak-etale bridge is already an explicit clause of the cited definition.

Small cases: an algebraically closed field gives identity strict localization even with larger Omega; a non-separably-closed field gives its separable closure. Positive-dimensional strictly henselian local spectra use localization, not a finite-presentation section theorem. Disconnected/nonaffine neighbourhoods reduce to the marked affine chart. Empty T has no geometric point; the zero abelian sheaf obeys all formulas. Verdict: no false strengthening or missing geometric hypothesis found.

Changes: refreshed the verbatim Step 4 quotation from the current `def-weil-proetale-geometric-stalk` statement; expanded the Step 5 section construction to avoid leaving “exactly as in Step 2” as its argument; appended this independent reading. Item statement and dependency lists are unchanged. The documented dry-run trailing dot is unsupported by deliver.py's parser; the same command without that redundant positional argument passed preflight.
