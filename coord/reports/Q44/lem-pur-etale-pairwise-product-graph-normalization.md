## Files written

- dag/nodes/sec-smooth-purity/lem-pur-etale-pairwise-product-graph-normalization.json: statement, split in ten steps; no Mathlib match.
- citations.json: verbatim statement quotations for all forty step/node citations.
- No new DAG nodes and no Mathlib leaves. Searches are preserved in searches.jsonl; write_split.py is a sandbox-only preparation script.

## Attachments

None. I searched lean/WeilConjectures by the exact blueprint tag and by graph comparison, product graph, and two-neighborhood terminology, then read LowerShriekComposition.lean:193-268. The declaration AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriekOfCompactification gives existence of an isomorphism from one compactification to one proper/open/proper presentation; it does not state equality of the specified pairwise graph comparison with the displayed lambda word. It is not an attachment for this item.

## WANTED

None. The agent extension is proved using the present Stacks source and existing unbounded module comparison nodes, rather than advertised as a theorem stated verbatim in Stacks.

## Problems found and changes

The item was unsplit and had no proof. Its statement and statement dependencies remain unchanged. No counterexample or typing fault was found. In particular the square E_nu really is Cartesian even though its lower open map need not be proper: monomorphy of that open immersion and the factorization z_nu=v_nu a give the pullback identification with X.

The ancestor command reports blueprint.from.node=None through the inherited created.item chain; I retained that inherited metadata. The latest blueprint places sk-prop-sf-cbc and sk-thm-sf-comp-composition under sec-six-functors-basics, while this DAG item retains its assigned chapter sec-smooth-purity and unit sk-prop-sf-cbc. I changed neither chapter nor unit. I read the latest composition proof's canonicity paragraph as the motivating place and followed the item's existing finite-coefficient ordinary-etale route, not the proetale assertion in that paragraph.

The proof of the existing graph-comparison/base-change node contains related calculations, but I have not cited its proof as a theorem. Its statement is used only for the definition C=B B^{-1}. The necessary product projection and intersection calculations are explicitly reproved in steps 3 and 5-9 from the exchange-cube node's stated pasting equations. This avoids taking the desired normalization from an unstated clause of that existing node.

The Stacks tag for composition of proper morphisms is 01W3, label lemma-composition-proper, not 01W5 (the latter is closed-immersion-proper). The proof's source places use the checked tag 01W3.

## Unfinished work

None in this one-level split. Existing non-Mathlib dependencies retain their own states and require their own work. No Lean was written or compiled.

## Search and duplicate review

Before deciding whether a new lemma was needed I searched the whole DAG for 0F7B, 0F7C, 0F7D, 0F7J, graph-comparison, pairwise product, and product graph, and ran blueprint_refs.py searches for graph comparison, pairwise product graph normalization, product graph, and compactification comparison. The existing proper base-change, proper composition, proper-to-separated, open-base-change, graph-model and exchange-cube statements provide all tools. No new node was created. The blueprint search found no equivalent assertion to record in same_as.

I read the pre-existing Mathlib searches and their actual results and ran fresh logged leanfinder, loogle, grep and leansearch queries, followed by a second leanfinder phrasing. The hits concern ordinary sheaf pushforward composition, manifolds, compact support in topology, gluing and limits of schemes, and Proj charts. None states this equation for the specified maps on ordinary unbounded small-etale module derived categories. In particular ordinary SheafOfModules.pushforwardComp supplies neither derived proper/open interchange nor the product-graph normalization. All recorded searches were actually run; no failed service was recorded as absence.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. The item is not replaced by a new node restating one of its clauses. Geometry is written as direct applications of existing statements, and the two grid calculations stay in the proof.

## Review by Q44

I read delivery-errors B-E in full, the item and every cited statement, Stacks more-etale.tex at lemma-shriek-proper-and-open (0F7B), lemma-shriek-proper-and-open-compose (0F7C), lemma-shriek-proper-and-open-compose-horizontal (0F7D), and the diagram comparisons in lemma-shriek-composition (0F7J). The latter uses more restrictive compactifications; the submitted argument uses its diagram-pasting method, not its existence assertions with dropped hypotheses. Finite A is a torsion ring, so the unbounded typing in the exchange-cube statement is the applicable one. I also read morphisms.tex at lemma-base-change-proper (01W4), lemma-composition-proper (01W3), and lemma-image-proper-scheme-closed (01W6), and the actual B1/B2/middle-intersection word in the local graph-model node and LowerShriekComposition.lean. No SGA source is used.

Step 1 uses the stated base-change and composition theorems for proper morphisms, open-immersion base change, and proper-to-separated. I checked the base for the latter is U_nu: a_nu is proper over that base and q_nu is proper, hence separated. Properness of a is obtained by an actual Cartesian square, not by incorrectly treating the open v_nu as proper. Products and opens use their definition statements. This verifies both that t is a presentation and that the two displayed lambda formulas have all their claimed isomorphisms.

Step 2 applies those same geometry statements to exactly three supplied factors P1,P2,C. The projection q_i^T is an iterated proper base change, so proper-to-separated applies to its lift of a_i, including a_0=1_X. Each smaller open contains the graph by its defining coordinate equations; its graph lift is the base change of the proper s_i. This checks the source and target of every Gamma in the later grids.

Step 3 takes horizontal pasting and identity normalization from the exchange-cube statement, and associative open composition from extension-zero-composition. The written two-factor substitution and cancellation prove the intersection equation directly. There is no extra support-comparison theorem invoked inline.

Step 4 uses the exchange-cube's Cartesian normalization and the resolution-normalized kappa statement to define A_i^T, and the open compositor to define E_i. I checked the directions: kappa splits a composite direct image, Gamma moves J_e R_q to R_pi J_n, and inverse shrinking maps into the common intersection. Thus E_i goes from F_i to H for every i.

Steps 5-6 check properness of z:T to P_nu times C and its restrictions by proper base change. Their first grid has proper columns (graph lift, restriction of z); their second has proper columns given by restrictions of z and open rows. The cited cube statement explicitly provides vertical and horizontal pasting for these squares, without requiring the interior squares Cartesian. The equations in step 6 are the two substitutions in those laws, with kappa and open compositors inserted; I checked both sides have the same source and target. The second projection equation uses the same normalized composite a_i on both paths. It does not appeal merely to equality of endpoints.

Step 7 is algebraic rearrangement of step 6 followed by step 3: the additional factor D_nu is independent of whether the index is 0 or nu. Step 8 uses the full statement of the graph-model node, not a construction hidden in its proof: that statement specifies B1, B2, B12 and the actual formula for B. It also uses exactly the definition of C in the graph-comparison/base-change statement. I verified B1=A_0, B2=A_nu and B12=sigma_nu sigma_0^{-1}, so the inverses in B and C have the required order.

Step 9 is the same already written grid substitution for the explicit projection T to P1 times P2. Its intersection is exactly U pulled back to N12. Here the downstairs inverse shrinking is Gamma_E_nu^{-1}, not Gamma_E_nu. The downstairs initial projection map is precisely kappa followed by Gamma_D_nu, so the complete downstairs map is the displayed lambda_nu. The two equations use a single tau_U, checked to be the same for nu=1,2. Step 10 then uses only horizontal shrinking and invertible-map cancellation to obtain the requested equality. This last cancellation proves equality of the specified natural transformations, not just their action on cohomology or stalks.

I tested the construction with X empty (the open-lift pullback remains the empty scheme), identical presentations, and all opens identities. In the identity-open case the normalized identity comparisons remove the shrinking factors; with identical presentations the two E/lambda factors coincide and the comparison is identity. For non-quasi-compact opens the proof uses only supplied finite products, arbitrary-open base change and the unbounded cube, whose statement explicitly has no quasi-compactness assumption. No argument uses density, a compactification existence theorem, a finite-type base, or a Noetherian hypothesis. All ten steps are below 2000 characters; the grid steps are specific applications of the cited equations with all vertices written, rather than hidden auxiliary comparison lemmas. No statement correction or new-node proof obligation was necessary.
