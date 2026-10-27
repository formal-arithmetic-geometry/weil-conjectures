# Stage-1 delivery: lem-cbc-proper-open-clopen-projector

1. Files written: `dag/nodes/sec-smooth-purity/lem-cbc-proper-open-clopen-projector.json` — statement, split into eight proof steps using existing nodes; Mathlib has no exact full assertion. `citations.json` gives a literal statement quotation for each of the 30 step/node pairs. No new DAG nodes and no new Mathlib leaves.
2. Attachments: none. The exact blueprint tag is absent from `lean/WeilConjectures/`. The structure-sheaf rank-stratum projectors concern a different site and coefficient sheaf. The side-library squareLift_clopen theorem in StrictTowerProperOpenArrows.lean:1076 proves only the geometry; pi_components in StrictTowerProperOpenCalculus.lean:154 proves component equations, while alpha_cartesian in that file still has sorry. These do not attach the full item.
3. WANTED: none.
4. The missing properness hypothesis and the cartesian identification are corrected below. The new proof supplies the argument that the inherited statement lacked, rather than copying its clauses into new nodes.
5. Unfinished: no stage-1 proof obligation left in this item; its existing cited nodes retain their own stage status. No Lean was written and no compiler, Lake or build was run.

## STATEMENT-DISPUTED

The imported child statement made p proper but left r arbitrary. Set T=W=S=Spec(k[t]), p=i=identity, V=D(t), and k=r the principal-open inclusion. Both horizontal maps are quasi-compact open immersions and p is proper. All the original hypotheses hold, but W_S=W and s is D(t) into Spec(k[t]), whose image is not closed: it contains the generic point and misses (t). Thus the original clopen conclusion is false.

I restored “r and p proper”, exactly the parent's hypotheses in lem-cbc-strict-tower-proper-open-calculus and Stacks 0F7B (lemma-shriek-proper-and-open). This is a repair to a non-target imported child, faithful to the source and caller, not a change of the locked target. The source itself is correct. The parent already has both proper maps, so its application needs no additional assumption.

Also, in an arbitrary cartesian square s is the canonical pullback isomorphism, not literally the identity on a separately chosen fibre product. The statement now explicitly makes that canonical identification before writing s=1. All remaining clauses, including arbitrary B and unbounded strict towers, are retained.

## Sources and searches

Read Stacks morphisms.tex Tag 01W6 (lemma-image-proper-scheme-closed), especially part (2) and its factorization proof; more-etale.tex Tag 0F7B, which assumes BOTH proper vertical maps; schemes.tex Tag 01IQ (lemma-immersion-when-closed); sites.tex Tags 00VM/00VR, the sheaf equalizer and empty-cover observation; sites-modules.tex Tags 03DI/03DJ, including the explicit Hom construction; proetale.tex Tag 09AE; derived.tex Tag 015F (lemma-right-derived-exact-functor) and Tags 0FND/0DVC/09T5. The pro-etale arbitrary-ring and strict-tower refinement is agent-written, explicitly marked as such: the etale Stacks lemma is not quoted as proving the additional refinement.

Read the chapter and unit records and the current blueprint thm-cbc-complete-proetale.proof.md, final sentence about compatibility of comparisons with completed maps. The parent's original steps 5–6 require precisely this intrinsic clopen projector. The unit's route is retained; the item is not the unit key node, so no unit realization fields were edited.

Whole-DAG searches included clopen, open and closed, 01W6, 0F7B, proper-to-separated, and disjoint-cover/sheaf-condition terminology. blueprint_refs.py ancestor locates thm-cbc-complete-proetale; searches for clopen, proper open, and product sheaves found no blueprint node stating the full assertion. Existing etale finite-ring product and clopen-section lemmas do not state the pro-etale arbitrary-ring assertion; they were not misapplied. No new node was necessary. Generic open base change, proper base change, proper-to-separated, site localization, adjunction uniqueness, exact tower abelianness and derived localization are all reused.

The actual msearch command results are retained in searches.jsonl; inherited item searches were preserved and the new calls appended, with the query text exactly as run. Both natural-language phrasings, Loogle, LeanSearch and grep ran successfully. Read the candidate signatures and source at Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:442 and :447 (Zariski structure-sheaf adjunction), AlgebraicGeometry/Limits.lean:480 (structure ring of a coproduct), and Topology/Sheaves/CommRingCat.lean:301 (topological ring-valued sheaf gluing). None is the full pro-etale normalized tower statement or a one-line specialization of it. There are no new-node searches to supply.

## Review by Q61

I checked the proof against delivery-errors B–E with the cited statements open. No new node is hidden in the delivery, no clause is delegated to a new node, and no inference uses a cited node's proof in place of its statement. Every cited step/node pair is quoted in citations.json, copied literally from the corresponding statement.

Step 1 uses open-immersion base change for b and the open-immersion definition to describe its restricted structure sheaf, then the fibre-product universal property gives bs=k, qs=r. Restricting the two given open embeddings proves the openness of s directly; it is not inferred from set-theoretic image containment for a general immersion.

Step 2 uses proper-base-change to get q proper, the definition to get q separated, and the Mathlib-leaf proper-to-separated triangle theorem with base S, source V, target W_S and proper composite r. These are exactly its hypotheses. Properness gives closed image, and the open/closed structure-sheaf argument is written on the two disjoint opens to meet the closed-immersion definition. This is precisely where the original missing hypothesis mattered.

Step 3 uses the weakly-etale localization theorem for the site objects and coefficient restriction, the pro-etale covering definition, the sheaf equalizer definition and module-sheaf linearity. On every affine test open the intersections with the clopen pieces are closed, hence quasi-compact, so they have finite affine covers; the covering condition is checked, not assumed for an arbitrary open cover. Empty overlaps give zero modules and no compatibility equation. The section formula follows directly from the stated sheaf axiom, not from an etale-only product theorem.

Step 4 writes the functor I(N)(H)=N(H_U) and the gluing inverse to the restriction Hom map. The localized exact extension-by-zero adjunction identifies it with the specified s_!; the conjugate-isomorphism statement supplies precisely the unit-preserving uniqueness used here. Localized-site identification supplies restriction to U. Inserting zero on H_C makes the map linear for the specified ring action. This explicit construction proves the projector and its uniqueness; no separate clopen-product lemma is smuggled in.

Step 5 uses the actual direct-image section formula from def-weil-pbc-proetale-operations. Both the unit and the transpose are computed, so invertibility of t and the normalization equation follow as actual natural transformations. The proper/open-arrow definition is used only to compare with the already specified formula pi=t inverse times eta; its asserted clopen theorem is not used to prove the geometry or section construction.

Step 6 uses tower-adjunction-realization for exact restriction/extension and their specified units, levelwise-abelian for exactness on towers, and exact-derived-factorization plus exact-derived-functor for the unbounded descent and comparison with R_s. Naturality handles arbitrary transition maps and differentials. No uniform lower bound, torsion, finite B or transition-surjectivity assumption is introduced.

Step 7 verifies the unit normalization using the cochain-derived-adjunction statement: both functors are exact for this clopen immersion, so all complexes form the resolving class and every derived comparison is invertible. The theorem states the exact unit equation needed, rather than only existence of some adjunction. The localization universal property's natural-transformation clauses carry the equations to the full derived category. Thus the equalities are not inferred from evaluation faithfulness. The zero complementary target is represented by the zero complex itself.

Step 8 uses the proper/open-arrow definition, the normalized open and inverse-image compositors, the beta theorem and the pullback universal property. A cartesian lift is the canonical isomorphism, whose normalized identification removes its identity projector; the remaining inverse beta has precisely the stated open-unit transpose. For r=identity the equality qs=identity identifies the chosen component as the stated section. Both cases retain the same construction and units.

All eight steps are below 1000 characters; none reaches the 2000-character long-step threshold or conceals an independent comparison lemma. The multi-sentence section calculations are direct applications of sheaf gluing and adjunction Hom bijections. Generic statements filed outside the unit are declared individually in split_report.tool_uses; they support the unit's existing route rather than replace it.

Small cases checked: empty V gives the zero projector; empty complement gives the identity; B the zero ring gives zero module categories; disconnected test objects use both product factors; arbitrary infinite B uses the same linear restriction and zero insertion; unbounded complexes and arbitrary tower transitions use the natural formulas termwise. The only failed edge case was the nonproper r counterexample, repaired as above.

## Not duplicates

No new nodes. In particular I did not recreate the existing proper-to-separated Mathlib leaf, the finite etale clopen-product lemma, the semilinear-system clopen projector, or the generic derived-localization tools. The proof writes the ordinary sheaf argument needed for this item and reuses the available generic interfaces.

## Validation

The server review_split check passed with eight proof steps and zero new nodes. Full deliver.py preflight and dry run are the final checks before push.
