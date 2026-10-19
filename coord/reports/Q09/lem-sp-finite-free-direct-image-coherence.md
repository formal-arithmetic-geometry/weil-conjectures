# Worker report

Item: lem-sp-finite-free-direct-image-coherence. Group: Q09. Date: 2026-10-17.

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-finite-free-direct-image-coherence.json: statement node, split into nine proof steps; no Mathlib match.
- citations.json: verbatim statement quotations for every step/dependency pair.
- searches.jsonl: actual additional searches, preserved as logged.
- report.md: this report.

## New nodes

None. The split reuses the existing general scalar-restriction/adjunct theorem, balanced scalar associator, localization, shift, and mate-pasting nodes. New Mathlib leaves: zero.

## Attachments

None. Searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the blueprint tag, finite-free direct-image spellings, projectionFormula/projection_formula, and coefficient-extension terminology. No declaration gives the full arbitrary-ring-sheaf unbounded statement with the input-shift and tower equations. The existing étale coextension and projection-formula interfaces do not state it. Nothing was compiled. The upstream master was used only as reference material, not evidence of completion.

## Literature and searches

Read literature/stacks-project/sites-cohomology.tex, Tag 0B56 (equation-projection-formula-map), Tag 0944 (lemma-projection-formula), Tag 0D6D (lemma-derived-pullback-composition), Tag 07A6 (lemma-adjoint), and Tag 0D6E (lemma-derived-pushforward-composition); also categories.tex, Tags 0037 (definition-adjoint and subsequent unit/counit formulas) and 0038 (lemma-adjoint-exact). The finite-free case is exactly the final reduction in 0944, proved here by coordinates instead of citing its whole perfect-complex statement. The shift and coefficient-tower equations are agent-written calculations from these constructions, not falsely attributed to clauses of 0944. proof_origin.by is agent.

Read the chapter record, the current sk-thm-sf-compatibility unit record (especially coefficient clause (7)), and the main-20261015 thm-cbc-qbar statement and proof. The opening scalar-extension/direct-image factor is the inherited blueprint ancestor; the current unit collects its coherence. This item is not the unit's key statement, so no unit realization is changed. No geometric route changes.

Searched the whole DAG by tags 0B56, 0944 and 0D6D, and by projection formula, scalar restriction, mate pasting, coefficient associativity, exact derived functors and derived tensor/pullback coherence. Ran blueprint_refs.py ancestor and searches for projection formula, finite free direct image, scalar extension counit, derived pullback composition, coefficient pullback, balancing and successive scalar. Opened the candidate statements. The finite-free projection-formula node is tied to its pre-existing coefficient-arrow package, and the perfect-projection node imposes an adic datum; neither states this arbitrary-ring-sheaf coefficient comparison. The proper finite-constant transpose node has geometric and coefficient restrictions. These nodes were not applied outside their hypotheses. Instead lem-weil-pbc-ring-sheaf-change-adjunction gives exactly the general adjunct normalization needed here.

Actual Mathlib searches were run only through msearch.py. LeanFinder's two phrasings returned free sheaf pullback and ordinary pullback-composition maps; LeanSearch returned free sheaves and generic exact-functor shifts; Loogle returned generic adjunction/shift compatibility. The grep searches returned no coefficient-changing derived direct-image comparison. Read the returned source for SheafOfModules.freeFunctorCompPullbackIso and pullbackObjFreeIso_hom_naturality (Sheaf/PullbackFree.lean:132,142), pushforwardPushforwardAdj_counit_app_val_app (Sheaf/PushforwardContinuous.lean:303), the termwise cochain shift (HomotopyCategory/Shift.lean:255), and Shift/Adjunction.lean. They do not specialize in one line to the item. Existing searches in the imported item are retained, with the new logged searches appended verbatim.

WANTED: none.

## Corrections and unfinished work

The imported statement is retained verbatim, with all original statement dependencies and metadata preserved. It is true for globally finite-free ring-sheaf extensions as stated. The imported item had no proof; the delivery supplies one. No statement dispute, weakened hypothesis, boundedness assumption or properness assumption is introduced. The proof explicitly distinguishes conservativity of scalar restriction from faithfulness on derived Hom sets: only conservativity is used, and all coherence equalities are proved in the enlarged module categories.

No stage-1 proof step remains unfinished. New supporting statements left for later workers: none. The current unit has no realization yet; that concerns its key item, not this subsidiary node. The server review_split check passed before packaging and reported zero new nodes.

## Review by Q09

I checked the statement against 0B56 and the finite-free case of 0944: q is arbitrary, M is unbounded, rings are sheaves of commutative rings, and both coefficient identifications are isomorphisms whose squares commute. The global basis assumed by the statement suffices; neither local trivialization nor geometric finiteness is silently used. Every supporting node cited by a step was opened and its statement, rather than its proof, checked. citations.json copies the actual clauses (sometimes the full statement where several clauses are needed).

Step 1 uses the exact identified-coefficient inverse image in def-weil-pbc-proetale-operations, the sheaf tensor definition, and the abelian module-sheaf kernel/cokernel description. I wrote both inverse basis maps, so finite-free exactness is not an uncited flatness theorem. lem-weil-pbc-exact-functor-derived-functor says every complex computes the derived functor of an exact functor; lem-pur-derived-change-of-rings identifies that functor with the specified target-ring-linear C_T. Thus the basis reduction works for unbounded complexes and at both sites.

Step 2 proves the coefficient/pullback comparison on exact complex functors using the actual balancing formula. The two ring-square identifications are exactly the hypothesis making it linear. Exact-functor factorization supplies the degreewise shift structures; the localization node supplies unique lifts of natural transformations and equality of the lifted equations. To identify the lift with the named canonical derived comparison I use the flat K-flat resolution supplied by lem-pc-kflat-resolution and the computation clauses of derived-change-of-rings and derived-tensor-pullback. These clauses really include preservation of flat K-flat representatives. The comparison is not justified by equality after scalar forgetting.

Step 3 uses lem-sfb-successive-derived-quotient-normalization. Despite its name, its statement allows arbitrary ring-sheaf maps and gives exactly the balanced associator and its complex-level formula, not just quotient rings. The remaining assertion is an elementary equality: both routes multiply the same two ring coefficients after inverse image. The ring map compatibility equates the displayed products, and the cited localization uniqueness passes that equality to D(B_Z). Identity coefficients give multiplication. This is an explicit coordinate calculation, not a hidden direct-image lemma or a new node restating the item.

Step 4 uses the mate definition's displayed transpose formula, which exactly matches the item's definition of pi. Its statement supplies naturality. The exact scalar and direct-image functor statements give exactness of the two composites. Their target is D(S_W), so existence and naturality of pi already hold with its S-action.

Step 5 applies lem-weil-pbc-ring-sheaf-change-adjunction under all its hypotheses: small pro-étale sites, arbitrary compatible ring-sheaf maps, and the two inverse-image isomorphisms. Its statement explicitly gives the comparisons b,d, conservativity, and the adjunct equation used here; it does not require flatness or boundedness. The basis calculation of the transpose fixes the canonical map, rather than replacing it with an abstractly existing isomorphism.

Step 6 uses the adjunction bijection's naturality from lem-weil-pbc-adjunction-of-natural-bijection and preservation of finite products from lem-weil-pbc-right-adjoint-preserves-limits. The finite biproduct coordinate relations are written out, and additivity of derived direct image is part of the operations interface. The inverse is the product comparison with components R_R(p_i). Conservativity of the restriction node then proves invertibility in D(S_W). This step never uses faithfulness on derived morphisms.

Step 7 uses the exact unit/counit-compatible shift conclusion of lem-weil-pbc-derived-adjunction-shift, the termwise exact scalar shift from exact-functor factorization, and the composition/whiskering closure stated in lem-weil-pbc-commshift-nattrans-comp-whisker. Expanding pi as unit, balanced comparison, and counit makes every factor covered. The formula is in the input M, not merely a shift in a second tensor argument. It gives the connecting square as well.

Step 8 uses precisely clause (4), identity squares, of lem-weil-pbc-mate-pasting after the multiplication normalization proved in Step 3. Step 9 uses clause (1), pasting along the horizontal coefficient functors, not composition of geometric q's. The square types were checked: L_B C_{B/S,W} C_{S/R,W} goes to C_{B/R,Z} L_R after a_Z, with L_B(a_W) on the source. Adjunction naturality puts a_W inverse first and R_B(a_Z) last, exactly as in the statement. The final equality is proved in D(B_W) and is independent of the conservativity argument.

Small cases checked: d=0 (the zero coefficient ring and zero functor); d=1 including nonidentity rank-one algebra presentations; q the identity, where the counit and comparison reduce to the tensor identity; M=0 and shifts of single-degree M; nonflat ring towers in the associator node versus the finite-free hypotheses actually used by the item; and a tower in which one extension is the identity. A basis of S and a basis of B over S give the product basis of B over R, including zero ranks. No noetherian, completeness, constructibility, properness or base-field hypothesis entered. There are no new statements requiring additional edge-case checks or duplicate comparisons.

Checked delivery-errors B–E: no statement-only child contains a proof, no duplicate or clause-copy node is created, every non-elementary ingredient is a cited node with a matching quotation, and no source theorem is used outside its hypotheses. Every proof step is under 2000 characters. The only elementary-labelled step is the explicit balancing equality of Step 3; its non-elementary associator and localization inputs are cited. Generic tools are declared in split_report.tool_uses without modifying maintainer-owned tool_uses. I corrected the initial tower-arrow display to run from the actual source to the actual target and added the explicit K-flat existence citation during this self-review. No Lean, compiler, Lake, or live-project writes were used.
