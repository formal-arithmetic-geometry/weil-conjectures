## Worker report

Item: lem-trf-devissage-pointed-restriction. Group: Q53. Stage 1 only.

Files written:
- dag/nodes/sec-trace-formula/lem-trf-devissage-pointed-restriction.json: statement node, now split into 11 steps. Mathlib verdict: no match. The statement and statement dependencies are retained.
- citations.json: one verbatim statement quotation for every step/node citation (the complete cited statement is quoted so its hypotheses remain visible).
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. All substantive generic ingredients already have DAG nodes, so none was duplicated.

Attachments: none. Searched lean/WeilConjectures by the exact blueprint tag and by devissage, dévissage and pointed restriction terminology. The homological and coherent-property devissages found there do not state the pointed finite-over-smooth scheme data or its shrinking theorem. No exact project declaration was found.

WANTED: none.

The item was initially unsplit, with no proof and with searches inherited from its creator. No earlier item/report existed in this sandbox. Retained those searches and appended five actual msearch.py queries, with their returned results read. Loogle's devissage search and the Mathlib AlgebraicGeometry grep are empty; LeanSearch finds individual smoothness/finite/finite-presentation permanence results, and both LeanFinder phrasings find affine-limit or morphism-property results. None supplies the item or a one-line specialization of it. No search is claimed unavailable.

The source is Stacks flat.tex: 05H7 (lemma-base-change-one-step), 05H8 (lemma-base-change-one-step-at-x), 05H9 (definition-shrink), 05HA (lemma-shrink), 05HJ (lemma-base-change-complete), 05HK (lemma-base-change-complete-at-x), 05HL (definition-shrink-complete), and 05HM (lemma-shrink-complete). I read these proofs, not just the cited tags. They apply to the auxiliary definition after deleting their unnecessary comparisons with support dimensions: the constructions preserve the smooth relative dimensions directly. I also read coherent.tex 02KG (lemma-affine-base-change), more-morphisms.tex 05B8 (lemma-finite-morphism-single-point-in-fibre), schemes.tex 01I9 (lemma-widetilde-pullback), modules.tex 01BG (lemma-pullback-quasi-coherent), and morphisms.tex lemma-base-change-finite-presentation and 056G (lemma-smooth-open) where these arguments call them.

No mathematical statement correction was needed. The source's complete-shrinking definition has obvious indexing/wording typos (calling the restricted complete data a one-step devissage); the item's auxiliary definition already expresses the intended chain and is not changed. The proof fills details the source abbreviates: force the lifted initial principal open to lie over the smaller base, preserve geometric irreducibility by nonemptiness after field extension, identify the actual restricted cokernel, and give both directions of chain induction. Nothing was moved wholesale into a new lemma.

The latest blueprint files read are literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md and its .proof.md. They now use contracting correspondences, whereas the inherited ancestry explicitly records historical supporting algebra in the semistable-alteration branch. This assignment does not change that chapter or unit route or claim that commutative-algebra devissage proves the new local-term theorem; it splits exactly the inherited supporting lemma on its parent's stated Stacks route. The existing blueprint.from place and via chain are retained. Whole-blueprint searches for devissage, finite morphism, smooth open, principal open, and singleton fibre found no equivalent blueprint theorem. No unit record was edited.

Nothing remains unfinished in this one-level split. Its dependencies remain independently owned DAG items where not already completed.

## Not duplicates

No new nodes were created. Whole-DAG searches by the source tags, lemma labels, titles and concepts located the existing singleton-fibre localization, affine pushforward base change, coefficient pullback/cokernel, principal-open, morphism permanence and openness nodes used here.

## Review by Q53

I checked the statement against the pointed auxiliary definition and Stacks' one-step and complete-devissage sections, including the fact that the datum requires finite presentation only for the closed immersion, finite type only for the coefficient module, and an isomorphism of the marked base residue fields for pointed base change. I did not apply the stronger Stacks support-dimension assumptions to these weaker data. There are no new-node sources to review.

Step 1 uses the statements of the affine fibre-product, locally-finite-type base-change, closed-immersion base-change, finite-presentation permanence, finite-morphism permanence and smooth-relative-dimension permanence nodes. I opened each: they explicitly give exactly the geometry taken from them, for arbitrary base change. The geometrically-irreducible definition quantifies over every field extension, so the displayed fibre tensor formula proves the remaining condition without a hidden spreading theorem.

Step 2 uses the pullback quasi-coherence statement, the natural affine-section pullback formula, the finite-type affine criterion, and affine pushforward base change. The latter explicitly supplies the pushforward comparison for arbitrary base change with quasi-coherent coefficients. Our i and pi are affine, and the coefficients satisfy its hypothesis. Finite generation after tensoring is proved by writing the generators; flatness is not asserted or needed.

Step 3 uses the affine fibre-product formula and the actual pointed-data definition. The residue-field isomorphism identifies entire marked fibres, rather than just selecting an arbitrary point above a point. Thus singleton fibres and purely transcendental marked extensions persist. This step is elementary after the geometric and sheaf checks in steps 1--2.

Step 4 uses affine pushforward base change, tensor right exactness, the quasi-coherent cokernel statement and the pullback-stalk formula. I verified that the cokernel node says it is the module quotient on each affine open, and that the stalk node gives the tensor formula naturally in the coefficient map. These yield the actual alpha maps and their actual cokernels, not just abstract isomorphic modules. Tensoring the isomorphism on the generic residue-field vector space with its inverse preserves it; no left exactness or flatness assumption is slipped in.

Step 5 invokes only the pointed-data definition and principal-open localization, after the preceding base-change result. It writes inverse images and iterated localizations as principal opens of the original affines. In particular prescribed base restrictions are retained through all subsequent shrinkings.

Step 6 uses smooth restriction, smooth implies flat and lfp, and flat-lfp openness. I checked that these give openness for W to B without Noetherian or finite-type-base hypotheses. The principal-open basis supplies the new base inside that image. The field-extension-surjectivity and surjective-base-change nodes say exactly what is needed to keep each fibre open nonempty after every field extension. The irreducibility argument then takes two opens and intersects them. Open immersions are etale and smooth-relative-dimension composition preserves d. Finally the affine closed-immersion criterion explicitly gives a surjective map on global rings; I lift the defining target function and multiply by the base function. This last factor corrects an omission that would otherwise fail to put X_1 over B_1. The two restricted maps are actual base changes, so their finiteness and finite presentation are those established in step 1.

Step 7 applies the neighbourhood clause of the singleton-fibre localization node, not its stalk clause. Its hypotheses are precisely pi finite and the marked fibre a singleton, both part of our datum. It chooses principal opens using the basis node and verifies that intersecting X_1 with the chosen U_0 leaves Z_1 unchanged. Arbitrary source restrictions of a finite morphism would not suffice; the proof always keeps Z_1 as an inverse image.

Step 8 uses the explicit quotient statement, tensor right exactness and the open-immersion residue-field statement. The pushforward restriction equality is checked directly on sections. The generic point remains in every nonempty open of the irreducible fibre. Hence alpha's residue-field map really is the original map, and its cokernel is the restricted old cokernel. This is a short consequence of steps 2 and 4, not a new restriction lemma requiring a new node.

Steps 9 and 10 use the definition of a chain and the one-step constructions already proved. For the backward induction I checked that each chosen target is exactly the initial open previously selected for the next datum and that all later changes are base restrictions. For the forward induction the tail is first base-restricted, shrunk inside the selected head target, then the head is base-restricted to that tail base before imposing that exact principal target. Thus the shared scheme and the shared cokernel agree on both sides. Both inductions terminate and preserve the last zero cokernel. They are bookkeeping applications of earlier steps, with no independent hidden comparison claim.

Step 11 uses the zero-length clause of the definition, the principal-open basis and open-immersion residue-field invariance. I checked zero coefficients, rank zero, a zero-length chain, a one-stage chain, dimension zero, an identity base map, and a nonflat residue-field-preserving base map. The proof uses right exactness only, so the last case does not cause an unintended flatness requirement. The last-target request is never made at length zero.

I checked the B--E delivery cases against the actual node files: no invented statement-only nodes or clause restatements, no missing citations for the non-elementary geometric and coefficient facts, no citation to a definition for a theorem it does not state, no added hypotheses, no circular dependency on this item's parent, and no SGA route. Every proof step is below 2000 characters. All off-unit statements are declared in split_report.tool_uses as generic tools; the unit has no replacements for these affine/module facts. All citations.json quotations are copied verbatim from the corresponding live statements.

The first dry run detected that the independently landed pointed-data definition had changed while I worked. I reread its live statement: the changes make the pointed map, module action, cokernel sheafification, generic point, rank-zero convention and principal opens explicit; they leave the conditions used here unchanged. I refreshed the verbatim citations against that live definition.
