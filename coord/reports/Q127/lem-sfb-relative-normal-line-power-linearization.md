# Stage-1 delivery by Q127

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-normal-line-power-linearization.json`: item, statement preserved, status split; Mathlib searches found no match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-laurent-line-invariance.json`: one new statement-only geometric lemma, status unsplit, no Mathlib match. It has neither a proof nor proof dependencies.
- `citations.json`: seven verbatim statement excerpts, one per citation of each proof step.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint tag, linearization/linearisation/Sumihiro and the Laurent-Picard notions. The representation-theoretic and module-object linearizations found there do not state this geometric result.

## WANTED

WANTED: local copy of R. W. Thomason, Equivariant resolution, linearization, and Hilbert's fourteenth problem over arbitrary base schemes, Adv. Math. 65 (1987), pp.16–34, specifically proof of Theorem 3.3, p.32, for the item. Its primary full text was read online at https://www.researchgate.net/publication/243015730_Equivariant_resolution_linearization_and_Hilbert%27s_fourteenth_problem_over_arbitrary_base_schemes . No download or literature edit was made. The proof is marked agent-written, not document-written.

## Audit and changes

The item had an empty proof and a reference to the first paragraph of Thomason's embedding proof. That paragraph uses positive-power linearization as an external input. For the split torus in this item, the proof below that input can instead use invariance of invertible sheaves under Laurent variables. The item's statement, including normality only on X and all its exceptional cases, is unchanged. The proof actually takes m=1; this is a witness to the given conclusion and does not alter it.

Read the three levels in SETUP.md, GOAL.md, the stage-1 brief, stage document, worker role, and both copies of delivery-errors sections B–E. Read the recorded chapter and unit and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof. This is a supporting node below the relative torus embedding on the existing alteration route, not a replacement of a unit step. The item is not the unit key node. `blueprint_refs.py ancestor` returns null for the inherited chain; retained that null and the complete via list, adding the item at the front for the new node. Blueprint searches for linearization, Picard, Laurent, Laurent Picard, Picard invariance, polynomial Picard, Picard affine, normal scheme and monomial unit found no equivalent blueprint statement.

The new geometric lemma does not mention an action, linearization, a cocycle, a relatively very ample line or an affine base. Its content is an isomorphism for every invertible sheaf on a split torus over any normal locally Noetherian scheme. This is a geometric input to the item, not the item's conclusion moved into another node.

## Source and future proof of the new node

Read `literature/stacks-project/divisors.tex`, Tag 0BD7, label `lemma-in-image-pullback`, hypotheses (1)–(5), conclusion and proof, and Tag 0BDA, label `lemma-open-subscheme-UFD`, both clauses and proof. These are the sources actually asserted by the new node; neither tag is falsely advertised as the verbatim Laurent invariance theorem. Also read the existing generic-line-pullback node and the affine-space Picard nodes.

For the eventual split of the new node: a locally Noetherian normal scheme is the disjoint union of its open normal integral components, so work on each component. The Laurent projection is locally of finite type and flat (its coordinate algebra is free over the coefficient ring), its source is locally Noetherian, and every fibre is the nonempty integral split torus over the residue field. The generic fibre is the principal open D(z_1...z_r) of affine r-space over a field; Tag 0BDA makes the restriction of any invertible sheaf trivial. Tag 0BD7 then gives N = q* M on each component. Pulling back along e identifies M with e*N; substituting yields q*e*N = N. Choose the componentwise isomorphisms and take their disjoint union. The empty scheme has unique sheaf maps. This argument is in this report only; the new node is deliberately statement-only. This future split must cite the normal-component and Laurent flatness inputs explicitly, rather than treat those facts as definitions.

## Not duplicates

lem-sfb-normal-laurent-line-invariance vs lem-sfb-normal-noetherian-generic-line-pullback: the existing 0BD7 node assumes an integral base, locally Noetherian source, flatness, integral nonempty fibres and generic-fibre triviality for a given line. The new node allows disconnected normal bases and asserts Laurent invariance for every line without any fibre-triviality hypothesis; verifying the Laurent geometry, triviality over the generic field and component assembly are necessary to deduce it. It does not merely rename the existing statement.

lem-sfb-normal-laurent-line-invariance vs lem-sfb-normal-base-fibrewise-line-locality: this existing input gives only base-local pullback under a smooth connected-fibre morphism and assumes fibrewise triviality; the new node gives a global isomorphism from the specified identity pullback for every line on a split torus.

lem-sfb-normal-laurent-line-invariance vs lem-sfb-local-generic-unit-factorization: this is a theorem about units of a generic fibre of a flat local ring map, not about invertible sheaves on a Laurent product.

lem-sfb-normal-laurent-line-invariance vs def-sfb-integral-cartier-divisor: this defines divisors and specifies a divisor/line dictionary; it does not state invariance of lines on Laurent space.

lem-sfb-normal-laurent-line-invariance vs lem-sfb-affine-space-open-invertible-trivial: this 0BDA node has a field as coefficient ring and says the line is trivial; the new node allows normal schemes over general rings and says the line is pulled back, not necessarily trivial.

lem-sfb-normal-laurent-line-invariance vs lem-sfb-affine-space-invertible-trivial: this 0BDA node covers the whole affine space over a field, not the Laurent product over a normal scheme.

lem-sfb-normal-laurent-line-invariance vs lem-sfb-smooth-affine-space-picard-invariance: the existing theorem is for an affine smooth geometrically integral finite-type scheme over a field and affine-space variables. The new theorem permits normal singular schemes in mixed characteristic, disconnected bases, and invertible Laurent variables. Neither specializes to the other in one line under the present hypotheses.

lem-sfb-normal-laurent-line-invariance vs lem-sfb-affine-group-picard-field-invariance: that theorem changes the field of definition of a geometrically integral algebraic group; no Laurent-product invariance over a general normal base is stated.

lem-sfb-normal-laurent-line-invariance vs lem-sfb-frame-product-laurent-algebra: that theorem describes functions and affineness of a product of frame schemes, not its invertible sheaves.

## Mathlib searches

All new searches were run through the required msearch.py, with their exact query texts and returned summaries preserved in searches.jsonl. The new node records two semantic phrasings, LeanSearch, Loogle, and source grep. The item retains the inherited Q144 records and adds the Q127 searches. None of the returned normalization diagrams, affine pullback constructions, ordinary Picard-group definitions, Rep.linearization declarations, or tensor-power identities asserts either statement. The exploratory units queries are also retained in the search log; they returned only monomial invertibility and support facts, not a counterexample or a more useful geometric theorem. The finite-support calculation is written out instead of creating an elementary new node. No unavailable service is recorded as a negative result.

## Review by Q127

I checked the item against the primary Thomason paragraph described above, but wrote the split-torus argument myself from the available Stacks inputs. I read both source tags for the new node, not merely their names. I checked every step against each cited node's statement, including the following specific uses and hypotheses.

Step 1 uses the affine-cover definition in pqf-def-locnoeth to recognize Spec A as locally Noetherian: the one affine chart has the given Noetherian coordinate ring. pqf-lem-locnoeth-lft states exactly that a locally finite-type map to a locally Noetherian scheme has locally Noetherian source. Finite type in the item includes locally finite type. I checked Tag 01T6, `lemma-finite-type-noetherian`, in morphisms.tex as its source. The Laurent tensor-algebra identification is explicit, so no normality of the base or unstated smoothness theorem is used here.

Step 2 uses def-sc-invertible-module for local rank-one frames and def-pc-module-pullback for tensor inverse image, its unit and composition comparisons. The pulled-back frames exhibit invertibility of a*L. The new node states exactly q*e*N is isomorphic to N for every invertible N on that Laurent product. X satisfies its locally Noetherian and normal hypotheses by step 1 and the item. Substituting N=a*L and the action unit ae=id gives the required unnormalized isomorphism. This citation uses the new node's statement, not its future proof or another lemma's proof.

Step 3 uses the same invertibility and tensor-pullback definitions. I wrote out why an automorphism of a line is a global scalar unit and why changing a local frame leaves the scalar unchanged. Thus normalization is genuinely defined globally. Pullback along the identity of theta_0 composed with q*alpha^{-1} is alpha alpha^{-1}=1, with the order of composition matching the direction q*L to a*L.

Step 4 is elementary assembly: action associativity identifies the target lines of the two composites, and their ratio is a scalar by the frame argument already proved in step 3. Both face restrictions equal one as scheme-theoretic sheaf-map equalities. This checks the cocycle condition on the full fibre product, including nilpotent test schemes; it is not an assertion about abstract rational-point actions.

Step 5 proves, rather than cites, the Laurent-unit assertion that is used. Over the domain O_X,x, finite nonzero Laurent supports have unique least and greatest product exponents in the lexicographically ordered lattice: cancellation cannot kill those extreme terms, since their coefficient products are nonzero. The widths add and cannot cancel because both are nonnegative. The inverse therefore forces singleton support. The two face identities separately kill the g and h exponents and the coefficient. Finally equality after every local-ring base change kills every Laurent coefficient germ on each affine open; the sheaf axiom kills the coefficients themselves. No invariant affine chart for the action is required: the affine opens only cover X under the projection T^2 times X to X, and need not be preserved by a. The step is 1415 characters and contains its finite-support proof; there is no long concealed lemma or new unit node.

Small cases: X empty (including A the zero ring) has unique line maps, so m=1 works. Rank r=0 gives the trivial exponent group and identity action. Disconnected normal X is handled locally in the cocycle argument, without demanding one globally constant Laurent exponent. The new node permits disconnected X explicitly; its future proof assembles independent isomorphisms over open normal integral components. Over nonreduced A, normal X may be supported on the reduction; only its own local domains enter the unit calculation. No reducedness, normality, field, properness or regularity of A was inserted. Singular normal X is allowed. The general line over X need not itself be trivial. Positive power m=1 satisfies the original conclusion, and no hypothesis or statement was changed.

I checked B–E point by point: complete self-contained statement and notion dependencies; no proof hidden in an unsplit node; correct tags and labels; TeX escaped once; all searches actually logged and read; no exact project attachment; blueprint searches and duplicate comparisons; no cited definition substituted for a nontrivial theorem; all citation excerpts verbatim; no dependency cycle through the item (new node's statement dependencies are definitions only); no new clause of the item; and no SGA source. All steps are below 2000 characters. The report's future-proof paragraph is intentionally not proof_deps of the new node. The item has no unresolved statement dispute.

## Unfinished work

None within this one-level split. The new node is left unsplit as required and awaits its own item. Delivery checks and push results are recorded by deliver.py.
