# Q25 stage-1 report: lem-sfb-semiabelian-multiplication-fppf

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-multiplication-fppf.json: item split, exact original statement retained, eight steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-flat-homomorphism-extensions.json: new statement-only geometric lemma, unsplit; no Mathlib match after five recorded searches with two semantic phrasings.
- citations.json: verbatim statement quotations for every citation of every proof step.

## Attachments

None. Searched the project WeilConjectures source for the blueprint tag, semiabelian spellings, multiplication and isogenies. Its abelian-variety declarations cover only abelian fibres, not arbitrary semiabelian families or their relation schemes. No declaration states the entire item.

## WANTED

WANTED: Moret-Bailly, Pinceaux de varietes abeliennes, Asterisque 129 (1985), II 3.3.2.1 and II 3.3.3, for lem-sfb-semiabelian-multiplication-fppf. The original cited PDF is absent locally. I did not download it; the proof is explicitly marked agent-written from the local Stacks inputs instead.

## Issues in the inherited material

The item was a statement-only prerequisite, not a completed split. Its broad Mathlib search verdicts were inherited; retained them and added the actual current searches, with their literal query texts and saved results. The original statement is true, including in characteristic dividing d. No statement dispute or added hypothesis is needed. Normality and integrality are not used by this argument, but remain in the statement.

The blueprint ancestry is already broken in live: tools/blueprint_refs.py ancestor returns None. The imported prerequisite chain records a precise place and via list, which I retained, with the new helper prefixed by this item. The current latest blueprint sk-thm-sf-ctf-stability-direct-images proof (3) has the direct-image preservation route; our inherited Picard/alteration prerequisites refine its open/direct-image input. No chapter or unit route was changed, and this item is not the unit key statement.

## Unfinished work

No requested stage-1 work is left. The new node deliberately has only a statement, no proof or proof dependencies, as required. It is queued for its own future split.

## Intended argument for the new helper

For any test scheme U with y in E2(U), form W=U x_(Q2) Q1 using q2(y) and w. The map W to U is finite locally free and surjective by base change of w. The W-section a of Q1 lifts fppf locally to g_i in E1(W_i), by exactness of the first row. In the scheme of solutions to v(x)=y, the subfunctor over W_i consists of x with q1(x)=a. It has x=g_i+j1(t) uniquely. Put delta_i=y-v(g_i), which is in K2 by compatibility. The remaining equation is u(t)=delta_i. Thus the solution scheme over W_i is the pullback of u along delta_i; it is finite locally free and surjective. Descent of finite local freeness (Stacks descent.tex Tag 02VO, lemma-descending-property-finite-locally-free) proves E1 to E2 x_(Q2) Q1 finite locally free, and surjectivity follows by lifting points on a jointly surjective covering. Compose with the base change of w. All identifications hold on every test scheme, including nilpotents; no assertion about a kernel based only on geometric points is used. This is a general diagram-of-extensions lemma, not a restatement of multiplication on a semiabelian fibre or of the relative item.

## Review by Q25

I read delivery-errors B through E in full and checked each node and step against them. I read the local groupoids.tex lemma-degree-multiplication-by-d (0BFG) and proposition-review-abelian-varieties (03RP), more-morphisms.tex theorem-criterion-flatness-fibre (039C), morphisms.tex lemma-finite-presentation-permanence (02FV), lemma-finite-type-noetherian (01T6), and descent.tex lemma-descending-property-finite-locally-free (02VO). For the new node the last is the descent ingredient; the actual group-extension deduction is written above and identified as my argument, not attributed to an unstated Stacks theorem. I checked the tag-label map. The inaccessible Moret-Bailly reference is WANTED above; I have not claimed to read it.

Step 1 uses the monic quotient node for its full basis assertion, the finite-free-flat node for flatness, and the affine flatness criterion to turn this into scheme flatness. The displayed polynomial algebra provides finite presentation directly and finiteness directly; the finite locally free definition then applies. The algebraic-closure definition supplies the nonzero roots proving surjectivity. The Laurent-variable inverse formula checks that this really is the torus fibre functor. Rank zero and d=1 give the identity; in characteristic p with d=p the same monic basis still works, so etaleness is not being smuggled in.

Step 2 uses precisely the proper/smooth/connected definition of abelian variety; the cited finite-flat multiplication node states finite local freeness for all positive integers, and the isogeny node states surjectivity for all positive integers. Multiplication commutes with the two extension arrows by its definition as a repeated sum, so all hypotheses of the new helper are present. The finite locally free definition provides flatness and local finite presentation. The finite-map fibre node supplies finite fibres. In contrast, the existing semiabelian-invertible-multiplication requires an invertible integer; it was read but is not used or duplicated here.

Step 3 uses the map-over-base lemma only for local finite presentation, which is exactly what its statement gives. Global quasi-compactness and quasi-separatedness are checked over each affine V in S using the qcqs permanence node and separated-implies-quasi-separated node, not claimed from a local finite-presentation statement. The target-local quasi-compactness lemma applies to the covering G_V and also to the diagonal to obtain quasi-separatedness. No quasi-compactness of S is assumed.

Step 4 uses the field-extension fpqc node and base-change flatness/surjectivity to obtain a point above each original point. The pointwise base-change node really states descent of flatness under a flat base map, with no finite-type condition on that map. The fibrewise flatness node requires source locally finitely presented and flat over S and target locally of finite type; smoothness and the given finite presentation supply all three. I read both statements and did not cite a smoothness definition as a flatness theorem.

Step 5 uses pointwise quasi-finiteness under arbitrary base change, whose statement is an equivalence at a point lying above an original point. Both base changes have such points; the residue-field fibre point is unique over a fixed x and the algebraic closure projection is surjective. Finite implies quasi-finite is cited explicitly. Local quasi-finiteness plus quasi-compactness is the exact cited equivalence. Finite fibres follow as images of finite geometric fibres, avoiding a degree or rank constancy assumption. The toric rank can jump, so finite multiplication over S is deliberately not concluded.

Step 6 is a short elementary application of the actual covering definitions. The fpqc finite affine refinement follows from quasi-compactness of the inverse image, not from the fppf definition alone. Step 7 sets up induction with R1=G and the common-value map; each new projection really is a base change of m. Its flatness and finite presentation come from the stated base-change nodes, flat composition and local finite-presentation composition. The qcqs claims are checked on inverse images of affine base opens. The finite-type-over-Noetherian node is applied only after restricting to a Noetherian affine base open; its hypothesis is not asserted globally. Step 8 is the fibre-product universal property, evaluated on all U-test schemes, which proves the restriction identification and its projection compatibility.

All cited statements were opened; citations.json copies them verbatim, including complete formulas. Every non-elementary ingredient is a cited node; the only elementary steps are the covering-definition argument and the fibre-product restriction argument. No proof step exceeds 2000 characters. The helper is self-contained, statement-only, with notions defined inline or by nodes; it allows nonreduced group schemes and arbitrary base, with no false smoothness shortcut. In small cases K trivial reduces to the quotient map, Q trivial to the kernel map; identity vertical maps and empty base give identities. The root-algebra case handles nonreduced mu_p. Searches of the full DAG, blueprint_refs, latest blueprint text and project Lean found no generic extensions lemma or complete attachment. Mathlib hits are about abstract finite groups, modules, or flat ring maps, not a finite locally free morphism of group schemes. No search was invented, and all newly recorded searches are in searches.jsonl.

## Not duplicates

lem-sfb-finite-flat-homomorphism-extensions vs lem-sfb-semiabelian-invertible-multiplication: the new lemma concerns arbitrary compatible arrows in two exact sequences, with no integer and no abelian or torus structure; the existing lemma is specifically invertible multiplication and asserts etaleness.

lem-sfb-finite-flat-homomorphism-extensions vs lem-sfb-zero-dimensional-stabilizer-finite-orbit: the existing node concerns Zero dimensional scheme theoretic stabilizers give finite orbit torsors; the new statement is a compatible homomorphism of arbitrary fppf-exact commutative group extensions, with finite locally free surjections on the two ends, and deduces that property for the middle arrow. It does not state a descent theorem or the existing special geometric construction.

lem-sfb-finite-flat-homomorphism-extensions vs lem-sfb-finite-locally-free-fppf-descent: the existing node concerns Effective fppf descent for finite locally free covers of fixed degree; the new statement is a compatible homomorphism of arbitrary fppf-exact commutative group extensions, with finite locally free surjections on the two ends, and deduces that property for the middle arrow. It does not state a descent theorem or the existing special geometric construction.

lem-sfb-finite-flat-homomorphism-extensions vs lem-weil-pbc-finite-locally-free-degree-etale-descent: the existing node concerns Finite locally free of degree d descends along etale coverings (Stacks 02VO); the new statement is a compatible homomorphism of arbitrary fppf-exact commutative group extensions, with finite locally free surjections on the two ends, and deduces that property for the middle arrow. It does not state a descent theorem or the existing special geometric construction.

Final review correction: the target-local quasi-compactness source is spaces-morphisms.tex Tag 03KG, lemma-quasi-compact-local (6), specialized to schemes; corrected the proof source field. First complete server dry run passed at fc84df0f68b before this citation-only correction.
