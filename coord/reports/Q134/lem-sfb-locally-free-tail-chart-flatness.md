# Worker report: lem-sfb-locally-free-tail-chart-flatness

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-locally-free-tail-chart-flatness.json: existing statement, now split; no exact combined Mathlib match. Six explicit proof steps, with no step longer than 545 characters.
- citations.json: ten verbatim statement quotations, one for every step/node citation.
- searches.jsonl: five actual searches run through the required msearch.py command; the node retains all imported searches and appends these five results without changing their tool or query text.
- report.md: this report.

## New nodes

None. The two module-flatness facts and the affine finite-projective sections theorem already have nodes. Introducing the tail-colimit assertion as a new node would simply restate the central clause of this item, so its elementary fraction argument remains in the item's steps.

## Attachments

No attachment for the item. Searching lean/WeilConjectures by the blueprint id and by homogeneous localization, colimits, flatness and locally free sections did not find one declaration proving all its clauses. The existing declaration AlgebraicGeometry.Scheme.Modules.finitePresentation_projective_sections belongs to the already attached lem-pc-finite-flat-affine-sections-projective, in lean/WeilConjectures/AlgebraicGeometry/Modules/LocallyFreeAffine.lean:71 (the live file's theorem keyword). I read the entire proof, which contains no sorry. It supplies only the first clause of the present item. The existing filteredColimit_flat declaration likewise supplies a generic algebraic ingredient, not the tail-colimit identification.

## WANTED

None. All sources used are available locally.

## Corrections and limitations

The item's statement is correct as written, including nilpotent f, arbitrary A_0 and arbitrary schemes. No statement correction, dependency-definition replacement, or statement dispute was necessary. The inherited node had no proof; its source explicitly requests an agent argument for the universal property. That argument is now written out rather than assigned to a new theorem with the same content. No Lean files, compiler commands, repository writes or direct git commands were used.

The blueprint ancestor command returns null for this imported created-item chain. I preserved its inherited from.node, exact from.place and via chain rather than inventing a blueprint identity. The current latest blueprint's det-thm-sf-ctf-stability-direct-images proof (3) concerns the larger direct-image route; this item is an algebraic prerequisite already placed beneath that route. Whole-blueprint searches for homogeneous localization (eight hits), colimit flat (zero), and projective flat (zero) found no node stating the present combined theorem. The eight localization hits are definitions or different chart identifications, not the tail universal property.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. Reused lem-pc-finite-flat-affine-sections-projective, lem-weil-pbc-projective-module-flat and lem-weil-pbc-filtered-colimit-flat-modules instead of duplicating them. DAG searches included the literal tag 05UT and the projective/flat, homogeneous-localization and tail-chart concepts. The parent's broader Proj-flatness statement uses this item and cannot be cited in its proof.

## Review by Q134

I read the item, its parent lem-sfb-flat-graded-tail-proj, the chapter/unit records and the current latest blueprint direct-images proof. I read Stacks algebra.tex, Tag 00JM, label section-proj, lines 13399--13408, where equal-degree fractions are defined without regularity of the homogeneous element; Tag 05UT, label lemma-colimit-flat, lines 8659--8669, whose hypotheses are exactly a directed system of flat modules; and the first proof sentence at Tag 051G, label lemma-local-artinian-characterize-flat, stating the general projective-implies-flat fact. The local/Artinian hypotheses of that lemma are not being imported: the separately cited DAG node states the unrestricted projective-module theorem, which is also Mathlib Module.Flat.of_projective. I also read the full statements of all seven distinct proof dependencies, in particular the ordinary localization definition with its explicit cross-multiplication annihilator relation. No new node needs a source review.

Step 1 uses the exact affine sections statement: it quantifies over any scheme, any finite locally free module, and any affine open. Applying it separately to each degree therefore gives finite presentation and projectivity without demanding a common frame. The projective-module-flat statement then gives flatness, with no finite-generation or Noetherian hypothesis. These are two actual theorem citations, not an appeal to the definition of flatness. The live LocallyFreeAffine.lean proof was read to confirm its match with the existing node.

Step 2 uses the graded-sheaf-structures statement's bilinear, associative multiplication and linear unit, so the transition maps really are R-linear even when R -> A_0 is not an isomorphism. Its exponent identities prove functoriality. The degree-zero homogeneous localization definition explicitly gives every representative a/f^e with a in A_e because f has degree one. The ordinary localization definition supplies the fraction operations. Multiplying numerator and denominator to degree D proves the displayed cocone and its coverage, rather than assuming cofinality or invoking a localization-flatness theorem over the wrong base ring. The indexing set is a small subset of natural numbers, nonempty at m, and directed by maximum.

Step 3 takes precisely the equality criterion stated in def-weil-ring-localization-away. From equality of fractions it obtains f^k(f^t a-f^e b)=0. Choosing L at least e+t+k and all chosen levels makes both numerators lie in A_L; multiplying by f^(L-e-t-k) proves their equality there. Compatibility of the given h_d then proves representative independence. Enlarging D uses compatibility alone. This is an explicit quotient calculation, not an uncited cancellation theorem and not an assertion that f is a non-zero-divisor. The step is elementary because its entire argument is the written multiplication identity from the cited definition.

Step 4 puts both fractions over the same degree D, so addition is addition inside A_D; scalar multiplication is the structural R-action in degree zero. The formula for h and linearity of h_D give both linear laws. Taking D=d proves h mu_d=h_d, and the representative description forces uniqueness. The category-colimit node states exactly that existence and uniqueness of a compatible morphism; it is not merely a definition of chosen colimit notation. Thus all clauses of the requested explicit universal property are proved within the item.

Step 5 applies the existing filtered-colimit-flat-modules statement only after checking every hypothesis: R is commutative, I is small and nonempty directed, the maps are a module diagram, all stages are flat from step 1, and C with these very mu_d is a colimit by steps 3--4. This avoids the incorrect shortcut that flatness of localization over A would imply flatness over R. This generic theorem and the affine sections theorem are recorded as tool uses in split_report, with reasons; neither changes the Hilbert-scheme route of the unit.

Step 6 checks degeneracies explicitly. If f^N=0, each a in A_d is sent to zero at d+N, so compatibility forces h_d(a)=0; the localization is zero by the quoted fraction relation. This verifies rather than excludes nilpotent elements, f=0, and zero coefficient rings. I also tested m=0 and arbitrarily large m in the degree bounds, and A=R[x] with f=x, where all transition maps identify the usual copies of R and C=R. As a zero-divisor check, take R=Z/4, A=R[x], f=2x: f^2=0 and both the tail colimit and homogeneous localization are zero. For a nonidentity degree-zero algebra, A=S[x] for finite projective R-algebra S and f=x gives C=S, as the formula predicts. No common neighbourhood or A_0=R occurs in the proof.

For Mathlib, I read the actual hits after running all searches. HomogeneousLocalization.lean:281--318 constructs the quotient and embeds it in ordinary localization; lines 601--626 define Away and give its homogeneous representative theorem, including nilpotent denominators. These establish the fraction model already represented by the definition node, not the universal property in the present item. Module.Flat.of_projective at Flat/Basic.lean:227 is already represented by the existing Mathlib leaf. The second semantic phrasing again returned fraction constructors and surjectivity, with no tail-colimit theorem. All five services returned successfully; none is falsely recorded as unavailable or absent after an error.

I checked B--E against the written files: there are no new or hollow definition nodes, no unsplit nodes carrying proofs, no unsupported definition-as-theorem citation, no restatement node, no use of a cited proof's private construction, no source-route substitution, and no missing hypothesis from a local flatness or finite-presentation theorem. All ten quotes were checked as literal substrings of their cited statements. The longest proof step is 545 characters, so there is no long step hiding another lemma. The report and item preserve the existing statement, source, maintainer fields and prior search records. What changed during review was to make the common-level equality and the nilpotent-family vanishing explicit; these are the places where cancellation or a restriction to positive/non-nilpotent denominators could otherwise have slipped in.
