## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-open-scalar-conjugate-normalization.json`: statement node, split into seven steps; no Mathlib match for the whole item.
- `citations.json`: a verbatim statement quotation for each of the twenty step/node citations.
- `searches.jsonl`: five actual search records made by msearch.py; the node retains its inherited Q20 searches and adds these records. `prepare.py` is sandbox preparation material, not a delivered node.

There are zero new nodes and zero new Mathlib leaves. The existing normalized K-flat scalar-comparison lemma provides the non-elementary input. The rest is explicit action and adjunction calculation, retained as proof steps rather than new nodes.

Attachments: none. I searched the project source by the item tag and by scalar/conjugate terminology. `AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionShriekIso`, `derivedComapUpperStarIso`, and `comapUpperStarIso` in `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean` define the specified maps, but do not state the item's normalization identity. I read their constructions at lines 177–196 and 280–301. The finite-coefficient ScalarExtension file also has a different comparison; it is not an attachment for arbitrary commutative condensed rings.

WANTED: none.

The imported item's statement is unchanged. Its proof was empty; it required an actual calculation identifying the restriction of the published conjugate, rather than an existence argument producing some scalar-extension isomorphism. The unit/chapter route is unchanged: this realizes the alternative common-right-adjoint argument in paragraph (2) of `det-prop-scalar-six-pullback.proof.md`, using paragraph (1)'s normalization through the existing K-flat lemma. This item is not the unit's key node, so I did not edit the unit realization.

Nothing remains unfinished in this one-level split. The cited K-flat lemma remains an existing unsplit dependency, as the stage-1 contract permits.

## Sources and searches

I read the main-20261015 chapter and unit records, the parent proof, and the blueprint statements and proofs of `def-sfb-comap-upper-star-iso`, `def-sfb-derived-comap-upper-star-iso`, and `def-sfb-derived-open-immersion-shriek-iso`. I read Stacks `categories.tex`, Tag 0B65, `lemma-transformation-between-functors-and-adjoints`, including its explanation by natural Hom bijections, and the immediately following Tag 0DV0, `lemma-compose-counits`, for composite adjunctions. This completion is an agent proof, not a claim that the source already writes the normalization formula.

The logged searches were: LeanFinder with the item's open scalar-normalization formulation, Loogle with `CategoryTheory.mateEquiv, CategoryTheory.conjugateEquiv`, grep of the Mates unit and composition declarations, LeanSearch with a derived-open restriction formulation, and a second LeanFinder phrasing about fully faithful open left adjoints and Beck–Chevalley mates. All services answered. The first semantic hits concern ordinary structure sheaves and the wrong restriction/pushforward adjunction. The second phrasing finds the useful abstract `unit_conjugateEquiv`, `unit_mateEquiv` and their inverse forms. I read `Mathlib/CategoryTheory/Adjunction/Mates.lean` at lines 123–155, 275–319 and the composition/iterated-mate portions. These are formal tools, not the whole scheme/condensed-ring normalization or its coefficient-action identification. The proof writes out their few-line Hom calculation using existing definition nodes. No new Mathlib node is needed.

I searched the entire DAG statements and whole blueprint for conjugation, restriction of scalars, scalar comparison, unit conjugation, and the item; I also ran blueprint_refs.py ancestor, which reports `det-prop-scalar-six-pullback`. The existing `lem-sf-open-comparison-unit-normalization` has a similar formula but compares etale and pro-etale ordinary finite-coefficient sheaves; it is not this derived coefficient-change statement. `new-comap-upper-star-iso-mate` concerns the ordinary pullback/pushforward mate, not open extension by zero. Neither is substituted for the present item. `blueprint.same_as` stays empty after these searches.

## Not duplicates

No new nodes are created. All required notions and the non-elementary normalization input already have nodes.

## Review by Q70

I checked B–E against the written split, the source constructions and every cited node statement. The crucial orientations are $c:r_U R_B\to R_A r_X$, $\theta:T_U R_A\to R_B T_X$, and $\beta:T_X J_A\to J_B T_U$. Keeping these directions fixes which comparison is inverted. In particular I did not assume that taking square mates preserves arbitrary isomorphisms or inverses.

Step 1 uses the coefficient-change node for the actual scalar adjunction, the derived restriction-square node for the levelwise comparison, and the derived open-conjugate node plus the conjugate definition for exactly the specified beta. The composite-adjunction node explicitly states both its unit formula and that the Hom bijection is the successive individual bijections. These are precisely the data used in steps 1 and 4; the proof does not import an unstated coherence theorem.

Step 2 uses the module pullback formula, the alpha-isomorphism lemma for each of the two rings, the explicit action/coequalizer formulas in change of scalars, the commutative pullback coefficient square in coefficient change, and the transport action formula. I checked that the coefficient map a itself need not be invertible or flat: only alpha_A and alpha_B are inverted. I wrote the collapse maps and both inverse identities directly from balancing, so this step does not invoke the abstract equivalence result with unverified categorical hypotheses. The action equality uses the same coefficient square as the published construction. The generic alpha-isomorphism lemma is declared as a tool use; this leaves the unit's route intact.

Step 3 unfolds the named underived restriction comparison and the invertible coefficient-square comparison that defines it. The action calculation of step 2 shows that the two collapse maps cancel to the identity on the common inverse-image module. This is a calculation of the defined map, not a claim that any isomorphism between those functors has this normalization. The derived restriction comparison explicitly is levelwise, so the degreewise identity commutes with the differential and remains the same identity after localization. The K-flat lemma's statement names exactly the mate of that action identification. No representative of the arbitrary derived object is chosen here.

Step 4 uses only the stated conjugate Hom correspondence and the explicit composite-unit formula. I checked equation (1)'s types: both sides go from M to $R_A r_X J_B T_U M$. In particular the two open units are the supplied actual units; I did not cite the underived lower-shriek definition as a proof that a derived unit is invertible.

Step 5 is the non-elementary input: the K-flat normalization lemma explicitly identifies theta with the scalar-adjunction mate on all unbounded objects and asserts invertibility without flatness. Its hypotheses are matched after the coefficient identifications of steps 2–3: the rings on the open are the actual inverse-image rings under alpha. The mate-definition node supplies the inverse unit/counit formula. Expanding it and transposing gives equation (2), whose domain is $R_A V$ and whose codomain is $r_U R_B T_X V$. This cites the lemma's statement, not a construction hidden inside its proof.

Step 6 uses the scalar adjunction stated in coefficient change. I checked all four lines: naturality of eta_U at the open unit; equation (2); naturality of c inverse at beta; then equation (1) and cancellation. Both resulting transposes lie in $\operatorname{Hom}(M,r_U R_B J_B T_U M)$. Injectivity of that Hom bijection proves equation (3). Step 7 uses only functoriality and the invertible maps already specified, and cancels on the correct sides to obtain exactly the item's displayed formula. All transformations are natural, which gives the natural identity without a further descent or detection lemma.

I tested the small cases before finalizing: j the identity, the empty open, M the zero object, and the identity coefficient change reduce the calculation to the corresponding unit and inverse identities. The unit calculation also permits rescaling a chosen open adjunction unit: its occurrence in equation (1) changes with its adjunction, and the final formula uses that same unit. For a non-flat map such as constant condensed Z to Z/2 and an unbounded M, the formal calculation still applies because only the cited K-flat normalization provides invertibility; no termwise ordinary tensor is substituted for derived tensor. The zero coefficient ring causes no exception. No new statement was introduced, no target or statement correction was needed, and no SGA source is used.

Every citation is represented in citations.json by text copied from that node's statement, with all hypotheses visible. Proof dependencies are exactly the union of step uses. There is no clause moved to a new node, no proof step over 2000 characters, and no new node requiring a duplicate or Mathlib-leaf review. The initial server review_split check passed with zero new nodes and the alpha tool use declared. The required full dry run and direct push follow this review.
