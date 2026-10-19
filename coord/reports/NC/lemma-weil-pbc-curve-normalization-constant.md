## Files written

- dag/nodes/sec-proper-base-change/lemma-weil-pbc-curve-normalization-constant.json: statement item, split using existing nodes; no Mathlib match.
- citations.json: full verbatim statements backing every step citation.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite in WeilConjectures/AlgebraicGeometry/Curve/Reductions.lean:277 has a sorry body at line 286 in the supplied slopmaster2 source. Its tagged docstring and nearby normalization theorem were read; it is not a completed proof. No upstream master sorry is treated as evidence of completion.

## WANTED

None: the proof sources used are present in literature/stacks-project/etale-cohomology.tex and varieties.tex.

## Corrections and discrepancies

The imported proof was three sentences about a conditional module-valued Lean interface. It did not cite Noetherianity for constructibility and left scalar annihilation implicit. The replacement makes the prime-field reduction precise as the implication from the corresponding smooth calculation, and supplies all its transfer hypotheses.

The stored Lean record includes Finite(Λ/(ℓ)) and incorrectly says sorry_free, while the source checkout theorem still has sorry and omits that finite-quotient hypothesis. This discrepancy is reported, and maintainer-owned Lean fields are preserved. The blueprint is specifically about F_ℓ, so its quotient is finite and no arbitrary-Λ generalization is needed. Scalar annihilation is immediate in the ring R=ULift(Z/ℓZ), rather than requiring unnamed additivity theorems.

No statement dispute: 'extension-invariance' is interpreted with the explicit C6/C7 conditions in the unit. In characteristic ℓ on a nonproper affine curve, unconditional invariance is not claimed. The full eight-assertion conjunction keeps those conditions.

## Not duplicates

No new nodes. Whole-DAG keyword searches and blueprint_refs.py searches for normalization, finite normalization and smooth constant found the existing smooth modification, smooth localization, normalization exact sequence and finite-pushforward tools. None were recreated. The existing k1-reduced-constant-lower-shriek-assertions-of-reduction-data depends on this item and was deliberately not cited.

## Review by NC

I read the master blueprint node, the fixed sec-proper-base-change chapter and sk-thm-p1 unit, and Stacks etale-cohomology.tex: 0A3Q (lemma-somewhat-easier), 03SG (lemma-even-easier), 0A5D (lemma-finite-pushforward-statements) and 0GJA (lemma-restrict-to-open). I also read varieties.tex 0BXR (lemma-normalization-locally-algebraic) and 0B8Y (lemma-regular-point-on-curve). No new nodes need additional source checks. The blueprint route is retained as a reduction from the smooth calculation to finite pushforward and finite-support correction.

Step 1 uses the statement of lem-weil-pbc-reduced-curve-normalization, which explicitly provides smoothness, the dimension bound, finite type, separatedness, finiteness and a dense isomorphism locus. The actual normalization is its permitted witness. Reducedness and algebraic closedness are supplied by the item’s curve conventions.

Step 2 introduces the smooth calculation as the input of this reduction, which is exactly what the item states (and what the Lean H expresses). No smooth-case theorem is cited as an established input. R=ULift(Z/ℓZ) has ℓ=0 and R/(ℓ)=R, so this uses the same prime-field coefficient sheaf and maps. This conditional reduction does not itself reprove the smooth calculations; they are separate nodes. Both characteristic branches satisfy the transfer hypotheses.

Step 3 uses b3-finite-pushforward-module-assertions: its statement explicitly transfers the eight conditional assertions from the composite structure morphism to the finite direct image. Step 4 uses the full statement of lemma-weil-pbc-normalization-exact-sequence, which gives exactly the mono, constructible finite-support cokernel, and field-extension/open compatibility used here. I did not substitute the weaker existential Lean statement for these clauses.

Step 5 uses lem-weil-pbc-finite-type-over-noetherian to meet the Noetherian-X hypothesis of lem-weil-pbc-finite-pushforward-open-quotient-constant. Spec k is Noetherian because a field has just two ideals. The latter node then supplies constructibility of G for the finite quotient R/(ℓ)=R. Since ℓ is zero in R, its action on every section of G vanishes; no unrecorded preservation-of-annihilation lemma is invoked. Step 6 checks every hypothesis of b3-finite-support-mono-assertions: X a curve, prime ℓ, finite quotient, mono α, constructible G and Q, zero scalar action and zero restriction of Q on dense V. Its conclusion is all eight assertions, including low-degree comparisons and C8. The separately cited finite-morphism permanence statement gives exactly properness and affineness of Y when needed.

I tested the argument on U empty, X empty, a zero-dimensional reduced X, an already smooth X (ν identity, Q zero), and a nodal curve (the cokernel at its branch point is retained). No positive-dimensional or connectedness assumption slips into the proof. Properness is used only in the proper conditional branch; characteristic-primary affine extension-invariance is not inferred. All citations were opened and their entire statements copied verbatim into citations.json. Step 2 is elementary setup of the smooth input and coefficient notation; the remaining steps are marked non-elementary because they apply substantive cited results. No new lemma relabels a clause, and no dependency points to a child that uses this item. Mathlib searches used only msearch.py; both semantic phrasings gave unrelated ring-theory results, Loogle and grep gave relative normalization only, and LeanSearch was recorded unavailable.

The only off-unit generic tool is finite-type Noetherianity, declared in split_report.tool_uses. All cited normalization and transfer nodes are in sk-thm-p1. No files in the read-only project or source checkout were edited, no git commands were run there by the worker, and no Lean/compiler/Lake/build command was run.

## Unfinished work

None for this one-level split. Existing dependencies remain the responsibility of their own items. This sandbox is for a fresh second reader; no push is authorized for this worker.

## Dry-run correction

The first dry run rejected a cycle through the smooth calculation nodes and their general-curve c1–c8 dependencies, returning via algebraically closed extension and k1 to this item. I removed these circular proof citations and made explicit that the item is the normalization reduction (as its statement says), conditional on the corresponding smooth calculation, rather than the entire reduced-curve calculation. This is not an added hypothesis to an absolute theorem: the imported statement says “reduces ... to the corresponding calculation”, and the existing Lean interface likewise has H. The first blueprint paragraph explains where the input is intended to come from; it remains a pointer, not a proof dependency of this transfer. The exact-sequence, finite pushforward and finite-support arguments are unchanged. No other node was modified.

## Second reading by NC

- Item statement: checked the master blueprint node's reduction wording and both proof paragraphs against Stacks etale-cohomology.tex, lemma-somewhat-easier (0A3Q), lemma-even-easier (03SG), lemma-finite-pushforward-statements (0A5D), and lemma-restrict-to-open (0GJA); PASS as a normalization transfer conditional on the smooth calculation. The absolute conclusion of 0A3Q additionally uses 03SG; this item explicitly states only the reduction. The supplied slopmaster2 Reductions.lean:267–286 docstring and hypothesis H confirm that interpretation, but its sorry is no proof. The exact upstream master has no matching declaration in WeilConjectures, checked by identifier and declaration-name search.
- Step 1: opened lem-weil-pbc-reduced-curve-normalization and compared its whole statement with varieties.tex, lemma-normalization-locally-algebraic (0BXR) and lemma-regular-point-on-curve (0B8Y); PASS. The cited node explicitly permits the actual normalization, supplies finite type/separatedness/dimension/smoothness and the dense isomorphism locus; the integral normalization definition is used componentwise with reduced structures, not on a reducible function field.
- Step 2: checked the coefficient calculation and the exact C1–C8 definition nodes against the eight assertions preceding 0A3Q; PASS elementary. The ideal generated by ℓ in R is zero, hence R/(ℓ) is canonically R, and the smooth input is a hypothesis rather than a circular proof dependency. This does not establish the smooth calculation itself.
- Step 3: opened b3-finite-pushforward-module-assertions and compared its conditional conclusion with 0A5D; PASS. Applied with its target Y renamed X, source X renamed Y, g the structure morphism and f=ν; both schemes meet its curve hypotheses, and F′ is ℓ-torsion over the finite coefficient ring.
- Step 4: opened lemma-weil-pbc-normalization-exact-sequence and its master blueprint text; PASS. Its statement supplies the actual mono and constructible finite-support cokernel together with boundary-map/open/field-extension compatibility. No compatibility is inferred from an existential mono alone.
- Step 5: opened lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-finite-pushforward-open-quotient-constant, and both constructibility definitions; FIX then PASS. Compared Noetherianity with morphisms.tex, lemma-finite-type-noetherian (01T6). Spec k has one point and Noetherian coordinate ring; ν is finite and R/(ℓ) has ℓ elements. Added the omitted passage from underlying constructibility to R-module constructibility: additive local trivializations of ℓ-torsion groups are automatically F_ℓ-linear. This applies to both G and Q, and ℓ acts as zero on G sectionwise.
- Step 6: opened b3-finite-support-mono-assertions and lem-weil-pbc-finite-morphism-permanence and checked all their hypotheses against steps 1–5; PASS. The former states the full eight-assertion implication, including canonical comparisons in degrees zero and one and C8. The latter supplies exactly the proper and affine permanence needed in the respective branches. No invariance in characteristic ℓ for arbitrary nonproper curves is asserted.
- New nodes: none; B1–B7 and new-node deletion/duplication checks have no instances. No clause of the item was moved into a child.

Small cases checked independently: empty X or U gives the zero sheaf; a reduced zero-dimensional finite-type scheme over k is a finite disjoint union of k-points with identity normalization; smooth X has Q=0; a nodal curve retains the branch-point cokernel. Taking ℓ=char(k) leaves only the appropriate conditional clauses: A¹ with F_p is not assigned unconditional extension-invariance. ℓ=0 and ℓ=1 are excluded by the stated primality hypothesis, rather than accidentally used.

Changes: added the explicit prime-field linearity argument in step 5 and its definition citation; updated citations.json with that definition's full verbatim statement. Retained all first-reader sections and the existing proof route. Repeated Mathlib searches with new phrasings via msearch.py: LeanFinder returned scheme/ring étale lemmas, Loogle returned general sheaf cohomology functors and nonabelian H¹ cochain relations, and grep returned unrelated normalization/pushforward occurrences; none states this transfer. Their raw records are appended by msearch.py to searches.jsonl. No new nodes or Mathlib leaves were warranted. No Lean file, compiler or build tool was used, and no direct git command was run in the read-only repository; packaging is solely through the explicitly requested delivery tool.
