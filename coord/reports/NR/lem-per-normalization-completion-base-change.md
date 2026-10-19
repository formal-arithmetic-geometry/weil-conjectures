# Split of lem-per-normalization-completion-base-change

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-normalization-completion-base-change.json: item, statement unchanged; eight proof steps following Stacks 0BG9, status split. The affine normalization identification is proved through minimal primes and generic residue fields.
- dag/nodes/sec-deligne-laumon-a1/lem-per-faithfully-flat-normal-ring-descent.json: new statement-only node, Stacks 033G, unsplit; no Mathlib match after both semantic searches, Loogle, and source grep.
- dag/nodes/sec-deligne-laumon-a1/lem-per-componentwise-normalization-properties.json: new statement-only node, Stacks 035Q/035K/0H7D and 035P, unsplit; no Mathlib match for componentwise absolute normalization with the stated normality, generic-fibre, restriction, and recognition properties.
- citations.json: one verbatim statement quotation for every step/node citation. cited-statements.txt retains the statements consulted. searches.jsonl retains the earlier attempt's actual search results; these were read and reused rather than rerun.

The earlier attempt had the item, two new nodes, citations, a preparation script, and searches, but no report. I retained its argument and searches, compared the item with the current repository (still unsplit), repaired explicit citation gaps, and completed this report. No unit or chapter record is changed. All writes are within this item's sandbox.

## Attachments

None. Searches for the exact blueprint tag and completion/normalization terminology in /home/ubuntu/weil-src-slopmaster2/WeilConjectures found no declaration giving this item. Curve normalization and relative normalization results have different hypotheses or conclusions; they are not an attachment. The two new supporting statements also have no exact project declaration found by their notions or source tags. The upstream master source is not used as evidence of finished proofs.

## Wanted literature

None: the item and supporting sources are present in literature/stacks-project/.

## Problems and corrections

The imported item had no proof. Its statement agrees with resolve.tex, lemma-normalization-completion (Tag 0BG9), including local finite type, arbitrary Noetherian local base, the specified base change, and possible nonreduced components. No statement dispute or source correction is needed.

The saved split's reference to faithful flatness alone concealed prime-surjectivity and minimal-prime existence; these now cite the existing Mathlib leaves. The affine tensor-product formula, fibre prime/residue-field correspondence, finite-algebra integrality, and finiteness local on the target also now have their own existing citations. Step 1 uses the affine cover supplied by the definition of local finite type, without imposing finite type on all of X. Step 2 explicitly checks that the reduction is Noetherian before using the reduced affine-chart node. Step 8 writes out the elementary sectionwise gluing argument. The final identification does not assume an open complement meeting every component: steps 5 and 6 check dominance and generic residue fields also for vertical components.

## Unfinished work

The two new supporting nodes are deliberately statement-only and remain for later stage-1 splits. There is no Lean writing or compilation in this delivery. The item's proof itself is complete relative to the cited DAG statements.

## Not duplicates

lem-per-faithfully-flat-normal-ring-descent vs lem-weil-pbc-normal-ring-field-extension-descent: the existing statement only descends along B to B tensor_F E for field extensions; this proof needs arbitrary faithfully flat B-algebra base changes D to D tensor_B C, with no field base.

lem-per-componentwise-normalization-properties vs lem-sbc-normal-finite-stage-universal: that node constructs a universal finite normal approximation of an integral scheme, not the generic fibres, open restrictions, or recognition of componentwise normalization for arbitrary locally Noetherian schemes.

lem-per-componentwise-normalization-properties vs lem-sbc-normalization-dominant-lift: that node gives a lift from an integral normal source to an integral target's normalization, not normality and generic fibres of a possibly reducible/nonreduced normalization or its integral birational recognition.

lem-per-componentwise-normalization-properties vs lem-sbc-stalk-normalization-normal-dense: that node concerns relative normalization of a finite etale cover over a smooth family and localization of the base; it does not state these absolute componentwise-normalization properties.

lem-per-componentwise-normalization-properties vs lem-trf-conductor-smooth-base-change: that node concerns a conductor ideal for reduced schemes of finite type over Q; it does not supply absolute normalization recognition over arbitrary Noetherian rings.

lem-per-componentwise-normalization-properties vs lem-trf-open-relative-normalization-gluing: that node extends an integral scheme over an open via relative normalization; it does not identify an integral normal birational scheme with absolute componentwise normalization, or state its generic fibres.

lem-per-componentwise-normalization-properties vs lem-trf-normalized-blowup-calculus: that node treats normalized blowups of reduced finite-type Q-schemes and smooth base change, not arbitrary locally Noetherian componentwise normalization or recognition of integral normal birational maps.

lem-per-componentwise-normalization-properties vs lem-per-integral-etale-chart-flatification: that node constructs a normal modification for a specified etale/flatification problem over a quasi-excellent integral base; it does not state this normalization package.

lem-per-componentwise-normalization-properties vs lem-per-excellent-normalized-blowup-tower: that node concerns excellent integral schemes and a tower of normalized blowups; its normal-open conclusion is a special restricted setting and it lacks the needed generic-fibre and recognition assertions without excellence.

lem-per-componentwise-normalization-properties vs lem-per-componentwise-normalization-affine-charts: the existing node gives explicit affine product-of-integral-closures charts for reduced locally Noetherian schemes and is reused in step 2; it does not state generic-fibre equality, open-normal triviality, or recognition of an arbitrary normal integral birational morphism.

lem-per-componentwise-normalization-properties vs lem-per-excellent-normalization-preparation: that node assumes a reduced excellent Noetherian scheme and asserts finiteness and existence of a dense normal open; the new statement does not assume excellence or reducedness and does not assert finiteness, and additionally gives generic fibres and birational recognition.

lem-per-componentwise-normalization-properties vs lem-per-normal-projective-compactification: that node constructs a normal projective compactification over a complete mixed-characteristic trait and makes no general assertion recognizing componentwise normalization.

lem-per-componentwise-normalization-properties vs lem-weil-pbc-reduced-normalization-over-normal-reduction: that node restricts normalization over a dense normal-reduction open of a finite-type scheme over a field; it gives neither arbitrary open restriction over arbitrary locally Noetherian bases nor generic fibres and birational recognition.

lem-per-componentwise-normalization-properties vs lem-weil-pbc-reduced-algebraic-normalization-field-change: that node assumes reduced finite type over a field and addresses field extension; it cannot apply to B or C over arbitrary Noetherian local rings, and has no general integral birational recognition clause.

## Review by NR

I read resolve.tex, lemma-normalization-completion (0BG9), statement and proof, and compared every hypothesis with the item. I also read morphisms.tex around the construction of normalization by generic residue fields, lemma-description-normalization (035P), lemma-normalization-localization (035K), lemma-normalization-normal (035Q), and lemma-normalization-trivial (0H7D). For the new normality-descent node I read algebra.tex, lemma-descent-normal (033G), including its localization and principal-ideal argument. These are supporting theorems independent of completion comparison, not clauses of the item renamed as new nodes. Their statements introduce their rings/schemes and cite the definitions of the notions they use; their proof fields remain empty.

For step 1 I read the statements of the affine fibre-product leaf, local-finite-type definition, adic-completion Noetherianity, local-ring/residue-field description of completion, module-completion completeness, complete-local Nagata theorem, local completion faithful flatness, faithful-flat base change, and finite-type Noetherianity. The first supplies exactly Spec of the tensor product; the completion nodes together make the completion complete Noetherian local with the stated residue field; Nagata then applies. Base change supplies B to C faithfully flat, and tensoring the residue-field isomorphism gives B/I to C/IC. Finite type on the chosen affine cover and its tensor-product algebra supplies the two Noetherian rings. The extension of powers of m is the same as powers of its extended ideal, so module completeness is the ring completeness needed by the Nagata node.

For step 2 I checked that the affine-chart node assumes reduced locally Noetherian X, so applied it to Spec(C_red), which is Noetherian as a quotient finite-type algebra. The componentwise definition is unchanged by killing nilpotents. Each C/q_j is a finite-type domain over the Nagata completion; the universally-Japanese node says precisely that such a domain is N-2. The Japanese-domain definition includes the degree-one extension, hence gives finite integral closure in its own fraction field. A finite product of finite modules is finite by the displayed union of factor generators; no extra node is introduced for this elementary argument. Clauses (1) and (2) of the new normalization-properties node then give normality and the structural isomorphism on the assumed normal complement. They do not give finiteness, which is established here.

For step 3 I read the formal-gluing datum definition and the complete statement of lem-per-formal-glueing-finite-algebras. It requires flatness, the quotient isomorphism, finite modules on all charts, algebra isomorphisms and the module cocycles. Steps 1 and 2 provide the first conditions; B localized at f_i is generated by 1 over itself, and the inverse of the structural normalization isomorphism supplies the prime transitions. The two- and three-denominator formulas in the step verify the cocycles and compatibility, so the cited theorem supplies a finite B-algebra D, with algebra rather than merely module comparison isomorphisms. The finite-morphism definition supplies the associated finite affine morphism. No descent theorem only about modules is silently upgraded to one about algebras.

For step 4 the base-change theorem applies to the B-algebra D. Its target is isomorphic to C^nu as a ring, so 033G gives normality of D with exactly the available faithful-flat hypothesis. The existing field-extension descent node is too narrow here. Finite module generators generate an algebra, so finite-type Noetherianity applies to D over B. The new descent node has no excellence or domain assumption.

For step 5 I checked the statements of faithfully-flat surjective spectrum, prime-contains-minimal-prime, the affine irreducible-component correspondence, and flat going down. They give a prime above each minimal prime of D, a minimal prime beneath it, the interpretation of generic points used in normalization-properties (1), and contraction of a minimal prime through B to C. Minimality forces the intermediate contraction back to the specified minimal prime of D. This proves every component of Z dominates a component of Spec B, including those in the special fibre; normality alone would not prove this.

For step 6 the same surjective-spectrum and minimal-prime statements give a minimal q of C above any minimal p of B. The new normalization-properties statement explicitly gives C^nu tensor_C kappa(q) = kappa(q), stronger than merely a bijection on generic points. Tensor associativity gives E tensor_K L = L as L-algebras. A basis proves scalar extension of a nonzero vector space is nonzero and preserves kernels/cokernels, so the unit K to E is an isomorphism. The existing fibre-ring-primes-residue-fields node states both the prime bijection and the compatible isomorphism of residue fields; it therefore supplies exactly the remaining passage from this fibre equality to the unique prime and its residue field in D. A minimal prime beneath that prime has the same contraction by step 5 and must equal it by uniqueness. This is not a normalization base-change theorem used circularly.

For step 7 I read finite-algebra-is-integral: it gives integrality of the finite algebra constructed in step 3, which the definition alone did not imply as a theorem. Clause (3) of the new normalization-properties node then applies because Z is normal locally Noetherian (step 4), and its generic points and residue fields have exactly the required bijections (steps 5 and 6). The recognition statement follows from 035Q(3), whose footnote permits birationality on reductions, and 0H7D applied to the normal source. Integral maps have affine preimages of affine opens, so the local finiteness of components required in 035Q(3) holds. This explains why nonreduced B is allowed.

For step 8 I checked the open-restriction and uniqueness clauses of the new normalization-properties node and all clauses of the existing finite-local-on-target leaf. The cover from step 1 proves finiteness globally. On overlaps both comparison maps identify normal integral birational schemes over the same open of Y, so the uniqueness clause makes them equal. The finite C-algebra C^nu is Noetherian, and therefore all these normalization charts are locally Noetherian as needed for recognition. The continuous maps and structure-sheaf maps glue explicitly, as do their inverses.

I tested the item when A is a field (m=0, empty normal-complement hypothesis), when X is empty, when X is wholly supported on the special fibre (C=B), and when X is nonreduced. The last generic-point argument remains valid for dual numbers: their normalization is the residue field, and tensoring at the unique generic point gives that field. For the new normalization-properties node I also checked a reducible crossing Spec(k[x,y]/(xy)), with two normalization summands and the stated generic fibres, and the empty scheme. The normal-ring descent node includes the zero-ring case: faithful flatness into the zero ring forces the base to be zero. No excellence hypothesis on A is used; complete-local Nagata is applied only to its completion.

I searched the whole DAG and blueprint by the source tags and normalization/descent terms before retaining the two nodes, opened all same-tag statements listed above, and found no general existing statement subsuming either new node. The Mathlib hits in the retained search log were read: relative normalization's universal factorization and isomorphism for already integral morphisms do not give normality or absolute componentwise recognition; integral-closure transitivity and localization criteria do not give arbitrary faithful-flat normal-ring descent in one line. The source files read include Mathlib/AlgebraicGeometry/Normalization.lean and Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean. Every recorded new-node query has an actual retained command log; unavailable results are not reported as absence. All proof-step citations have verbatim quotes in citations.json. No step exceeds 2000 characters. The explicitly declared generic off-unit tools supply commutative-algebra inputs below the fixed unit route, rather than replacing that route. No forbidden SGA source is used.
