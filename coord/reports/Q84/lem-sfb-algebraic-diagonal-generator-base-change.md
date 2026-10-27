# Q84 stage-1 report: lem-sfb-algebraic-diagonal-generator-base-change

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-diagonal-generator-base-change.json: unchanged statement, eight proof steps; split.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-rhom-finite-flat-base-change-model.json: statement; unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-fibrewise-flat-complex-concentration.json: statement; unsplit; no Mathlib match.
- citations.json: one verbatim statement quotation for each node cited in each proof step.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, relativeDualizing, relative_dualizing, diagonal/generator, pseudo-coherence and relative Tor terminology. No project declaration states this item or either new lemma. Ordinary diagonal generators and coefficient comparison declarations have different objects.

## WANTED

None. The source files used are present locally.

## Corrections and remaining work

The item was a new unsplit node without an argument. Its full statement is retained, including the B-module derived isomorphism, the specified map on the chosen generator, arbitrary scalar extension and absence of Noetherian assumptions. There is no STATEMENT-DISPUTED issue. I did not use the invalid shortcut that a bounded-below complex of flat modules automatically computes derived tensor. Instead I retained the finite Noetherian model, checked its residue-field fibres, and isolated the universal truncation argument. The new model explicitly states that the termwise base changes of P and F represent the base-changed objects; the proof therefore uses its statement rather than an unstated construction from its proof. The two new lemmas remain statement-only for subsequent workers. No stage-2 or stage-3 work, repository edits, compiler calls or agent delegation occurred.

## Sources and proof plan

I read dualizing.tex Tag 0E2F, lemma-base-change-relative-dualizing, from its statement through the final generator sentence; Tag 0E2E, lemma-relative-dualizing-noetherian; Tag 0BZV, lemma-base-change-relative-algebraic; and Tag 0E2D, lemma-uniqueness-relative-dualizing. For the first new node I read more-algebra.tex Tag 0E1U, lemma-compute-RHom-relatively-perfect, including its optional finite-presentation clause and the termwise formula in proof (b). For the second I read the last two paragraphs of 0E2F and algebra.tex Tag 00ME, lemma-mod-injective. It is the general complex calculation used there, not another diagonal-duality assertion. The current blueprint was read under literature/blueprint/latest: sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, clause (3). The inherited long support chain and null blueprint ancestor were retained, consistently with blueprint_refs.py ancestor; the generic algebraic prerequisite does not change the unit or chapter route.

The eventual proof of the new concentration lemma uses Q^i=coker(E^{i-1}->E^i). For i != 0 the fibre hypothesis says Q^i tensor k(p) -> E^{i+1} tensor k(p) is injective. At every prime q of S above p, 00ME applies to the finite source over the Noetherian local ring S_q and the R_p-flat target. Thus Q^i -> E^{i+1} is universally injective and its cokernel Q^{i+1} is flat. Its source is flat as the kernel between flat modules. These assertions localize and give universal exactness away from zero. Q^1 flat gives Z^0 flat and kernel base change; Q^{-1} flat and the assumed flat H^0 give universal exactness of 0 -> Q^{-1} -> Z^0 -> H^0 -> 0. The two indicated truncation maps are consequently quasi-isomorphisms after every tensor. This argument is recorded here, not as a proof in the new statement-only node.

## Searches and reuse

I searched the whole DAG by tags 0E1U, 0E2F, 0E2C, by the labels compute-RHom-relatively-perfect, mod-injective, flat-finite-presentation-limit-flat, and by diagonal Hom, fibrewise concentration and bounded-below flat complex terminology. The existing quotient pseudo-coherence, algebraic shriek, polynomial-perfectness, arbitrary-ring uniqueness, flat-subring approximation and perfect-coinduction exchange statements were reused. blueprint_refs.py search was run for diagonal generator, Hom relatively perfect, compute-RHom-relatively-perfect, relatively perfect, fibrewise cohomology and bounded below flat. No imported node states either new assertion. The broad RHom and flat-subring searches gave unrelated coefficient or geometry statements; none supplies this module-complex model.

All new-node Mathlib queries were actually run using msearch.py and are preserved in searches.jsonl and the two result JSON files. Both new nodes have LeanFinder searches with a second phrasing, Loogle, LeanSearch and source grep. I read the hits and inspected Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean and Mathlib/RingTheory/Flat/CategoryTheory.lean. CochainComplex.HomComplex constructs a Hom complex but does not assert this relative derived-Hom representation or its universal scalar comparison. Module.Flat.lTensor_shortComplex_exact and its right-tensor version preserve exactness when the tensor factor is flat; they do not prove fibrewise concentration or the universal truncation comparison here. The narrower follow-up greps had no hits. Every reported service was available; no unavailable response was reclassified as absence.

## Not duplicates

- lem-sfb-fibrewise-flat-complex-concentration vs lem-trf-specialization-external-product: the existing statement concerns specialization and nearby-cycle external products with finite coefficients; the new statement concerns universal truncation of module complexes over Noetherian rings.
- lem-sfb-fibrewise-flat-complex-concentration vs lem-sfb-relative-dualizing-pair-base-change: the existing statement is scheme-level base change of a coherent dualizing pair; the new node is a generic complex over Noetherian rings, with no schemes, diagonals or dualizing pairs.
- lem-sfb-fibrewise-flat-complex-concentration vs lem-sfb-proper-flat-dualizing-polynomial-model: the existing statement constructs a proper-duality object and its polynomial charts; the new statement is a criterion for universal truncation of an arbitrary complex.
- lem-sfb-fibrewise-flat-complex-concentration vs lem-sfb-polynomial-diagonal-adjunction-scalar-naturality: the existing node asserts a polynomial-diagonal adjunction and its normalized scalar-naturality square; it has no fibrewise finite-flat-complex concentration criterion.
- lem-sfb-fibrewise-flat-complex-concentration vs lem-sfb-algebraic-diagonal-generator-base-change: the item concerns a supplied relative-dualizing complex and its diagonal generator; the new node concerns an arbitrary finite flat complex and a specified universal truncation zigzag, without a diagonal or dualizing object.
- lem-sfb-fibrewise-flat-complex-concentration vs lem-sfb-relative-duality-polynomial-base-change: the existing statement compares scheme dualizing pairs using polynomial charts over locally Noetherian bases; the new node provides only a general algebraic complex criterion.

- lem-sfb-fibrewise-flat-complex-concentration vs lem-weil-pbc-flat-mod-injective: the existing local module-map criterion proves injectivity and a flat cokernel; the new lemma concerns a whole cochain complex, universal concentration and the specified truncation zigzag, requiring the criterion at all primes and degrees.
- lem-sfb-fibrewise-flat-complex-concentration vs lem-trf-flat-graded-fibre-regular-lift: the existing statement lifts a regular initial form in an associated graded ring; the new lemma has no ideal filtration or nonzerodivisor assertion and concerns universal cohomological concentration.
- lem-sfb-fibrewise-flat-complex-concentration vs lem-trf-noetherian-arrow-eventual-injective-flat-cokernel: the existing statement descends injectivity and flat cokernels through a directed system of local rings and finite modules; the new lemma has no directed system and compares canonical truncations of a fixed complex under every ring extension.

No existing node mentions Tag 0E1U or its lemma label, and no duplicate of the new relative Hom model was found.

## Review by Q84

I checked B through E of delivery-errors.md with the item, both new statements, the cited node statements and the sources open. Both new nodes introduce all objects and assumptions, have empty proof/proof_deps and null proof_origin, and use actual source tags/labels. The model lemma is 0E1U with both source and target pseudo-coherent and the target of finite relative Tor amplitude, which ensures its additional finite-presentation clause. The concentration lemma keeps the Noetherian hypothesis on the auxiliary algebra and finite generation of every term, so that the local criterion applies; its base-changed ring is deliberately allowed to be arbitrary. Neither is a clause of the diagonal-generator theorem: both are general complex tools with different input data.

The step-by-step statement audit is as follows.

Step 1 cites lem-weil-pbc-flat-module-base-change, lem-sfb-perfect-coinduction-tor-independent-exchange. Flat module base change supplies the flat tensor algebras. The exchange node explicitly supplies its tensor comparison theta_N for every N without a perfectness assumption; only its coinduction comparison gamma requires perfectness. I used theta here. Applying it to the diagonal gives A rather than a wrong fibre or a Tor-uncorrected tensor. Associativity gives the displayed target and the same derived-extension map.

Step 2 cites def-pc-ring-pseudo-coherent-complex, lem-pc-module-bounded-flat-kflat, lem-pur-derived-change-of-rings, lem-sfb-relative-rhom-finite-flat-base-change-model, lem-weil-pbc-flat-module-base-change, lem-weil-pbc-flat-tensor-exact. The pseudo-coherent definition supplies a finite-free bounded-above representative. The module bounded-flat K-flat lemma applies to this bounded-above representative and to bounded flat F. The change-of-rings statement computes their scalar extensions. The new model now explicitly supplies F tensor T as a representative, and flat module base change and flat-tensor exactness justify its interval and the coprojection calculation. No pseudo-coherence of an arbitrary finitely presented module is inferred.

Step 3 cites lem-trf-algebraic-shriek-calculus, lem-trf-algebraic-shriek-relative-perfect, lem-weil-pbc-finite-type-algebra-noetherian. The three cited statements give the polynomial shriek model, relative perfection and Noetherian tensor algebras. In the shriek statement I checked the flat-base-change clause, the surjection clause including the restriction of the coinduction action, and composition on a bounded-below input. Multiplication composed with the second coprojection is the identity; this proves the derived diagonal assertion, not only a statement after restriction to an unrelated ring.

Step 4 cites lem-trf-flat-polynomial-quotient-perfect, lem-sfb-perfect-coinduction-tor-independent-exchange, lem-trf-algebraic-shriek-calculus, lem-trf-algebraic-shriek-relative-perfect. Polynomial-quotient perfectness supplies exactly the perfect input needed by the coinduction exchange. Tor independence is checked by flatness over D and theta, rather than by flatness of D->T. The resulting coefficient is P_T[e], exactly the polynomial model in the shriek statement. This step is used only for Noetherian targets, especially residue fields.

Step 5 cites lem-sfb-flat-fp-quotient-pseudocoherent, def-pc-ring-pseudo-coherent-complex, lem-sfb-relative-rhom-finite-flat-base-change-model. The quotient pseudo-coherence statement applies because multiplication is surjective and both algebras are flat finitely presented over D. C[0] has a one-term finite-free C representative. The new Hom-model statement gives the full finite flat E and the class comparison, without pretending that its bounded-below E is K-flat.

Step 6 cites lem-sfb-fibrewise-flat-complex-concentration, lem-sfb-relative-rhom-finite-flat-base-change-model, lem-pur-rhom-global-sections. The concentration statement is used with S=Q, finite terms from the model, fibrewise vanishing from Step 4 and H^0(E)=C flat from Step 3. Its specified truncation maps identify the actual map [z] tensor t -> [z tensor t]. The Hom/global-sections statement on the one-object site identifies H^0 with the derived morphism group; this is the needed Hom identification, not merely fully faithful Yoneda.

Step 7 cites lem-trf-flat-subring-model-system, lem-weil-pbc-finite-type-algebra-noetherian, lem-sfb-arbitrary-ring-relative-dualizing-isomorphism. The flat-subring statement supplies a flat model at an actual finite stage. The finite-type theorem applies after the elementary principal-ideal proof that Z is Noetherian. The arbitrary-ring uniqueness statement is used with N and the supplied M, whose pseudo-coherence, finite relative Tor interval and full derived diagonal Hom are all established. It asserts no generator compatibility, and I did not attribute such a clause to it.

Step 8 cites lem-sfb-relative-rhom-finite-flat-base-change-model. This is the elementary assembly of the generator comparison already given by the new Hom-model statement and Step 6. I wrote the inverse-image class eta, the precomposition action, the surjective cyclic generator map, and the functorial equality gamma-prime=alpha-prime composed with eta-prime. Pure tensors prove preservation of this surjection. No compatibility is smuggled into the arbitrary-ring uniqueness isomorphism.

I tested the model on K=S[0], where E=F and the comparison is scalar extension itself, and on shifted free sources (the Hom differential has the usual sign). I checked boundedness directions: finite-free P is bounded above, bounded F makes Hom(P,F) bounded below, with finite sums in every degree. The criterion holds for a one-term flat finite module and for a split acyclic two-term complex; a shifted nonzero single module fails its fibre hypothesis, as it should. For nonflat extension, the polynomial example R=Z, A=Z[x], R′=F_p retains the dualizing shift under the perfect exchange and is covered. Zero rings and the empty spectrum cause no generator exception: the diagonal modules and derived objects are zero, and the zero element generates the zero module. Every proof step is under 2000 characters; the two real complex subclaims were extracted into the new nodes, rather than hidden inside a long step. Citations were regenerated after the explicit F-base-change sentence was added, so each quote is verbatim in the final statement.

## Unfinished work

Only the proofs of the two new statement-only prerequisites remain for later DAG items. The item proof and the requested direct delivery are otherwise complete subject to the server checks.

## Resumed direct-delivery check

The required initial dry run of the retained sandbox stopped at three additional same-tag comparisons for Tag 00ME. I opened all three current statements. The local injectivity criterion is the input used degree by degree in the concentration argument, while the graded-regular-lift and directed-system descent statements have different hypotheses and conclusions. I added the three explicit comparisons under Not duplicates. The repeated dry run then exited successfully: OK (not pushed), preflight passed. I also rechecked every cited current statement and all 25 verbatim quotations against the final sandbox, including exact coverage of the eight steps. Their lengths range from 755 to 1027 characters. The retained searches and full saved results were read; no searches were invented or rerun. The item statement still agrees exactly with the current repository.
