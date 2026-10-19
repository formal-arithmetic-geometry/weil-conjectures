# Q97 — lem-trf-lci-pointwise-criterion

## Files written

- dag/nodes/sec-trace-formula/lem-trf-lci-pointwise-criterion.json — statement, split in nine steps; no Mathlib match; statement and statement dependencies unchanged.
- dag/nodes/sec-trace-formula/lem-trf-essentially-finite-type-ci-kernel-invariance.json — one new statement-only unsplit algebra lemma (Stacks 00SF); no Mathlib match.
- citations.json — one verbatim statement quotation for each step/node citation.
- searches.jsonl — the command's actual search log; inherited item search records are retained, and newly run searches are appended to the item and recorded for the new node as applicable.

## Attachments

None. I searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint tag and item id, and for complete-intersection/CompleteIntersection/lci terminology. No declaration there states the item or the new lemma. The upstream master is reference material only and is not treated as a finished proof.

## WANTED

None. All mathematics used follows the local Stacks source.

## Problems in the item, blueprint, or brief

No statement correction was needed. The imported statement agrees with Morphisms 01UG and the algebra clause of 00SH, with the quotient definition of 00SD. The given definition of finite regular sequence already requires nonzero final quotient, so the zero-ring convention causes no nonzero local-ring claim. The item is a historical auxiliary below the nodal-chart route recorded in blueprint.from; it does not state the current contracting-correspondence theorem. I retain that provenance and do not change the unit or chapter.

The main non-elementary input absent from the DAG was independence of a regular-sequence kernel under changing an essentially finite type regular local presentation. Creating a new 00SG neighbourhood criterion would merely restate an essential clause of the item. Instead the proof constructs the polynomial-local surjection and its kernel explicitly, changes regular presentation via the new kernel lemma, and invokes the existing 00SC spreading theorem.

The newly created lemma's source says essentially finite presentation in the universal condition, while its surrounding definition and proof also use essentially finite type. Over the base field these notions agree; the regular local source is a localization of a finitely generated algebra over a Noetherian field. The statement is the (1) to (2) equivalence of 00SF applied in both directions, with the definition of 00SD expanded.

## Unfinished work

Nothing remains for this one-level split. The single new lemma is intentionally statement-only and is not recursively split. No Lean was written or compiled; no build, Lake, or local maintainer check script was run.

## Not duplicates

lem-trf-essentially-finite-type-ci-kernel-invariance vs lem-trf-regular-local-surjection-kernel-comparison: the existing 00SE statement requires a chain of surjections U→V→W, with U and V regular. The new 00SF statement compares two unrelated regular local k-algebra presentations P→A←Q, assuming essential finite type, without a comparison P→Q or Q→P. That is precisely what the two unrelated presentations in step 4 require.

lem-trf-essentially-finite-type-ci-kernel-invariance vs lem-trf-complete-local-ci-presentation-independence: the existing 09PZ statement requires the common target to be complete Noetherian local; S_q in this item need not be complete. The new lemma uses essential finite type over a field, with no completeness hypothesis.

lem-trf-essentially-finite-type-ci-kernel-invariance vs lem-trf-regular-quotient-completion-kernel-test: the existing 09Q1 statement compares the kernel defining R/I with a presentation of its completion. The new lemma compares two presentations of the uncompleted algebra itself, and invokes no completion.

lem-trf-essentially-finite-type-ci-kernel-invariance vs lem-trf-lci-pointwise-criterion: the new statement is a generic comparison of kernels in two regular local rings. It neither asserts the existence of an affine neighbourhood nor an equivalence between a scheme property and local rings, and cannot replace the item's polynomial-kernel calculation or the 00SC neighbourhood step.

lem-trf-essentially-finite-type-ci-kernel-invariance vs lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection: the existing 00SY statement assumes an already given global-complete-intersection principal neighbourhood in the fibre and flatness, then constructs a relative global complete-intersection presentation of the source algebra near a prime. It does not compare the kernels of two unrelated regular local presentations. Its incidental source mention of 00SD defines the fibre hypothesis only.

There are no existing nodes sourced at 00SF/lemma-lci-local. Whole-DAG searches for 00SF, 00SG, 00SD, regular-local surjections and complete intersections, and blueprint_refs searches for 00SF, regular local surjection, complete intersection and local ring found no equivalent blueprint statement. Broader candidate statements above were opened and compared, not inferred from their titles. The existing 00SC, polynomial regularity and global-equations regularity nodes are reused. No new definition or elementary auxiliary node was created.

## Review by Q97

I read the worker brief, stage-1 rules, the three blueprint levels in SETUP, GOAL and dag-sync, and delivery-errors B through E in full. I read the unit sk-i-curve-zero and chapter sec-trace-formula records, the item's provenance and its citer lem-trf-lci-affine-open-locality. The split does not cite that citer, avoiding the obvious cycle. I read the local Stacks Morphisms proof of 01UG, Algebra 00S9 and 00SD, the complete statements and proofs of 00SF, 00SG and 00SH, and the relevant 00SC proof paragraphs. The new node is sourced to 00SF, whose comparison is what step 4 needs; it has only its statement, no hidden proof or proof dependencies. I also checked the tag-to-label mapping in stacks-project/tags/tags.

Step 1 uses the global presentation and dimension condition actually given by def-weil-pbc-complete-intersection-over-field. I opened the statements of lem-weil-pbc-global-complete-intersection-local-regular-sequence and lem-weil-pbc-polynomial-ring-field-regular-ring: the former applies at every prime containing the equation ideal (not just maximal primes), and the latter makes the polynomial localization regular local. Essential finite type is exactly localization of a finite type algebra in its cited definition. The quotient-localization identification is proved by fractions in the step. Nonzero T and the prime ensure the regular sequence lies in a proper ideal; zero T has no primes.

Step 2 uses the actual principal-cover definition, not any locality conclusion from the definition node. It selects h outside q and writes both inverse fraction maps identifying S_q and (S_h)_{q_h}; it then uses the already proved step 1. This two-line localization verification is elementary. Step 3 writes the finite-generator evaluation surjection and quotient presentation, proves surjectivity of its localized map, calculates its kernel IP_p using an actual lifted annihilator outside p, and checks localness. The definition nodes cited there provide the localization and essential finite type notions; the kernel calculation is not attributed to a definition.

Step 4 applies the new kernel comparison only after verifying that both sources are regular local, both are essentially finite type over the same field, both maps are surjective local k-algebra maps, and their common nonzero target A is essentially finite type. The witness R→A comes from the item's actual local definition. The independent polynomial source is regular by the opened polynomial-ring node. Step 5 takes exactly the conclusion of the opened 00SC (5)→(1) node: generation of IP_p by a regular sequence produces g outside q with S_g a global complete intersection. It makes no unsupported claim about dimensions or conormal modules. Step 6 assembles these g into the defining principal cover, proving the algebra clause; the definition allows an infinite family, so quasi-compactness is unnecessary here.

Step 7 uses clause (c) of the opened affine-open-stalk-localization statement, including the germ formula, to obtain the correct k-algebra identification and the algebra result of step 2. Step 8 takes an actual finite type affine chart from the locally-finite-type definition (the target is Spec k). It then uses the same affine stalk lemma, the previously proved steps 3–5, and clause (b) of the opened affine-open-section-vanishing-prime Mathlib leaf: the principal open is affine and its restriction map localizes the coordinate ring. This is a scheme-and-section statement, not just the topological homeomorphism supplied by spec-localization-away-basic-open, which would have been insufficient. The scalar compatibility follows directly from the stated germ and restriction maps. Step 9 uses g=1 in the cover definition to see that a global complete intersection is local, then closes the implication cycle. It keeps empty X and the empty cover explicit.

Small cases checked: X empty and S=0 (vacuous primes and empty covers); k itself (zero polynomial variables, empty sequence); k[t]/(t^2) (nonreduced complete intersection); k[x,y]/(xy) at the node and at a generic point; an inseparable field algebra k[t]/(t^p-a) over an imperfect characteristic-p field (no smoothness or separability is substituted for the local complete-intersection condition). For the new node, the presentations k[x]_(x)→k and k[y,z]_(y,z)→k have regular kernels of different lengths, which its statement permits; identity presentations give the empty-sequence case. The non-CI ring (k[x,y]/(x^2,xy,y^2))_(x,y) has a height-two kernel needing three generators in the standard regular local presentation, so the lemma asserts no spurious regular sequence in another presentation. No equidimensionality, algebraic closure or completeness hypothesis was imported into the item.

I inspected all Mathlib search hits, including the presentation-dimension comment at RingTheory/Extension/Presentation/Basic.lean:103 and the regular-sequence transport results; these do not compare kernels in two unrelated regular local presentations. Semantic searches were tried in a second phrasing, as were item searches in algebra and scheme language. All new records come from searches.jsonl; no unavailable service was recorded as an empty result. The new node has no Mathlib match and no attachment.

All nine proof steps are shorter than 2000 characters. The three off-unit algebra facts are declared as generic tool uses in split_report: they supply algebraic input beneath the existing unit route, not a replacement route. Definition and Mathlib-leaf citations need no such declaration. I generated citations.json from the actual statements and checked every quote is a literal substring. The overlay's dependency closure is acyclic and proof_deps is exactly the union of uses. The required server dry run and push follow this review.

The first captured dry run requested an additional same-tag comparison with lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection (its source also mentions 00SD). I opened that entire node and added the explicit distinction under Not duplicates; its hypotheses already assume a global-complete-intersection fibre neighbourhood, so it cannot supply the missing independent-presentation comparison.

The server preflight then rejected the phrase “as in the item” in step 3 as a self-containedness issue (B2). I replaced that phrase by the full assumption A≅R/(a_1,…,a_c), with R regular local and essentially finite type over k and the sequence regular in its maximal ideal. I also expanded the corresponding shorthand conclusion in step 1. The item statement and every proof citation are unchanged.
