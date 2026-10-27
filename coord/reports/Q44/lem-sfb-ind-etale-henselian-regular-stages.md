# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ind-etale-henselian-regular-stages.json`: existing statement, now split into seven steps; no exact Mathlib match for the whole assertion.
- `citations.json`: one verbatim statement quotation for every citation in every numbered step.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean source or repository file was written; no compiler or build command was run.

## Attachments

None for the item. The existing `lem-sc-regular-connected-integral` already records `AlgebraicGeometry.IsRegular.isIntegral`; its current source is `lean/WeilConjectures/AlgebraicGeometry/Regular.lean:249`. That theorem only supplies the connected-integrality step, not the ind-etale regularity and parameter clauses, so it is not an attachment of this item.

## WANTED

None.

## Problems checked and corrections

The statement is true as written, and was retained verbatim, including nonempty connected spectrum, Noetherian target, the Jacobson-radical condition, and the empty parameter list. The source metadata calls Tag 031E `lemma-flat-over-regular`, but the Stacks tag table and source identify 031E as `lemma-flat-over-regular-with-regular-fibre`. The former label is Tag 07DY and proves a different flatness criterion. I retained the maintainer-owned source metadata and used the correct label in proof-step citations. I also checked the weakly-etale base-change tag in the local tag table: it is 092H.

There was no earlier sandbox split or report to continue. I searched the project for the exact blueprint tag and for ind-etale/regularity declarations; none proves all clauses. Prior research embedded in the item was retained. The searches run here are logged in `searches.jsonl`; LeanFinder and LeanSearch returned etale definitions and flat preservation of regular sequences, not this complete assertion. Loogle reported unknown identifier `Algebra.IndEtale`, which is an uninformative pattern result, not evidence by itself. The Mathlib grep for indEtale and regularity was empty. The second semantic phrasing found `RingTheory.Sequence.IsWeaklyRegular.of_flat` and `RingTheory.Sequence.IsRegular.of_faithfullyFlat`; those are not needed because the argument transports the whole parameter system using a field fibre and the dimension equality.

I searched all DAG statements and source tags for 031E, 092Q, connected regular schemes, parameter quotients, finite-etale algebras over fields and Noetherian localizations, and ran blueprint_refs searches for ind-etale, regular local, regular sequence, flat regular, henselian, regular domain and parameter. Existing nodes suffice. The blueprint ancestry tool returns `None`: an inherited created.item chain is broken before reaching an imported blueprint node. I retained the supplied nonempty place and via chain rather than invent an imported ancestor. The supplied place serves paragraph (3) of the current `det-thm-sf-ctf-stability-direct-images` proof. I read that proof, the current unit file, the recorded chapter and unit records, and GOAL.md. The ring-theoretic tools do not replace the unit's open/proper direct-image route.

## Not duplicates

No new nodes were created. Existing nodes are cited in place of new regular-ascent, connected-integrality, Noetherian-permanence, finite-etale-product and parameter-quotient nodes.

## Review by Q44

I read the source with each claimed fact open: Stacks more-algebra.tex Tag 092Q (`lemma-absolutely-flat-over-field`), its proof's absolute-flatness paragraph and the subsequent weakly-etale-field discussion; algebra.tex Tag 00U3 (`lemma-etale-over-field`), Tag 031E (`lemma-flat-over-regular-with-regular-fibre`), Tag 00ON (`lemma-dimension-base-fibre-equals-total`), Tag 00NQ (`lemma-regular-ring-CM`), Tag 00FN (`lemma-Noetherian-permanence`), and Tag 00HT (`lemma-flat-localization`); properties.tex Tags 0569 and 033N. I checked all cited node statements, not their proofs, against what each step takes.

Step 1 uses `lem-weil-pbc-ind-etale-stability` for ind-etale implies weakly etale and stability under base change. `def-weil-pbc-ind-etale-algebra` explicitly includes flatness in weak etaleness. `lem-weil-pbc-weak-etale-field` explicitly states both reducedness and that each finitely generated field-subalgebra is finite etale. The base-change field is the residue field at an arbitrary prime of B; no finite-type hypothesis on C is inserted.

Step 2 again uses the exact finite-subalgebra assertion of `lem-weil-pbc-weak-etale-field` and the product-of-fields statement of `lem-weil-pbc-etale-algebra-over-field-product`. It proves the field-localization conclusion itself: coordinatewise inverse-or-zero produces a=a^2b; the same identity holds for a/s; a nonzero nonunit would be annihilated by the unit 1-uv. This is a short elementary ring computation from those statements, not a new absolute-flatness node and not a disguised invocation of reducedness implying a field. `def-weil-pbc-localization-at-prime` supplies the local ring and its proper maximal ideal. The zero fibre is handled without assigning a field structure to it.

Step 3 uses precisely the quotient-of-localization description in `lem-weil-pbc-fibre-ring-localization-quotient`, the permanence conclusion of `lem-weil-pbc-localization-noetherian`, and the surjective-image conclusion of `lem-weil-pbc-surjective-image-noetherian`. This verifies the Noetherian condition missing from a claim merely that fibre localizations are fields. `def-weil-regular-scheme` says exactly that a Noetherian ring with regular localizations is regular. Fields have dimension zero and maximal ideal zero directly, including that their only prime is zero. This is elementary assembly.

Step 4 cites `lem-weil-pbc-regular-map-ascent`, whose statement assumes regular source, Noetherian target, flatness and regular fibres; these are respectively the given hypothesis, the given hypothesis, step 1 and step 3. It gives precisely regularity of C, with no geometric-regularity or finite-presentation assumption required.

Step 5 uses `def-weil-regular-scheme` to regard Spec C as regular, `lem-sc-regular-connected-integral` for a nonempty connected regular scheme being integral, and the explicit affine-open characterization in `def-pc-integral-scheme` for C to be a domain. Nonemptiness is checked here, so neither the zero ring nor a disconnected product is called a domain.

Step 6 uses `lem-weil-pbc-flat-local-ring-maps` for both flatness/locality and Noetherianity of B_p -> C_m. The contraction p need not be maximal in B; the cited statement allows any prime. `lem-weil-pbc-fibre-ring-primes-bijection` supplies the fibre prime over m, and `lem-weil-pbc-fibre-ring-local-ring-iso` states exactly the identification with C_m/p C_m. I use the local-dimension equality explicitly stated as the equivalent formula in `lem-weil-pbc-flat-height-formula`. The closed fibre is nonzero and a field by step 2; its kernel is therefore the unique maximal ideal of C_m and its dimension is zero. The Jacobson condition puts every t_i in m, hence in its contraction p, so the parameter-extension hypothesis really applies. I did not assume p was maximal or that the original map was faithfully flat.

Step 7 uses `def-weil-pbc-regular-system-of-parameters` for the full list's length and maximal-ideal generation. Step 6 carries these two conditions to S, because pS=mS and dim R=dim S. The statement of `lem-weil-pbc-regular-local-generators-regular-sequence` then gives both the full regular sequence and every initial regular local quotient, including c=0. `def-weil-pbc-regular-sequence` provides the exact injectivity and nonzero-quotient conditions: the first r injectivity conditions are a subset of those of the full list, and the quotient is nonzero because all t_i lie in the proper maximal ideal. Thus no flat-regular-sequence lemma or uncited preservation theorem is hidden here.

Small cases checked: r=0 and dimension zero; B a field and C a nonzero separable algebraic field extension; empty fibres (for example Z -> Q at a nonzero prime with r=0); B disconnected with connected C; the excluded zero C; and a disconnected finite etale product, which shows why connectedness cannot be discarded for the domain conclusion. No henselian-pair or excellence hypothesis is used or needed. I checked the B--E checklist: statements remain self-contained, no new unsplit proof is hidden in a statement, every non-elementary invocation is a cited statement, no clause was moved into a new node, the parameter prime is correct, and no identification is asserted merely by saying it transports. All proof steps are below 2000 characters. The proof is agent assembly of the listed sources, recorded as such. Every off-unit theorem used as a generic tool is declared in split_report.tool_uses.

## Unfinished work

None of the authorized stage-1 split remains. Required server dry run and direct delivery follow this report; their process output is the delivery evidence.
