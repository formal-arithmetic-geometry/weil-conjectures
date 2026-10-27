# Q43 — lem-sfb-scalar-direct-image-mate-coherence

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-direct-image-mate-coherence.json: statement; split in five steps. No exact whole-item Mathlib match. All generic mate results are existing DAG leaves.
- citations.json: one verbatim current-statement quotation for every citation of every proof step.
- searches.jsonl: searches performed by msearch.py. No new nodes or Mathlib leaves.

## Attachments

None. I searched the live WeilConjectures tree for the item tag and for scalar/direct-image/mate/coherence terminology. The item tag is absent. ChangeOfCoefficients.lean:231–257 defines derivedPullIso and derivedPushHom under an exactness/flatness hypothesis on extension of scalars; it does not state the unrestricted item or all its identities. Generic project mate theorems also do not state the complete item. No attachment is claimed on the basis of a sorry declaration or a proper subset of the clauses.

## WANTED

None. The current blueprint and local Mathlib source suffice for this formal argument. No SGA source was used.

## Corrections and source alignment

The imported created node had doubled TeX backslashes in the decoded statement. These were normalized to single TeX backslashes; every object, quantifier, hypothesis and conclusion is mathematically unchanged. No STATEMENT-DISPUTED mathematical correction is needed. The source path now points to literature/blueprint/latest, specifically the direct-image proof's Formal properties and Preservation paragraphs and the pullback proof's parts (1), (3).

The source says "mates ... compatible with composition" without exhibiting the substitutions. Steps 1–4 supply them, retaining the unit's formal mate route. The narrower invertibility arguments later in the source are unused: the item only asserts existence and coherence of a morphism. In particular, no flatness, boundedness, constructibility, or isomorphism of gamma was imported from those later paragraphs.

For the compositor I use the general composable-scheme-map clause of the existing def-sfb-test-map-derived-composition, not a test-object assertion from its proof. Its statement explicitly defines the canonical ordinary unbounded condensed-module direct-image comparison by conjugating the inverse pullback compositor under the actual composite adjunction. This applies to arbitrary commutative condensed rings, so it does not restrict this item to the admissible rings of some other compositor nodes. It is declared as a generic tool in split_report.tool_uses, along with the specified ambient adjunction definition. No top-level tool_uses approval is written.

## Not duplicates

No new nodes. The pre-existing def-weil-pbc-adjunction-mate and lem-weil-pbc-mate-pasting already state the generic facts needed. The pre-existing lem-pur-mate-unit-compatibility and lem-amb-mate-unit-counit already cover the unit and counit clauses. Thus no generic mate lemma or restated clause was created. lem-sfb-derived-scalar-mate-composition supplies related geometric coherence, but its representative-normalization context is unnecessary here; I use the abstract mate-pasting leaf directly, so no hidden equivalence between its normalization and the item's one is needed.

## Searches and Mathlib verdict

Searches used only the required msearch.py command. I read the returned hits and Mathlib/CategoryTheory/Adjunction/Mates.lean:55–218, including mateEquiv, mateEquiv_counit (123), unit_mateEquiv (136), mateEquiv_vcomp (170), and mateEquiv_hcomp (209). These are exactly the generic calculus already represented by existing nodes. Natural-language searches returned underived SheafOfModules/PresheafOfModules pullback or pushforward statements and generic mate calculus, not the specified derived coefficient comparison with its canonical identifications. A second semantic phrasing was run. A malformed application-shaped Loogle query was recorded honestly as rejected; the valid Adjunction/mate query succeeded. Earlier item searches were retained. No new search or result was invented, and no new Mathlib node is required.

Blueprint searches: blueprint_refs.py ancestor found det-prop-scalar-six-direct-image. Searches for mate, mate pasting, and scalar direct image, together with whole-DAG keyword and declaration searches, found no distinct blueprint node stating the entire unrestricted item. same_as is therefore empty. The source ancestor itself contains the formal claims but also an invertibility assertion under standing coefficient/constructibility assumptions; it is not an independent whole-item duplicate.

## Review by Q43

I read coord/delivery-errors.md B–E whole (both copies), the worker and stage-1 briefs, the three levels in SETUP, GOAL, the six-functor chapter and scalar-six unit, and the current blueprint direct-image statement/proof and pullback proof. For this item the relevant source is the Formal properties paragraph and the successive-coefficient reduction in Preservation. No new node needs a separate source reading. The statement introduces all rings, schemes, categories and functors, and the proof retains exactly those domains.

For step 1 I opened def-weil-pbc-adjunction-mate, def-sfb-module-derived-pushpull-adjunction and det-prop-scalar-six-pullback. The first says that the explicit unit–square–counit composite is a natural transformation and gives the bijection; the second supplies the actual geometric adjunction for any commutative condensed ring; pullback part (1) supplies the natural comparison in precisely the required orientation after inversion. Taking G=T_Y, H=T_X makes the component formula literally the item's gamma, rather than an unspecified comparison with isomorphic source and target.

For step 2 I opened both existing Mathlib leaf statements. With exactly the step-1 variables, the unit leaf yields gamma at L_f N followed by T_Y eta, and the counit leaf yields epsilon-prime after L_f gamma. Their right sides are exactly the two displayed equations. Neither leaf assumes gamma invertible. Their Mathlib types and orientations agree after reversing Lean's diagrammatic composition notation.

For step 3 I read def-sfb-test-map-derived-composition's whole statement and verified that its final clause is for arbitrary composable scheme maps and arbitrary commutative condensed rings, not merely pi_{X,P}. It supplies the adjunction-normalized compositor required by pasting; det-prop-scalar-six-pullback (1) supplies geometric compatibility. I checked every category in lem-weil-pbc-mate-pasting (2): A is D(W,Lambda), B is D(Y,Lambda), C is D(X,Lambda), D/E/F are the corresponding primed categories; L1=L_g and L3=L_f, so the composite right adjoint is R_g R_f. Thus its formula gives R'_g(gamma_f) after gamma_g at R_f K, in the stated order. No claim from the proof of a cited node is used.

For step 4 I reopened the mate-pasting leaf, the ambient adjunction statement, the mate definition and pullback parts (1), (3). There are three coefficient rows; all geometric adjunctions exist for these rings. Pasting along the scalar functors gives d=(T_X^b c_f^a)(c_f^b T_Y^a) and delta=gamma^b(T_X^a K) T_Y^b(gamma^a(K)). Pullback part (3) asserts compatibility with successive scalar extension, which in the inverse direction is exactly c^{ba} L^2(s_Y)=(s_X L^0)d. I explicitly checked the two whiskerings in the mate formula: naturality of eta^2 handles s_Y; naturality of s_X at epsilon^0 handles the target. This gives R^2(s_X) delta=gamma^{ba} s_Y, not an equation with the associators reversed. The calculation is elementary after the cited pasting theorem and is written out inside this 1126-character step; it hides no separate comparison theorem.

For step 5 I read sk-def-sfb-coefficient-change: it defines actual module-derived extension and states both coefficient squares and functoriality of a_X. Together with the actual module-derived c and s of the pullback proposition, all compositions above are already module-derived morphisms. The proof never uses equality after forgetting coefficients to infer equality upstairs. This is why no conservativity or full faithfulness assertion is needed. The imported sk-prop-sfb-cartesian-coefficients statement lists admissible coefficients in its displayed theorem, whereas the item is unrestricted; I do not extend that narrower theorem to arbitrary rings. The proof uses the unrestricted pullback proposition and coefficient-change squares instead.

Small-case tests: with f identity and normalized identity comparisons, the formula reduces to the identity scalar functor; with identity scalar maps it reduces to the identity on R_f. With either a or b identity, the scalar equation reduces through the canonical scalar unitor to gamma^a or gamma^b. The zero object satisfies every displayed equation. For nonflat a (e.g. Z to Z/2 as discrete condensed rings), the argument still concerns the unbounded derived scalar functor and does not replace it by ordinary tensor. I also checked that a natural isomorphism c alone does not force its mate to be invertible; no such invalid inference is present.

B checks: no new unsplit node or hidden proof in a new statement; single-escaped TeX repaired; every cited notion already exists. C checks: every non-elementary invocation has a matching cited statement, and citations.json quotes it verbatim; proof_deps is exactly the union of uses. D checks: no clause was merely moved into a fresh node; the substitutions, pasted square and scalar-associator argument carry the proof. E checks: every domain and composition direction was type-checked in ordinary mathematical notation, without compiler use; no extra geometric or coefficient hypotheses appear. All five steps are below 2000 characters, and there is no new statement requiring a small-case audit beyond the unchanged item.

## Unfinished work

None at stage 1. No Lean file was written or compiled. Dry-run and delivery diagnostics are recorded below after execution.

## Validation

The required deliver.py --no-push exited 0 and printed OK (not pushed) at ebfb23890dc: preflight passed. This includes the server-side check_dag and review_split checks. No local check_dag, review_split or preflight script was run. Final validation is repeated after recording this receipt; direct delivery is authorized by the worker brief, with the maintainer's independent review still to follow.
