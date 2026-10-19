# N3: lem-coef-adjunction-free-simplicial-resolution

## Files written

- `dag/nodes/sec-six-functors/lem-coef-adjunction-free-simplicial-resolution.json`: assigned statement unchanged; three-step specialization of an existing general theorem; no Mathlib match.
- `citations.json`: verbatim statement excerpts for all four step/node pairs.
- `searches.jsonl`: additional executed searches, with the original log retained.

Zero new nodes; zero Mathlib leaves. The two uncommitted helper proposals from the earlier sandbox attempt were removed after searching the current DAG.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its blueprint tag, free/simplicial resolutions, comonads, monadicity, bar constructions and extra degeneracies found no project declaration stating the item. No compiler was run; upstream master was not treated as finished evidence.

## WANTED:

WANTED: an archived copy of Lurie, Higher Algebra (2017), Theorem 4.7.3.5(c), Proposition 4.7.3.14 and Remark 4.7.3.15, for this item and the existing `lem-coef-infinity-monadic-bar`. I read the author's online PDF at https://people.math.harvard.edu/~lurie/papers/HA.pdf, printed pp.685,688-689; it is not archived under this repository's literature/. No literature was downloaded. The proof origin remains agent because the archive is absent and this proof specializes an existing DAG interface.

## Problems found and corrections

The earlier attempt proposed two helpers without noticing that the current existing `lem-coef-infinity-monadic-bar` already provides the entire coherent augmented bar and its realization. Its statement uses exactly the same coherent-diagram and cocone conventions, assumes existence and preservation of realizations and conservativity, and specifies the degree formula. I reused that statement instead of adding overlapping nodes. Reusing this already existing stronger theorem is a specialization, rather than moving this item's content into a newly created node. Its own unsplit proof remains work for its owner.

The earlier report claimed that the blueprint paragraph named free simplicial resolutions; it does not. The main-20261015 ancestor's paragraph beginning “For K” displays the finite-level derived mapping-complex comparison. The free-resolution item is a foundation below that comparison through its existing ancestry, not a quotation from the paragraph. I corrected the provenance wording while retaining the ancestor and via list. The inherited unit is `sk-prop-sf-biduality-general`, as is that of the reused theorem; I changed no unit or chapter binding. This is not the unit's key node, so no unit realization record is part of this delivery.

No false statement or missing hypothesis was found. The item has no blueprint_update and its statement was retained byte for byte as a JSON string. The stale unused cone-calculus tool declaration was removed from the sandbox split_report: the existing bar node already states the augmentation's colimit property with the required definition.

## Unfinished work

The split is complete; acceptance is determined by the required dry-run command below. No Lean was written or compiled. The existing general bar node is intentionally left untouched for its own worker; the second reader must review this specialization and deliver it.

## Review by N3

I read delivery-errors B–E whole, the stage-1 brief and stage document, SETUP's three levels, GOAL and dag-sync, the chapter record `sec-six-functors` and unit record `sk-prop-sf-biduality-general`, and the current main-20261015 ancestor proof. I opened the complete statements of `lem-coef-infinity-monadic-bar`, `def-cbc-enhanced-diagrams-cones`, and `def-coef-complete-algebroid`. The last two supply the item's existing notions and size conventions. The bar node uses simplicial maps into quasicategories and the same coherent comma-cocone definition of colimit; its explicit hypotheses impose no presentability, completeness, monadicity assumption, or ordinary-category restriction. Its Barr–Beck equivalence is a conclusion, not an extra hypothesis.

For the source check, I read Higher Algebra Theorem 4.7.3.5(c) on printed p.685, Lemma 4.7.3.13 and its proof on pp.688-689, and Proposition 4.7.3.14 with Remark 4.7.3.15 on p.689. The proposition gives free terms and a colimiting split resolution when the right adjoint is conservative and preserves the appropriate split realizations; the item's all-realizations hypotheses imply these conditions. There is no Stacks tag for this infinity-categorical theorem. No SGA source was used.

Step 1 cites the general bar node's hypothesis sentence and the cocone definition. The substitution C=B, D=X, U=R respects the left/right orientation. Reflection of equivalences is exactly its definition of conservative, and the item's all-small-realizations assumption covers the small simplex category. This is elementary hypothesis matching, not a theorem about creating colimits.

Step 2 cites the bar node's complete augmented-bar conclusion, including its explicit coherence assertion and the sentence asserting realization at Z. Thus it gets the augmented coherent diagram and its colimitingness from a theorem statement, not from a proof, a mere definition, or an unrecorded split-realization lemma. This is the only non-elementary invocation. The theorem's stated coherent cocone conventions give precisely the cocone in the item's conclusion; no transport of a selected colimit or separate cone-calculus theorem is required.

Step 3 cites the same degree formula and takes b_0=Rx, b_(n+1)=RL(b_n). R maps X to B and L maps B to X, so every b_n has the correct type. Substituting into the formula proves the degreewise equivalence in one line. The item's last sentence asks for no simplicial diagram of the b_n, and none is inferred from degreewise freeness. This is elementary extraction of existential witnesses. All step uses have verbatim quotes in citations.json, and proof_deps is their exact union. A dependency traversal of the reused theorem's current statement/proof closure found five nodes and no path back to this item, so reuse does not introduce a cycle.

For B1–B10 and C5, no new node survives. Before retaining any helper I searched the whole DAG for comonad, extra-degeneracy, split-augmentation, bar-construction and the HA theorem numbers. `tools/blueprint_refs.py ancestor` confirmed the recorded ancestor; its whole-blueprint searches for “bar construction”, “comonad”, “simplicial resolution”, “extra degeneracy”, “split augmented” and “split augmentation” returned no blueprint statement matches. The DAG search found the already existing general bar node; I read it rather than accepting an id match. No same_as blueprint alias was found. I removed the two sandbox proposals and their stale citations rather than misclassifying them as independent lemmas.

I reran LeanFinder with two phrasings, Loogle, LeanSearch and Mathlib grep for the item, recording each actual query and result. I read `CategoryTheory/Monad/Adjunction.lean:67`, `AlgebraicTopology/ExtraDegeneracy.lean:72`, `AlgebraicTopology/SimplicialObject/Split.lean:233`, and the quasicategory strict-bicategory introduction. The first two are ordinary-category interfaces; the split-object colimit is a degreewise coproduct decomposition, not an augmented geometric realization. The search hits therefore provide no exact theorem or one-line Mathlib specialization. No unavailable service was recorded as a negative result, and no unexecuted query was added.

For E1–E6, I checked that no realizations in B beyond the images preserved by R are assumed, that no unital or coherence data is manufactured from a mere homotopy-category adjunction, and that the bar formula gives b_0=Rx and P_0=LRx. With the identity adjunction the resolution is constant; with X empty the assertion is vacuous. An adjunction with a nonconservative terminal right adjoint does not satisfy step 1, so it cannot yield an erroneous free-generation assertion here. There are no new statements to test. The final statement, its hypotheses and its coefficient-free ambient categories were not changed.

## Not duplicates

No new node remains. The removed `lem-coef-infinity-adjunction-bar-construction` overlapped the coherent construction and extra-degeneracy clauses of existing `lem-coef-infinity-monadic-bar`; the removed `lem-coef-infinity-split-augmentation-realization` was unnecessary because that existing node already states the bar augmentation is colimiting. This item is a weaker consequence of that existing theorem, so its proof cites it directly.

## Validation

Required command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py N3 lem-coef-adjunction-free-simplicial-resolution --no-push`. Its server preflight runs check_dag and review_split. The worker reports READY only after that command prints OK. No delivery is pushed by this worker.


## Second reading by N3

Source and statement: I independently opened the author's 2017 Higher Algebra PDF, Theorem 4.7.3.5(c), printed p.685, Lemma 4.7.3.13 and Proposition 4.7.3.14 with Remark 4.7.3.15, printed pp.688–689. The theorem asks only for right-adjoint-split realizations; the item's all-realizations hypothesis implies that requirement. The proposition supplies a colimiting simplicial diagram with terms in the left adjoint's essential image. The item retains that consequence and does not assert a simplicial lift of those terms. Its statement is byte-for-byte identical to the current shared node. No Stacks tag states this result, and no SGA source was used. I also read GOAL.md, dag-sync.md, the stage-1 contract, chapter/unit records and the current main-20261015 ancestor proof; its paragraph beginning “For K” is application provenance, not the source of the general theorem.

- Step 1 — PASS against the full statement of `lem-coef-infinity-monadic-bar` and the cocone paragraph of `def-cbc-enhanced-diagrams-cones`: C=B, D=X, U=R have the correct types and adjunction orientation; existence, preservation and reflection are exactly the assumptions. Matching hypotheses and the small simplex indexing category are elementary.
- Step 2 — PASS against the bar node's augmented-bar conclusion and opening coherent-cocone convention: it supplies the coherent simplicial object, augmentation and realization at x. These are in its statement; no construction from its proof or uncited colimit-reflection theorem is used. This is the sole non-elementary invocation.
- Step 3 — PASS against the bar node's degree formula: b_0=Rx, b_1=RLRx and b_n=(RL)^nRx lie in B, so P_n is equivalent to L(b_n). Iterating the endofunctor and extracting these witnesses are elementary; no structure on the b_n is inferred.
- New nodes — NONE. The existing bar theorem already states both removed helpers' content. It is in the same inherited unit as the item, so no additional cross-unit tool authorization is needed. A fresh read-only traversal of the item's statement/proof dependency closure found 11 nodes and no cycle. Each of the four citation quotes is a verbatim substring of its cited statement, and proof_deps is the union of the step uses.

Edge cases: for the identity adjunction the bar diagram is constant; in a category of vector spaces over a field with the identity adjunction, x=0 gives only zero terms. If X is empty the assertion is vacuous (and existence of L forces B empty). Degree zero gives P_0=LRx and degree one gives P_1=LRLRx, with no negative degree required. No presentability or existence of unrelated realizations in B enters the proof.

Independent searches: I ran msearch.py with a new LeanFinder phrasing about iterating the counit, Loogle for `CategoryTheory.Adjunction.toComonad`, a grep for `barResolution|ExtraDegeneracy|Barr.Beck|geometricRealization` under AlgebraicTopology/Quasicategory, and a new LeanSearch phrasing using quasicategories and simplicial colimits. All four ran successfully and their unmodified results were appended to searches.jsonl. LeanFinder returned ordinary localization resolutions; LeanSearch returned ordinary adjunction/colimit interfaces. I read the returned toComonad construction in Monad/Adjunction.lean:67–77, ExtraDegeneracy.lean:66–84, and SimplicialObject/Split.lean:212–233: these require an ordinary Category and the last colimit is a coproduct within a fixed degree. None states this coherent infinity-category result. The quasicategory grep returned zero hits. A direct project-source and upstream-name search returned no attachment candidate for this item. No compiler or build tool was run.

Changes: appended this independent reading and fresh executed search evidence; retained the mathematical statement, three proof steps, citations and zero-new-node split. The creation stamp correctly records the earlier item that created this existing node; it is unchanged. No statement dispute was found.

Validation: the required `deliver.py N3 lem-coef-adjunction-free-simplicial-resolution --no-push` completed successfully: `OK (not pushed) deliver/N3/lem-coef-adjunction-free-simplicial-resolution at f5cc6f38cf: preflight passed`. The tool ran the server preflight; no prohibited local check, compiler or build command was invoked. The authorized push follows.
