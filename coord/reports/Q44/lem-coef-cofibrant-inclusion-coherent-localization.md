# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-cofibrant-inclusion-coherent-localization.json`: statement, split into five steps; no exact Mathlib match. No new nodes and no Mathlib leaves.
- `citations.json`: seven step/node entries with verbatim excerpts of the cited statements.

The sandbox initially contained only dispatcher markers. There was no previous proof, report, or search log to recover. The item statement, original citations/searches, created record, and blueprint ancestry are retained. No unit realization changes are appropriate: this is a descendant supporting the coefficient-adjunction infrastructure, not the key node of the biduality unit.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the item tag, cofibrant and Cofibrant; no declaration was returned. The same conceptual search in the reference master project returned none. Mathlib's ordinary localization declarations are not project attachments and do not establish this item's coherent conclusion.

## WANTED

WANTED: Lurie, Higher Algebra, Remark 1.3.4.16, printed p. 116; Construction 4.1.7.1 and Proposition 4.1.7.2, printed pp. 485-486, for lem-coef-cofibrant-inclusion-coherent-localization. The PDF is not archived locally. I read these places online at https://www.math.harvard.edu/~lurie/papers/HA.pdf without downloading or changing literature/. Remark 1.3.4.16 asserts equivalence of the cofibrant/all-object presentations under functorial factorization but leaves the replacement argument implicit. The proof is therefore marked agent: it explicitly supplies that argument using existing, separately stated tools.

## Audit and changes

The imported item was statement-only. Its assertion is correct as stated; there is no STATEMENT-DISPUTED and no change to its statement. The proof now constructs the relative replacement functor, types the restricted replacement transformation in the full cofibrant subcategory, and descends both transformations in full coherent functor categories. The distinction between an ordinary localization and a coherent localization is essential: the ordinary Mathlib results are recorded as candidates ruled out, not promoted to leaves.

I read the chapter and unit records, SETUP's three levels, the main-20261015 ancestor proof paragraph 2, and the stage-1/dag-sync rules. The inherited ancestor concerns the R Hom/R lim coefficient-adjunction calculation. This small replacement argument remains within its supporting model/localization infrastructure; no chapter or unit route is changed. The off-unit componentwise-equivalence theorem is declared in split_report.tool_uses as a generic quasicategory tool. The existing model-adjunction node is used only for its explicit first-paragraph definitions, never to invoke the derived adjunction or to assume the present conclusion.

## Searches and duplicate audit

The entire imported blueprint was searched with `tools/blueprint_refs.py search cofibrant` (zero matches) and `search pointwise` (13 unrelated definition nodes); ancestor confirms prop-coef-integral-exceptional-adjoint. Whole-DAG textual searches for pointwise equivalences, natural transformations and coherent localization found the existing system-localization and functor-cone nodes. Their statements supply exactly the tools needed, so I created no replacement lemmas. No duplicate-pair section is needed because there are no new nodes.

Ran logged msearch searches with LeanFinder in two phrasings, LeanSearch, Loogle, and Mathlib grep. Read all hits. Read Mathlib/AlgebraicTopology/ModelCategory/CofibrantObjectHomotopy.lean:127-245 and 285-340, DerivabilityStructureCofibrant.lean:25-65, and the ordinary-category signatures of Localization.Predicate.functorEquivalence. The first file constructs resolutions and proves inclusion is an ordinary localized equivalence; it explicitly makes its resolution functorial only in the homotopy quotient. The derivability file proves an ordinary left derivability structure. Localization.Predicate takes ordinary Category inputs. None states an equivalence of arbitrary coherent functor categories. No unavailable service was recorded as a negative result. Existing inherited searches are retained separately from this run's logged searches.

## Review by Q44

I read Higher Algebra Remark 1.3.4.16 online: the needed assumption is functorial factorization, not simplicial enrichment or combinatoriality. The item already includes it via the model-category conventions. The stronger conclusion about transformations follows from the full universal property explicitly stated in lem-coef-system-localization-universal, whose statement I opened in full. I also read the full statement of lem-cbc-enhanced-functor-cone-calculus, including its arbitrary-small-simplicial-shape and componentwise-equivalence clauses, and the first-paragraph model definitions in lem-coef-model-infinity-derived-adjunction. No new node requires a separate source check.

Step 1 uses the named model conventions only: the factorization of the initial arrow provides a cofibrant middle object and a natural trivial fibration. Functoriality supplies identities, composition, and the naturality equation; this is an elementary unpacking of the hypothesis, not an existence assertion smuggled in from the derived-adjunction theorem.

Step 2 uses exactly the two-out-of-three axiom explicitly written in that model node. In epsilon_Y Qf = f epsilon_X, the right side and epsilon_Y are weak equivalences, so Qf is one. For the restricted epsilon, I checked BOTH endpoints are cofibrant, not that cofibrant objects are closed under arbitrary weak equivalence. Fullness then supplies its naturality inside the subcategory. These are elementary arguments, not separate new lemmas.

Step 3 uses the model conventions to check the systems and uses the actual full Fun_W universal property of the system-localization node to descend qj and q_c Q. The relevant source nerves and target localizations all fit in the expressly enlarged universe. Each functor being descended inverts its required class by Step 2. The composite comparisons follow by substitution of the two restriction comparisons; no Quillen derived-adjunction clause is used.

Step 4 cites both existing tools. The functor-cone statement really says a coherent transformation is an equivalence iff its components are equivalences. The system-localization statement really gives an equivalence onto a FULL functor subcategory, not just its core or a bijection of homotopy classes. I checked each endpoint inverts the specified weak equivalences, and the inverses and their homotopies stay in that full subcategory. Transport under the functor-category equivalence gives both inverse comparisons with the correct sources and targets. This is where coherent descent is proved; it has not been moved to a restatement node.

Step 5 uses the arbitrary-shape component criterion from the functor-cone node. Postcomposition and whiskering are the defining operations on coherent functor categories. I wrote the naturality on K times Delta^1 and its higher versions on K times Delta^n, so the conclusion includes transformations. It does not infer coherent naturality from an equivalence of ordinary homotopy categories.

For small cases I checked a terminal model category (everything reduces to the identity), the case all objects are cofibrant (Q still need not be identity, but epsilon restricts correctly), a non-cofibrant object (the unrestricted comparison lives in M, not M^c), and a weak equivalence between arbitrary objects (the proof does not require cofibrancy of its endpoints). For diagram shapes I checked empty K and K=Delta^1; the empty case has no component conditions, and the arrow case includes a coherent naturality square. No fibrancy, properness, enrichment, or smallness before universe enlargement is used.

Against delivery-errors B-E: statements and metadata are retained, no unsplit new nodes or duplicated clauses were created, every non-elementary input has its own existing cited statement, and the full dependency closure of each of the three cited nodes was searched for a path back to the item (none). All five proof steps are below 1100 characters, so none crosses the long-step threshold or hides a separately quantified comparison lemma. No SGA source is cited. I corrected no mathematical statement; the repair is the missing proof and its explicit coherent and typing checks.

## Unfinished work

None in the one-level split. Existing cited nodes keep their own independent proof obligations. Server dry-run and delivery results are recorded below when available.
