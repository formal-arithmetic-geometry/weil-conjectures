# Worker report: lem-cbc-hypercover-localization-generation

Group Q126; stage 1; 2026-10-17. This is the first worker's split for independent second reading. Delivery is dry-run only.

## Files written

All delivered JSON files are in `dag/nodes/sec-smooth-purity/` in this sandbox.

- `lem-cbc-hypercover-localization-generation.json`: item, statement unchanged, split into nine proof steps.
- `lem-cbc-dense-hypercover-set.json`: new statement-only lemma, Mathlib no match.
- `lem-cbc-dg-presheaf-model-localizations.json`: new statement-only model-existence lemma, Mathlib no match.
- `lem-cbc-dold-kan-hypercover-quillen.json`: new statement-only localized adjunction lemma, Mathlib no match.
- `lem-cbc-simplicial-hypercover-fibration-test.json`: new statement-only lifting lemma, Mathlib no match.

`citations.json` contains a verbatim statement quotation for each of the 15 step/node pairs. Search results are recorded verbatim in the nodes, and the actual calls are logged in `searches.jsonl`. No unit file is changed: this item is not the unit's key statement.

## Attachments

None. I searched the item id, its blueprint tag and hypercover/localization terminology in `WeilConjectures/` in slopmaster2, and checked the exact upstream reference source. No project declaration states this theorem or any of the four new helper statements. In particular, the existing hypercover material is about geometric hypercovers and cohomology, not this unbounded arbitrary-site localization. There is no proposed attachment of a Mathlib declaration.

## Sources wanted

WANTED: Choudhury--Gallauer Alves de Souza, *Homotopy theory of dg sheaves*, https://arxiv.org/pdf/1511.02828, Corollary 3.1, Proposition 3.15, Facts 5.2 and 5.5, Theorem 5.7(1)-(2), Remark 5.8, Lemmas 5.12-5.13 and proof of Theorem 5.11, for the item and its model/adjunction helpers. I read the online primary paper; it is not archived under the named literature directory. No download was made. The item's proof is consequently marked agent-written.

WANTED: Dugger--Hollander--Isaksen, *Hypercovers and simplicial presheaves*, https://arxiv.org/pdf/math/0205027, Definition 6.1, Proposition 6.6, Lemma 6.4 and the projective-model paragraph of Theorem 6.2 in arXiv v2, pp. 16-19, for the dense-set and simplicial-fibration nodes. I read these online. The published numbering quoted by Choudhury--Gallauer is Proposition 6.7 and Lemma 6.5, respectively; the version difference is recorded in both node sources.

## Errors and choices

The imported item was unsplit. Its statement is correct against the paper and is kept verbatim. There is no statement dispute. I did not change its coefficient category, add boundedness or require a basis of covers, enough points, representable intersections, a terminal object or a subcanonical topology.

The paper's augmentation exactness fact is proved here directly by finite matching cones, with the local-lifting and exact-sheafification statements as its cited inputs. This keeps that whole clause in the item's argument. The proof does not use the parent local-object criterion `lem-cbc-hyperdescent-local-orthogonality`, which depends on the item and would create a cycle. It also does not assume that an arbitrary simplicial hypercover is projectively cofibrant.

I deliberately kept two levels separate: the existence of the cohomology-sheaf model structure, and its identification with localization at the chosen shifted hypercovers. The new model lemma states the former and existence/universal properties of arbitrary set localizations, but does not identify them. Steps 6-8 prove the latter by shifting and lifting paths. Neither this helper nor any other new node restates the item's generation conclusion.

## Unfinished work

No stage-1 mathematical part remains in the item. The four new lemmas are intentionally statement-only, as required by a one-level split. Their later splitting and Lean formalization are outside this assignment. Independent second reading and actual delivery remain assigned to the second worker.

## Not duplicates

The whole DAG was searched by id, source URL, hypercover density/refinement, model-localization and Dold--Kan terminology. Blueprint searches were made for `hypercover`, `dense hypercover`, `Dold`, `Dold Kan`, `Bousfield`, `localization`, `model`, `local projective`, `refinement`, and `hypercover fibration`; the resulting geometric/cohomological nodes do not state the four helpers. There are no new Stacks tags or shared-tag pairs.

- lem-cbc-dense-hypercover-set vs lem-cbc-hypercover-localization-generation: the former is a cardinal-bounded refinement theorem for all representable simplicial hypercovers, not the existence of linearized generators for cohomology-sheaf equivalences.
- lem-cbc-dense-hypercover-set vs lem-weil-pbc-finite-hypercover-map-extension: the latter extends finite geometric simplicial maps, not a uniform small dense refinement set on an arbitrary sieve site.
- lem-cbc-dense-hypercover-set vs thm-weil-pbc-hypercover-cohomology: the latter computes geometric cohomology after refinement; it does not assert this cardinal-bounded family.
- lem-cbc-dg-presheaf-model-localizations vs lem-cbc-hypercover-localization-generation: the former has no hypercovers in its statement and supplies two independent model structures, their factorizations and arbitrary-set mapping-space tests. The item must prove the two weak-equivalence classes coincide for its particular set.
- lem-cbc-dg-presheaf-model-localizations vs lem-coef-quillen-section-rectification: section rectification supplies projective enriched diagrams; it does not give the local cohomology-sheaf model or arbitrary set Bousfield model structures. The projective piece alone would be a special case; it is not the new content for which this helper is cited.
- lem-cbc-dg-presheaf-model-localizations vs lem-coef-simplicial-bousfield-model-structure: the existing theorem requires a simplicial model and cofibrations between cofibrants. The helper treats unbounded dg presheaves and arbitrary sets of complex maps, and independently asserts the cohomology-sheaf model. No simplicial tensor structure on unbounded complexes is silently assumed.
- lem-cbc-dg-presheaf-model-localizations vs lem-coef-sheaf-flat-model: the latter is a model on complexes of sheaves with flat cofibrations, not the local model on complexes of presheaves retaining projective presheaf cofibrations.
- lem-cbc-dold-kan-hypercover-quillen vs lem-cbc-presheaf-dg-function-complex: the latter computes mapping complexes and their Dold--Kan mapping spaces; it does not assert a right Quillen functor between the two localized model categories.
- lem-cbc-simplicial-hypercover-fibration-test vs lem-coef-simplicial-presheaf-localization-comparison: the existing node identifies a set-local model with a coherent local-object category, but says nothing about homotopy-sheaf equivalences being objectwise trivial fibrations between localized fibrants.

## Review by Q126

I read the source paragraphs named above with the item and each helper open. Choudhury--Gallauer use homological degrees; the split uses their homological degree n as cochain degree -n. Their small category carries an arbitrary Grothendieck topology. DHI explicitly develop their presheaf notion for general sites, rather than assuming the matching objects lie in the site. These match the item's covering-sieve, non-subcanonical, no-fibre-products formulation. Corollary 3.1 gives the projective model on all complexes. Theorem 5.7(1)-(2) and Remark 5.8 give the independent cohomology-sheaf model. The proof uses only that existence, not part (3)'s description of fibrants or Theorem 5.11's conclusion.

For the dense-set node I read DHI v2 Proposition 6.6's cardinal proof: start with covering sieves whose arrows form a set, extend truncated refinements degree by degree, and take a sufficiently large regular cardinal. Smallness controls the total set of representable summands. Its output is a genuine refinement of each hypercover over the same target, stronger than just choosing a family of tests. The new statement includes this refinement property, the regular-cardinal bound, and representatives up to isomorphism. It needs smallness but no points or finite-dimensionality. The zero-site case allows the empty family.

For the model node I read the projective existence and the separate localization-existence paragraphs. All three structures have the same presheaf category and the indicated projective cofibrations; only the weak equivalences change. Its arbitrary set localization is tested by homotopy function complexes from the original model. Its shift assertion applies only to shift-invariant sets. Its comparison assertion applies only when every set member is a cohomology-sheaf equivalence. These two hypotheses are checked in steps 4-6. I did not import the theorem identifying cohomological equivalences with hypercover localization into this helper.

For the Dold--Kan node I read Proposition 3.15 and Lemma 5.12 and the interval calculation in Lemma 5.13. Smart truncation at cochain zero has cycles in degree zero; using brutal truncation would give the wrong right adjoint and wrong pi_0. The right adjoint's homotopy groups are H^{-m}, and translations account for all slice-site basepoints. The localized Quillen assertion applies to any small H, so its proof is not a disguised dense-hypercover generation theorem. The interval has differential a maps to (-a,a), precisely the boundary used later. Normalization and the alternating complex need not be equal; the source compares them by an objectwise quasi-isomorphism. The helper asserts the resulting localized adjunction, not a false equality of those complexes.

For the simplicial-fibration node I read DHI's boundary-lifting lemma and the separate projective-model paragraph. It requires a dense set, a localized fibration, and both objects localized fibrant. All three are necessary and are present in step 6. Derived mapping spaces are projective, including replacements of noncofibrant hypercovers. The helper's conclusion is actual lifting against representable boundaries, rather than only a homotopy-category equality.

Step 1 uses the model node's combinatorial projective existence and the exact hypothesis/conclusion paragraph of `lem-coef-combinatorial-localization-presentability`. The latter gives presentability of the coherent localization, not merely existence of an ordinary derived category. Both factorization systems and local presentability are supplied by the former.

Step 2 uses the dense-set node's refinement conclusion. Taking integer shifts of a set stays a set. The conclusion is a family in the same working universe, with varying targets, as the target statement requires.

Step 3 uses the full epimorphism/local-section-lifting equivalence of `lem-cbc-presheaf-sheafification-epi-local-lifts`; I read its statement, including that it requires no fibre products or subcanonical hypothesis. I checked the cone induction at a vertex and at an edge. In degree zero its boundary is the original vertex minus the chosen vertex over the target. In higher degrees the specified cone faces satisfy the matching identities by the lower induction. Finite covering-sieve intersections and transitivity suffice for the finitely many fillers for any one chain. There is no infinite intersection of covers. A correction during drafting was to retain the original finite labelled face diagram throughout refinement: two labels becoming equal after restriction must not erase the formal chain cancellations already known before refinement. The written step addresses this explicitly.

Step 4 uses `lem-cbc-sieve-module-sheafification` for its exact left adjoint b and the sheafification unit, not a definition node used as a theorem. Local-zero homology gives zero sheafification by the adjunction argument written in the step: every map to a sheaf is zero, and applying this with bE makes its identity zero. This avoids silently assuming a plus-construction formula or a pointwise criterion. Exactness then commutes with kernels, images and quotients, which gives the required homology sheaves. The argument handles the augmentation cokernel as well as reduced degree-zero and positive homological cycles, so every clause of the augmentation assertion is covered.

Step 5 uses the model node's existence, local-fibrant mapping-space tests and W_B subset W_J clause, whose hypothesis follows from step 4. `lem-coef-simplicial-presheaf-localization-comparison` is read for the projective set-localization and its derived mapping-space convention, not for a cohomology-sheaf theorem that it does not state. The three off-unit citations in this split are declared generic tools in `split_report.tool_uses`.

Step 6 uses the model node's shift autoequivalences, the Dold--Kan node's right Quillen functor and preservation of cohomology-sheaf equivalences, and the simplicial-fibration node's actual boundary lifting. Every integer shift is present in B. R of both shifted endpoints is therefore localized fibrant, and R of the shifted map is a localized fibration. Local equivalence is not inferred from an arbitrary right Quillen functor; it is the separate preservation assertion of the Dold--Kan node.

Step 7 uses the explicit interval of the Dold--Kan node and the projective fibration clause of the model node. I checked that placing z in cochain degree zero requires X[r], not X[-r]. The shift sign is harmless by multiplying the primitive by a unit sign. The lifted interval lies in the kernel because its image interval is zero, so this proves kernel acyclicity, not just acyclicity of X. The map is already degreewise surjective by the right Quillen identity back to the projective model. The two element arguments at the end prove the quasi-isomorphism claim without an uncited long-exact-sequence theorem.

Step 8 expands the model-comparison argument rather than citing a theorem that already asserts generation. The model node supplies functorial fibrant replacement and the trivial-cofibration/fibration factorization. The intermediate object is fibrant by composition of its fibration with the terminal map of the fibrant target. Both replacement arrows and the trivial cofibration are in W_J by step 5. Thus the fibration satisfies exactly the hypotheses used in steps 6-7. Two-out-of-three proves the result for the original arbitrary map; no cofibrancy or boundedness is introduced.

Step 9 uses the model node's identification of the original homotopy function complexes with coherent derived mapping spaces, and `lem-coef-infinity-small-localization-saturation` for the equivalence between the local-object mapping test and the precise closure in the question. I read that node's statement: it explicitly includes pushouts and small colimits in the arrow infinity category computed on both ends, not just coproducts or transfinite composites. Its presentability and smallness hypotheses were established in steps 1-2. The augmentation clause is inherited from the explicit argument in steps 3-4, not from assuming membership in the selected dense family.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the actual files. New nodes have statements only and complete inline notions or definition dependencies; no proof sketch is placed inside their statements. Before creating them I searched the DAG, blueprint and project Lean source. Each new node has two distinct semantic phrasings, Loogle, source grep and LeanSearch, all actually called through msearch; all services returned results. The Mathlib hits were read: zero/one hypercovers and dense subsites are weaker than full dense hypercovers; Bousfield.lean uses ordinary Hom-set orthogonality; the available cochain model is bounded-below injective; the additive Dold--Kan equivalence does not prove localized Quillen compatibility; ordinary Kan horn lifting does not prove the site's local boundary-lifting theorem. The node records preserve the actual queries and outputs, with the corresponding no-match explanations.

As edge tests, the zero ring makes all complex and Dold--Kan assertions trivial. The empty site makes both presheaf model categories terminal. For the topology with only maximal covering sieves, local equivalence is objectwise equivalence, and the coning argument becomes sectionwise. If an object has an empty covering sieve, the local lift requirements over that cover are vacuous and the associated sheaf criterion still works; the proof does not demand a vertex over that object globally. The identity hypercover gives its usual contractible augmented alternating complex. The interval argument in every integer degree, including arbitrarily positive and negative degrees, confirms that the proof does not truncate the unbounded theorem. No correction to the imported statement was needed.

## Second reading by Q126

- Item statement: checked against Choudhury--Gallauer Facts 5.2, 5.5, Theorems 5.7 and 5.11; all hypotheses (small site, arbitrary Grothendieck topology, unbounded complexes, sheafified cohomology, and shifted augmentations) and all conclusions agree.
- Step 1: checked the cited projective-model and combinatorial-presentability statements; they supply objectwise weak equivalences, localization, and presentability exactly as used.
- Step 2: checked the dense-hypercover statement and the set argument; varying targets and all integer shifts are covered without extra site hypotheses.
- Step 3: checked the local-lifting criterion and the written finite labelled cone induction; the matching sections, finite refinements, and augmentation boundary calculation are explicitly accounted for.
- Step 4: checked exact module sheafification, its adjunction, and the local-zero argument; the conclusion covers every augmented homology degree.
- Step 5: checked both model-localization citations and the inclusion of augmentation maps in the cohomology-sheaf weak equivalences; no cofibrancy assumption is used.
- Step 6: checked shift invariance, the localized Dold--Kan right Quillen assertion, and dense-set boundary lifting; fibrancy and local-equivalence hypotheses are all present.
- Step 7: checked the interval endpoint identification and the kernel-contraction argument in every integer degree; surjectivity and the acyclic-kernel quasi-isomorphism argument are written out.
- Step 8: checked functorial fibrant replacement, factorization, fibrancy of the intermediate object, and two-out-of-three; the argument applies to arbitrary maps.
- Step 9: checked the coherent mapping-space identification and strong-saturation theorem; closure operations and arrow-colimit convention match the item.
- `lem-cbc-dense-hypercover-set`: checked self-contained site, matching, density, cardinal, and representative clauses against DHI Definition 6.1 and Proposition 6.6; no duplicate or Mathlib exact match.
- `lem-cbc-dg-presheaf-model-localizations`: checked all projective, cohomology-sheaf, Bousfield-localization, shift, and mapping-space clauses against Choudhury--Gallauer; no duplicate or Mathlib exact match.
- `lem-cbc-dold-kan-hypercover-quillen`: checked smart truncation, normalization/alternating comparison, localized adjunction, interval, and shift clauses against Proposition 3.15 and Lemmas 5.12--5.13; no duplicate or Mathlib exact match.
- `lem-cbc-simplicial-hypercover-fibration-test`: checked local weak-equivalence, fibrancy, dense localization, and representable boundary-lifting clauses against DHI Lemma 6.4 and Theorem 6.2; no duplicate or Mathlib exact match.
- Changes: no mathematical or node-statement repair was required; appended this second-reading record and retained the worker's source, search, and citation records after verifying all 15 citation quotes are verbatim substrings of their cited statements.
