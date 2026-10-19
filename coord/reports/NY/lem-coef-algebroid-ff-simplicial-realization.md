# Stage-1 worker report: lem-coef-algebroid-ff-simplicial-realization

## Files written

- `dag/nodes/sec-six-functors/lem-coef-algebroid-ff-simplicial-realization.json`: existing statement node, now split into seven steps. Mathlib verdict: no match. The statement, statement dependencies, historical ancestry, chapter, unit and creation record are preserved. Its previously empty proof is replaced by the explicit Segal-presheaf argument.
- `citations.json`: 19 per-step quotations copied verbatim from the statements cited by the proof.
- `searches.jsonl`: the genuine msearch log for two LeanFinder phrasings, Loogle, LeanSearch, and two source greps. No search was invented. The six current searches were added to the item's existing search records with their actual outputs and verdicts.
- `report.md`: this report. No new nodes or Mathlib leaves. No unit record is changed because this item is not a unit key statement.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the exact blueprint tag and by algebroid, Segal-presheaf, simplicial-realization and full-faithfulness concepts found no project declaration stating this item. The exact master checkout was searched as reference material and yielded no attachment either. No source was edited, and no compiler or Lake command was run.

## Wanted literature

WANTED: Gepner–Haugseng, *Enriched infinity-categories via nonsymmetric infinity-operads*, arXiv:1312.3178v4, Section 4.5 and the cartesian-square/Segal-presheaf part of the proof of Theorem 5.6.2, for lem-coef-algebroid-ff-simplicial-realization.

WANTED: Haugseng, *On the tensor product of enriched infinity-categories*, arXiv:2311.13362v1, Definition 4.3, Proposition 5.1, Proposition 8.2, Observation 8.4 and Proposition 8.5 read with the existing DAG's fiberwise correction, for lem-coef-algebroid-ff-simplicial-realization.

WANTED: Lurie, *Higher Topos Theory*, Theorem 6.1.3.9(4) and Proposition 6.1.3.10, for lem-coef-algebroid-ff-simplicial-realization.

These were read online at https://arxiv.org/html/1312.3178v4, https://arxiv.org/html/2311.13362v1 and https://www.math.ias.edu/~lurie/papers/HTT.pdf. They were not downloaded into the shared repository. The proof is marked agent-origin because it expands the source's special completion diagram to the arbitrary diagram of this item and the sources are not archived in literature/. No Stacks tag states this infinity-categorical result; no Stacks tag has been substituted for an unrelated theorem. No prohibited SGA source was used.

## Problems found and repaired

The imported item was a statement-only support lemma. GH Theorem 5.6.2 treats a particular completion diagram, so its theorem cannot simply be cited as the arbitrary-diagram conclusion here. I wrote out the argument from its cartesian-square paragraphs: derive the squares from full faithfulness, realize them, check Segal after the endpoint cover, then check locality of the mapping presheaves and the colimit universal property. All of these remain on the item's existing proof route.

I also checked a possible localization pitfall. The uncorrected wording of Haugseng Proposition 8.5 tests the total edge presheaf. The already-existing `lem-coef-algebroid-segal-localization-model` instead states the correct criterion at fixed endpoints. Step 5 uses only that fiberwise criterion. It does not apply coefficient locality to the total space of edges, and it does not need the free-edge calculation hidden in that model's own proof. No other node was edited.

The main ancestor's current proof paragraph 2 is the finite-coefficient mapping-complex adjunction before the derived inverse limit. This item is one level of its recorded enrichment/completion support chain; the unit binding is retained. The ancestor was read in the current main-20261015 snapshot. No claim about general Verdier biduality or its historical bibliography is used in this split.

## Unfinished work

None in this one-level split. The existing nonsplit model and geometric-descent nodes remain tasks of their own. This delivery introduces no new support obligations. The second reader must review and deliver the accepted sandbox; this worker does not push.

## Not duplicates

No new nodes were created. I searched the entire DAG and blueprint for algebroids, Segal presheaves, geometric realization, full faithfulness and cartesian descent; the blueprint search found no alternate statement of this item. Existing Segal-model, definition and space-descent nodes were reused instead of creating their specializations. The model and descent dependency closures were checked and do not reach this item, so their use does not close a cycle.

## Review by NY

I read delivery-errors B–E in full and compared this split with those cases. For the item I read GH Section 4.5, including the mapping-object interpretation of the Segal model, and the whole relevant part of Theorem 5.6.2 through its full-faithfulness conclusion. I read Haugseng Definition 4.3 and Section 8 through Proposition 8.5/Observations 8.6–8.7, comparing the latter with the already-corrected DAG statements, and HTT Theorem 6.1.3.9(4) with the infinity-topos hypothesis in Proposition 6.1.3.10. I opened and read the statements of all five cited nodes: the algebroid definition, the Segal-presheaf definition, the model theorem, geometric descent of spaces, and the enhanced-cone definition. There are no new nodes requiring additional sources.

For step 1, the model theorem explicitly supplies a small monoidal presentation of any presentably monoidal coefficient category, the natural equivalences of algebroids with the stated full subcategories, and the endpoint mapping-presheaf identification. The definition supplies the universe and presentably-monoidal conventions. The given hypothesis is precisely presentably monoidal, so no stronger symmetry or compact-generation assumption is introduced. I use only the small category and small set that this existing statement provides.

For step 2, the Segal definition gives the product of the edge fibers over a fixed tuple; the model theorem identifies each edge fiber with the corresponding coefficient mapping object. The algebroid definition says full faithfulness is equivalence of those objects. Finite products of equivalences are elementary here. The geometric-descent node's final fiber criterion then proves that the actual naturality square is cartesian, using the identity cover of the source endpoint space. This uses the statement of each cited node, not any construction buried in its proof. In degree zero the endpoint square is an identity square.

For step 3, pointwise small presheaf colimits are an explicit clause of the model theorem. The space-descent statement explicitly gives both finite-product compatibility and cartesian cocone squares for a transformation cartesian on every indexing arrow. Step 2 established exactly that hypothesis. The index is the small simplex category, not a large category. I do not claim realization preserves arbitrary finite limits.

For step 4, the displayed pulled-back Segal target is obtained by rearranging its finite fiber products and applying the edge instance of the cartesian square. The degree-zero Segal map is an equivalence by the definition. The space-descent node says that degree zero covers the realization on components and supplies the fiberwise detection criterion. Coordinatewise lifts show the finite power of that cover is still a cover. Thus the criterion applies to the comparison over the full endpoint space. This is a proof of the Segal condition, not a new lemma restating that clause.

For step 5, taking the degree-one fiber of step 3 gives an equivalence natural in every label, so it gives an equivalence of entire mapping presheaves. The degree-zero endpoint cover reaches every pair up to paths. Since fibers over path-connected points are equivalent, the mapping presheaf there is equivalent to one of the original local mapping presheaves. Locality is invariant under that equivalence directly from its definition using Map(psi,-) to Map(phi,-). The model statement explicitly says that local endpoint mapping presheaves characterize its localized subcategory. No essential surjectivity of the structure maps is assumed.

For step 6, I wrote out why the ambient colimit remains a colimit in the full subcategory once its apex belongs to it: the cocone subcategory is full, and the same initial object remains initial. This is two lines from the full-subcategory and cocone definitions, so it is marked elementary, rather than turned into another node. For the model equivalence I also wrote out the cocone-level argument: apply the coherent inverse functors and their inverse homotopies to obtain equivalences of cocone categories, which preserve the initial object. This avoids hiding a compatibility claim behind the word transfer.

For step 7, the model statement identifies object spaces and mapping objects naturally on canonical maps, so the result of evaluating the colimit presheaf at the vertex is the required equivalence compatible with every cocone map. The mapping equivalence of step 5 is the actual cocone map. Both presheaves are local, and fullness supplies its inverse in the local subcategory. The conclusion of full faithfulness is exactly the algebroid definition. This last step is elementary reading-off of the proved equivalences, not an unsupported proof of the whole item.

I tested the empty-object case: if X_0 is empty, each X_n is empty because there are face maps to degree zero; every labelled presheaf value maps to an empty endpoint power. The realization is empty and the mapping assertions are vacuous. I checked constant diagrams and the one-object case: constant diagrams return the same algebroid, while constant one-object mapping equivalences realize to equivalences. I also checked the nonconstant fully faithful diagram whose object labels form a simplicial space and whose mapping objects are all the tensor unit; duplicate objects and nontrivial paths are retained in the realized object space. The proof never identifies an endpoint cover with an equivalence, and it retains homotopy fibers, so these cases introduce no hidden discreteness, completeness or nonemptiness hypothesis.

For B, there are no new-node form or same-tag questions; all files are valid TeX-in-JSON and the searches are actual logged searches. For C, each of the 19 uses has a verbatim statement quote, every non-elementary input is one of the five existing cited nodes, and no cited closure reaches this item. For D, the seven steps carry the proof themselves and create no restatement node. For E, all covers, indices, coefficient categories, mapping objects and cocone maps were checked with their actual hypotheses. No statement dispute was found and no statement was changed.

Mathlib searches returned ordinary `createsColimitOfFullyFaithfulOfLift'`/`OfIso'`, the ordinary nerve fully-faithfulness theorem, and strict Segal statements. I read `CategoryTheory/Limits/Creates.lean:431–460`, `CategoryTheory/Enriched/Basic.lean:47–72`, `AlgebraicTopology/SimplicialSet/NerveAdjunction.lean:395–407`, and the strict Segal source and declarations at `StrictSegal.lean:525–537`. These concern ordinary categories or strict simplicial sets, not the coherent infinity-algebroid construction. The second semantic phrasing found strict Segal nerve statements and still no applicable result. The item is not a Mathlib leaf.

## Second reading by NY

Item statement: checked the hypotheses and conclusion against Gepner–Haugseng Theorem 5.6.2, Theorem 4.5.3, Haugseng §8, and HTT 6.1.3.9–6.1.3.10; verdict: faithful arbitrary fully faithful simplicial generalization, with no essential-surjectivity assumption.

Step 1: checked the presentation, natural model equivalence, object-space and mapping-presheaf clauses against `lem-coef-algebroid-segal-localization-model` and the definition nodes; verdict: all uses are stated and the smallness convention is explicit.

Step 2: checked the endpoint square, labelled Segal fibers, finite products, and fiberwise comparison against the model, complete-algebroid definition, and geometric-descent statement; verdict: full faithfulness gives each fiber equivalence, including the degree-zero case.

Step 3: checked pointwise presheaf colimits, cartesian transformation hypothesis, finite-product comparison, and displayed pullback against the model and geometric-descent statements; verdict: no illicit claim that arbitrary pullbacks commute with realization.

Step 4: checked the Segal map after the degree-zero endpoint cover, coordinatewise product cover, and fiberwise detection against the Segal definition and geometric-descent statement; verdict: the argument proves the full Segal condition for every label.

Step 5: checked degree-one fibers, naturality in labels, path transport, empty-object case, and fixed-endpoint locality against the model and geometric-descent statements; verdict: locality is applied fiberwise and no total-edge locality is assumed.

Step 6: checked the full-subcategory cocone argument and coherent model equivalence against the enhanced-cone definition and model statement; verdict: the ambient initial cocone remains initial, and the two-line universal-property argument is appropriately marked elementary.

Step 7: checked object-space compatibility, mapping-presheaf equivalence, fullness of the local subcategory, and the definition of fully faithful against the model and complete-algebroid definition; verdict: exactly the stated cocone conclusion follows.

Existing nodes: reread all five cited node statements in full and searched the DAG for algebroid, Segal, geometric-realization, and full-faithfulness duplicates; verdict: no new node or Mathlib leaf is needed, and no citation cycle occurs.

Small cases: checked empty object space, constant diagrams, the one-object case, and non-discrete object paths; verdict: no hidden nonemptiness, discreteness, completeness, or essential-surjectivity hypothesis.

Changes: retained the statement and all seven proof steps. Expanded the step-1 conventions quotation and step-3/4 space-descent quotations so the audit excerpts include the clauses actually used. Added two independent Mathlib searches and their actual logged results: the semantic query returned strict Segal right-Kan-extension declarations, read at `Coskeletal.lean:186–226` with `StrictSegal.lean:42–60`; grep returned the ordinary `BicartesianSq.of_isPullback_isPushout`, read at `BicartesianSq.lean:293–295`. Neither states this item. Appended this second-reading record. No Lean files, compilers, Lake, or build tools were used.
