# Q52 stage-1 report: lem-weil-pbc-integral-models-extension-closed

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-models-extension-closed.json`: statement, split into six proof steps; no Mathlib match for the whole theorem. Statement and original metadata retained.
- `citations.json`: verbatim statement excerpts for every step-node citation.
- `report.md`: this report. Search command records remain in `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this item is not the unit key node.

## Attachments

None. I searched upstream WeilConjectures for the exact blueprint tag, the item id, integral-model terminology and constructible extension terminology. FieldCoefficient/Extension.lean proves closure of constructible field sheaves, not existence of a continuous integral model under the stated Ext criterion. CategoryTheory/ModuleObjects/EllAdicRationalization.lean concerns derived rationalization with its internal-module notion, not this exact module-sheaf statement. No exact finished project declaration was found to attach.

## WANTED

None. All sources used are already in literature/.

## Audit of the original item and blueprint

The current item is correctly stated: surjectivity of the *specified* localized scalar-extension map is an explicit hypothesis. It had no proof. I retained the statement, including its final sentence allowing the inclusion to change. The important detail missing from a bare instruction to clear denominators is that a rationalized integral extension has class varpi^m times the given class, not the given class itself. Step 5 corrects for this by replacing the inclusion u by u composed with multiplication by varpi^(-m), and computes the class by an explicit morphism of sequences. No statement dispute or source error was found for this item.

I read the current blueprint main-20261015 finite-extension node, its chapter and unit. The current finite-extension statement has no lattice proof paragraph; this item's recorded ancestry refers to the historical first sentence and reaches it through the integral-lattice and realization nodes. This delivery preserves that historical provenance and realizes the final paragraph of Bhatt-Scholze 6.8.13, rather than pretending it is new text in the current blueprint. Whole-blueprint searches for integral extension, integral model, stratified perfect, scalar localization and extension class found no other blueprint node stating this conditional theorem. In particular sk-lem-integral-models is a different derived finite-type/field-setting assertion. The proof citations are in this item's own unit; no off-unit tool declaration is needed.

## Mathlib searches

I ran msearch.py under Q52 and this item for LeanFinder (two different formulations), Loogle, grep and LeanSearch. Their exact queries and returned names are appended to the existing mathlib_searches, with the search command's records retained in searches.jsonl. All services answered. The first LeanFinder returned localization/surjectivity lemmas for ordinary modules and local sections; LeanSearch returned valuation-ring algebra. The second LeanFinder returned Ext.mapExactFunctor and general Serre-class infrastructure. I read Mathlib/Algebra/Homology/DerivedCategory/Ext/ExtClass.lean (especially extClass and extClass_naturality, lines 81 and 131) and Ext/Map.lean (actual exact-functor construction and class compatibility). They support ingredients already represented in DAG nodes, not the integral-model existence assertion. The grep query found no matching theorem. The old item searches were preserved, not presented as newly executed searches.

## Not duplicates

No new nodes were created. Existing lem-weil-pbc-ext-one-extension-classification, lem-weil-pbc-complex-ses-triangle, lem-weil-pbc-continuous-coefficients-immersion-restriction, lem-weil-pbc-scalar-localization-sheaf-exact, and lem-weil-pbc-integral-stratified-perfect-characterization supply the required non-elementary facts. The internal finite-presentation Serre node was deliberately not used to identify ordinary finitely presented A-module local models: the cited stratified characterization states the exact latter condition.

## Review by Q52

I read Bhatt-Scholze Lemma 6.8.13, particularly its last paragraph, and expanded its Ext-denominator implication. I also read Lemma 6.8.2 (continuous coefficient completion/localization), Definition 6.8.10 and Proposition 6.8.11(1),(3) (integral constructibility and its derived characterization). For extension classes I read Stacks derived.tex Tag 06XV, lemma-ext-1, its degree-one identification through Tag 06XU, lemma-yoneda-extension, and Tag 0152, lemma-derived-canonical-delta-functor, which gives the natural connecting morphism for a sequence of complexes. The item follows these sources; no SGA source is used. There are no new nodes with separate sources to audit.

For step 1 I opened the immersion-restriction node and checked that its *statement* gives both A_X = lim(A/varpi^n)_X and A_X[1/varpi] = E_X, compatible with the inclusion. The exactness node explicitly sends every short exact sequence of sheaf modules to a short exact sequence under actual localization, so it supplies exactness, not merely a definition of flatness. X is noetherian as required for the coefficient comparison; no enough-points assumption is smuggled in.

For step 2 the extension-classification statement provides the original degree-one class. The module-localization definition gives representatives alpha/varpi^m for m >= 0. Applying the hypothesized surjection gives the exact identity xi = varpi^(-m) S(alpha); there is no auxiliary Ext continuity assumption to prove. Step 3 uses the reverse direction of that same classification *in the ambient A_X-module category*, which gives an actual middle module N without first asserting it is constructible.

For step 4 I checked the full statement of the stratified-perfect characterization: its condition (iii) is boundedness plus cohomology sheaves locally A_X tensor_A a finitely presented ordinary A-module, on a finite stratification, and its final sentence gives closure under shifts and cones. Thus P[0] and Q[0] satisfy exactly its hypotheses. The coefficient completion and immersion-restriction identifications make its completed-ring and stratum coefficients the item coefficients. The SES-triangle node really supplies a distinguished triangle for degreewise exact complexes; rotation and shift/cone closure put N[0] in that same category. Its only cohomology sheaf is N, so condition (iii) gives the required ordinary-module local models. The scheme assumptions (noetherian, finite dimensional, ell invertible) and finite coefficient extension are all in the item. This avoids equating two different constructibility encodings without a comparison theorem.

For step 5 the classification node explicitly includes exact-additive-functor compatibility, so its statement identifies the rationalized class with S(alpha). The connecting-morphism naturality node explicitly gives u_1[1] composed with delta = delta-prime composed with u_3. The morphism from the given sequence to the rescaled one has left scalar varpi^m and identities in the middle and right. I checked the left square: (u composed with varpi^(-m)) composed with varpi^m equals u. Thus the rescaled extension has class varpi^m xi, as required. This is not an unproved pushout or transport assertion. Step 6 uses injectivity of classification with identity endpoints, which really gives an isomorphism of middle objects, and then forgets the rescaled inclusion. The conclusion does not claim an integral model compatible with the original u.

I checked small cases: m = 0 leaves the given inclusion unchanged; a zero class is represented by a split integral extension; P = 0 or Q = 0 reduces to the corresponding rationalized module; integral torsion is allowed and nowhere divided inside N. An empty X gives the zero module category and the same argument. Rescaling only occurs over E_X where varpi is a unit. No new fact is a duplicate, elementary padding node, or reformulation of the item's conclusion. All six proof steps are below 2000 characters and carry explicit arguments with their non-elementary statements cited. The union of uses is exactly proof_deps; all selected dependencies have no return path to the item. Every citation quote is copied verbatim from the dependency's statement.

## Unfinished work

No mathematical portion of this one-level split remains. The required deliver.py --no-push exited 0 with OK at d674075d6e9: server preflight, check_dag and review_split passed. The direct push follows this successful dry run.
