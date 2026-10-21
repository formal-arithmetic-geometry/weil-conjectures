# Q54 stage-1 report: lem-cbc-ringed-open-flat-resolution

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-ringed-open-flat-resolution.json: statement node, split into five steps; no Mathlib match.
- citations.json: ten verbatim statement excerpts, one per step/node citation.
- report.md: this report. searches.jsonl is the unmodified search-command log.

No new nodes, no new Mathlib leaves, no Lean files and no unit/chapter changes. The existing statement, source, created record and blueprint ancestry are retained. The existing Mathlib search records are retained and the five searches actually run by Q54 are appended.

## Attachments

None. I searched WeilConjectures for the item tag and for K-flat/extension/flat terminology. SheafOfModules.isFlat_extensionByZero_unit in lean/WeilConjectures/Algebra/Category/ModuleCat/Sheaf/ExtensionByZeroFlat.lean states only flatness of the extended localized unit. I read its statement and proof; it gives neither arbitrary flat terms nor the unbounded K-flat and strict-tower assertions. The exact localized module adjunction is an existing input, not an attachment of this item.

## WANTED

None. The blueprint and Stacks source files used here are present.

## Problems found and changes

The item had no proof or proof dependencies. Its statement is correct with the standard sheaf meaning of surjective: an epimorphism of module sheaves, equivalently local surjectivity. Step 4 makes that meaning explicit. No assertion of surjectivity on all global sections is introduced. The tower claim is expressly objectwise; it does not identify objectwise K-flatness with any stronger tensor-flat property in a system category.

I reused lem-sf-ringed-open-total-tensor-kflat, an existing statement that includes the full unbounded direct-sum chain comparison, rather than creating another comparison or K-flat-preservation node. The item's further flat-term and strict transition clauses are proved in the steps. The current blueprint's later claim that extension by zero preserves countable products is not an input or a consequence of this split. This split supplies only the ordinary exactness and resolution calculation needed at the opening of that blueprint proof.

## Not duplicates

No new nodes were created. The existing lem-sf-ringed-open-total-tensor-kflat covers the chain comparison and K-flat-resolution clause; I cite its chain comparison and give the acyclic test explicitly. The existing ringed-slice extension-tensor and exact-adjunction nodes supply the sheaf inputs. Blueprint searches for K-flat, extension/K-flat and flat resolution, together with whole-DAG tag/concept searches, found these inputs rather than a reason to introduce another node. No blueprint node states every clause of the item.

## Review by Q54

I read the current main-20261015 proof of lem-cbc-completed-extension-zero-comparison, its chapter/unit records and the item's originating statement. I read Stacks sites-modules.tex at lemma-extension-by-zero, lemma-extension-by-zero-exact (03DI/03DJ), lemma-j-shriek-and-tensor (0E8I), and definition-flat (03ER), verifying the labels against the local tag table. I also read homology.tex, section-functors and definition-quasi-isomorphism-cochain (0115). The unbounded and tower refinements are honestly marked agent-written, rather than attributed as a literal Stacks theorem. There are no new-node sources to check.

For step 1 I opened the statement of lem-pur-site-restriction-module-adjunction-exact: it identifies exactly the sheafification of the direct-sum extension presheaf in the item, and states exactness of both that functor and restriction for a sheaf of commutative rings. Its hypotheses apply on our small site in the chosen module universe. The cohomology definition in def-pc-acyclic-complex-modules is the kernel/image quotient used in the two displayed short exact sequences. These sequences give the natural cohomology identification degree by degree, including for unbounded complexes; there is no uncited spectral-sequence or totalization argument.

For step 2 I opened lem-sf-ringed-open-total-tensor-kflat and checked that its statement really provides a natural chain isomorphism for arbitrary unbounded complexes using direct sums, the same ringed slice and the same sheafified extension. It does not require constant coefficients or flat terms. The other citation, def-pc-kflat-complex, gives exactly the acyclic tensor test. Step 1 makes restriction of the acyclic test object and extension of the resulting acyclic tensor valid. I wrote the signed interchange formula explicitly to cover the order of factors in that definition. This reuses a stronger existing node, rather than hiding this item in a new node.

For step 3 I opened lem-weil-pbc-ringed-slice-extension-tensor: it gives an isomorphism natural in both module variables for the actual sheaf tensor and actual sheafified extension. Naturality is exactly what identifies the two maps of the three-term sequence. I checked def-pc-flat-sheaf-modules says exactness of tensoring, and the exact-adjunction statement supplies the two exact functors used. Applying this three-functor argument to a short exact sequence is elementary from those statements; I did not turn it into a new node or confuse flatness on sections with sheaf flatness.

For step 4 the exact-adjunction statement gives preservation of the displayed kernel/epimorphism short exact sequence. The statement of def-pc-quasi-iso-modules is precisely the cohomology-isomorphism test used with step 1. The functor carries inverse maps to inverse maps, so no reflection or conservativity assumption is used. Surjectivity is not inferred merely from K-flatness.

For step 5 I read lem-weil-tower-category-levelwise-abelian. It asserts that kernels/cokernels and epimorphisms are levelwise for strict inverse sequences in any abelian category. Hence cycles, boundaries and cohomology are also levelwise by their definitions. Applying a single actual functor to the strict transition and chain equations preserves them. There is no choice of independent replacement maps, no inverse-limit operation, and no product-preservation assumption.

I checked B1-B10: no new-node proof sketches, no missing object introductions, no unsupported Mathlib leaf or invented searches, no changed protected fields, and the blueprint reference and search are present. For C1-C8 I read all eight distinct cited statements, wrote all ten verbatim excerpts, and declared the off-unit generic tools in split_report.tool_uses. Every input used is its statement, not a construction borrowed from its proof. For D1-D5 the steps carry the cohomology, acyclic tensor, short exact tensor and strict-functor arguments; no new restatement, circular lemma or omitted induction is introduced. For E1-E7 I checked the fixed universe/smallness, commutative variable ring sheaf, actual slice restriction and extension, unbounded direct-sum totalization, and degreewise rather than bounded reasoning.

Edge cases: the zero complex and zero module satisfy each step; the empty sum in the presheaf construction introduces no problem because the exact-adjunction input already treats it. No final object or spatial points of the site are used. A one-term flat complex reduces step 3 to the sheaf exact tensor test. An unbounded acyclic test complex still uses only degreewise exactness and the stated unbounded comparison. Nonidentity or zero strict transition maps remain their functorial images, so no transition invertibility is assumed. No step exceeds 2000 characters; none hides a separate long comparison argument. No statement dispute was needed.

## Verification and unfinished work

The server-side review_split check passed with zero new nodes. The unit has no realization recorded yet, as expected: this item is not its key statement and I did not change the unit. The required full delivery dry run follows this report. No unfinished mathematics within this one-level split remains; existing unsplit dependencies remain the project's own queue items.
