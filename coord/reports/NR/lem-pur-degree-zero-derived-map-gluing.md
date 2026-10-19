## Files written

- dag/nodes/sec-smooth-purity/lem-pur-degree-zero-derived-map-gluing.json: statement node, now split in seven steps; no exact Mathlib match for the whole assertion. No new nodes and no new Mathlib leaves.
- citations.json: twenty-two step/node entries, each quoting an exact substring of the cited statement.

The interrupted attempt had only searches.jsonl and dispatcher brief files, with no item, split or report. No deliver.py process was running when resumed. I retained and read all five logged searches rather than reissuing them. The sandbox script write_split.py is scratch material only; it is not part of the delivery.

## Attachments

None for this item. Searches of WeilConjectures in the read-only slopmaster2 source by the exact blueprint tag and by derived gluing, degree-zero, singleFunctor and sheaf-map terminology found no project declaration stating all the clauses. The affine-line concentration and orientation uniqueness declarations are special cases with extra geometric hypotheses, not this general statement. The existing DAG leaf lem-weil-pbc-derived-single-fully-faithful already records DerivedCategory.instFullSingleFunctor and DerivedCategory.instFaithfulSingleFunctor; I read the Mathlib source at FullyFaithful.lean lines 37 and 45 and reuse that leaf.

## WANTED

None. All sources used are already in literature/stacks-project/.

## Corrections and source findings

The mathematical statement is retained, including arbitrary set-indexed open covers, both small sites, ordinary uncompleted derived categories, finite commutative coefficients, naturality, restriction compatibility, uniqueness and the empty scheme. I changed only its bracketed restriction reference and the corresponding stmt_deps: def-weil-derived-pullback-tensor-hom is scoped to the special coefficients A_E,n and the small pro-etale site, whereas this item allows arbitrary finite commutative A and also the small etale site. It is replaced by the localized ringed-site definition, the existing exact module restriction statement and the exact-functor derived-category leaf. This is a reference repair, not an added hypothesis or a weakened conclusion.

The item was an unsplit child of lem-pur-vector-integration-site-comparison. Its source states the general degree-zero Hom identification, not a general descent theorem for all derived morphisms. The proof now first establishes global concentration and an explicit natural truncation identification, then applies fully faithful embedding and module-map gluing. There is no appeal to arbitrary derived-category descent.

Source precision: Modules on Sites 03DJ, lemma-extension-by-zero-exact, states exactness of extension by zero. It does not itself state restriction exactness, despite the shorthand in some inherited DAG source records. I read the sectionwise restriction in 04IX, definition-localize-ringed-site, and the explicit use of restriction exactness in the proof of 0E8G, lemma-j-shriek-reflects-exactness. My proof takes exact restriction from the statement of lem-pur-site-restriction-module-adjunction-exact, which explicitly supplies it; its source place now accurately distinguishes these facts.

## Source error

The printed proof of Derived Categories 06XS, lemma-negative-exts, says after upper truncation that the representing L has L^i zero for i < a. The truncation used there instead has L^i zero for i > a. The assertion of 06XS is correct. I use its degree-zero Hom assertion through the existing fully faithful Mathlib leaf and do not reproduce that erroneous inequality. No item statement requires correction.

## Unfinished work

None in the requested one-level split. Existing cited nodes retain their own status and proof responsibilities. No Lean was written, no compiler or Lake tool was run, and no shared node, unit, chapter, launcher or live-project file was edited.

## Not duplicates

No new nodes were created. Before deciding this I searched all dag/nodes for 06XS, 03EM, 04TQ, localization, restriction, concentration, fully faithful embeddings and gluing, and used blueprint_refs.py ancestor and searches for degree zero, glue maps, derived maps, gluing and 06XS. The general sheaf-map gluing, single-complex Hom and site-localization facts already have nodes, so I cite them. Blueprint hits for tower gluing and representing-pair gluing concern different complexes/coefficient constructions; they do not state this assertion, and same_as remains empty. The ancestry still points to cor-pur-dualizing-object-purity through lem-pur-vector-integration-site-comparison. This auxiliary sheaf argument realizes the normalized-map uniqueness clause without changing the smooth-purity unit's diagonal/deformation/vector-bundle route.

## Review by NR

I read the item's statement against Derived Categories 06XS, lemma-negative-exts (especially part (2)); Homology 0118, section-truncations, including both explicit cochain truncation diagrams; Modules on Sites 04IX, definition-localize-ringed-site, 03DI, lemma-extension-by-zero, 03DJ, lemma-extension-by-zero-exact, 0E8G, lemma-j-shriek-reflects-exactness, and 03EM, lemma-internal-hom; and Sites 00XZ, section-localize, 00VR, definition-sheaf, and 04TQ, lemma-glue-maps. I also read the current main-20261015 ancestor statement and proof. There are no new-node sources to review. The assembly is explicitly agent-authored, since no single source asserts the entire local-concentration/gluing consequence.

Step 1 uses the statements of lem-weil-pbc-etale-site-localization-open and lem-weil-proetale-weakly-etale-localization for the actual site equivalences, not merely a definition of localization. The latter also gives the constant-ring comparison. The statement of lem-weil-pbc-site-constant-restriction supplies the etale coefficient comparison and its unit compatibility; equality of multiplication can be checked on locally constant generators. I checked that open subschemes and their intersections meet the hypotheses. The two site-definition statements give the relevant coverings, and def-weil-pbc-sites-and-cohomology gives stability under pullback. The additional existing Mathlib leaves lem-weil-pbc-affine-opens-basis and lem-weil-pbc-affine-scheme-qcqs explicitly supply the affine refinement and its finite subcover. I read Schemes 01IT, lemma-basis-affine-opens, and Algebra 00E8, lemma-quasi-compact, for these clauses. Only affine opens of an object are finitely refined for the pro-etale covering test; neither T nor its given cover is assumed quasi-compact. Both covering pullbacks and all overlaps are actual scheme fiber products.

Step 2 takes exact module restriction from the precise clause of lem-pur-site-restriction-module-adjunction-exact and termwise derived functoriality from lem-sf-exact-functor-derived-triangulated. These are the ordinary module sheaf categories, with no constructibility, boundedness, coefficient exponent or characteristic hypotheses. The cohomology-sheaf definition supplies the kernel/image quotient, so exactness gives its restriction comparison. The text verifies derived-morphism naturality using localization; it does not take that theorem from a definition of a pro-etale exceptional operation.

Step 3 uses only the stated sectionwise restriction formula and the equalizer sheaf axiom. Its proof of vanishing is objectwise and therefore works without an enough-points theorem on the pro-etale site. A zero restriction makes every local section zero; separatedness then makes every global section zero. This is the elementary local-to-global vanishing step, not a new node restating a clause of the item.

Step 4 uses the formulas in def-kun-truncations and the inversion of quasi-isomorphisms in def-weil-abstract-derived-category. I checked the direction of both arrows: the good upper truncation maps to C and to H^0(C)[0], so the desired isomorphism is Q(p) composed with Q(c) inverse. The degree-zero quotient kills the incoming differential, making p a chain map. All its other cohomologies are zero after Step 3. This is an explicit elementary two-arrow construction; no splitting of module sheaves or injective-resolution existence is being assumed.

Step 5 uses the actual statement of lem-weil-pbc-truncation-descends, which supplies the projection as a natural transformation after localization. The other cited statement, lem-weil-pbc-localization-universal-property, supplies descent of natural transformations, not just existence of a localization category. I wrote both chain-map naturality equations and checked that exact restriction preserves the kernels, images and quotients occurring in them. Thus the canonical isomorphism is independent of the chosen complex and compatible with iterated restrictions. This addresses the compatibility itself rather than leaving the word transports in place of an argument.

Step 6 uses abelianness from def-weil-sheaf-of-modules-category and exactly the Hom bijection stated by lem-weil-pbc-derived-single-fully-faithful. Its hypotheses hold for either site in the chosen universe. I checked the conjugation directions and that restricting a single-complex map is literally the single-complex map of the restricted sheaf map. Faithfulness on intersections is what turns the given derived overlap equation into the required sheaf overlap equation. No general derived morphism sheaf property is assumed.

Step 7 uses the existence and uniqueness in the statement of lem-pur-sheaf-hom-cover-gluing. It allows a covering of any object on a site with the indicated fiber products; here that object is T, the final object, and the product conditions were checked in Step 1. Its conclusion is a module-sheaf map, exactly the input needed by Step 6. I checked that forming the inverse conjugate yields the prescribed local derived maps, and that its uniqueness yields injectivity as well as surjectivity.

I tested the statement and argument on an empty scheme with the empty cover; an empty open added to a nonempty cover; the singleton cover by T; repeated opens; zero M or N; a disconnected scheme; and the zero coefficient ring. Empty-cover sheaf sections are singleton groups, so every sheaf is zero on the empty site and all complexes there are quasi-isomorphic to zero. No nonempty-index assumption appears in the argument. For a nonempty scheme an empty family is not a cover. An unbounded representative with acyclic nonzero tails is also allowed: the truncation proof uses vanishing cohomology, not termwise boundedness. This is why arbitrary derived complexes outside the heart are not claimed to satisfy the same gluing property.

Against delivery-errors B through E: there are no new nodes with hidden proofs, missing hypotheses, duplicate identities or unrun searches. Every non-elementary ingredient is an existing cited statement; citations.json was checked verbatim against those statements. No proof has been moved into a new node that restates the item. The only two elementary steps are the sheaf-equalizer zero test and the explicit good-truncation quasi-isomorphism construction. All seven steps are shorter than 2000 characters and contain the needed comparison formulas. The corrections from self-review were the mismatched original restriction reference, a source-label imprecision about restriction versus extension exactness, and four escaped TeX tabs in Step 1 and three citation excerpts shorter than the delivery tool's forty-character minimum; those were repaired before the dry run. There was no lead or second worker, as required by this direct-delivery brief. Generic off-unit tools are declared in split_report.tool_uses; no maintainer-owned tool_uses field was set.

## Validation

The initial completed server dry run passed at 7b1ce3f84e. The final self-review then made the finite affine-refinement ingredients explicit using two existing Mathlib leaves and added their verbatim citations. The final dry run below checks that updated split before direct push.

## Delivery blocker

The updated final dry run exited 1. Its only diagnostic was an unrelated shared-DAG parse error: tools/check_dag.py reports that dag/nodes/sec-six-functors/lem-coef-terminal-local-kan-corepresentability.json has Extra data at line 261 column 2 (character 29703). I independently read that file in the shared snapshot with json.loads and reproduced the same error. This is outside this item's delivery scope, so I did not edit it or suppress the check. No delivery process remains active and nothing was pushed. The item, twenty-two citations, report and exact search log are retained for resumption after maintenance repairs the shared DAG.
