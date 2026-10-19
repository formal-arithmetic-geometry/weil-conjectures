# Worker report: lem-cbc-relative-nerve-projective-cofibrancy

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-relative-nerve-projective-cofibrancy.json`: item, statement, split; no Mathlib match. Eight proof steps establish the two free-cell squares, colimit preservation, free-cell lifting, and the relative skeletal/marking construction. The mathematical statement is unchanged.
- `citations.json`: fifteen verbatim dependency-statement quotations, one for each step/node pair.
- `searches.jsonl`: actual Q89 search results, retained in the sandbox; the item's pre-existing Q12 searches are preserved and Q89's seven searches are appended to the item record.
- `report.md`: this report. `finish_split.py` is a sandbox-only preparation script, not a project file or a delivered dependency.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. All four statement dependencies are existing nodes, and the proof dependency union consists of those same four nodes. No unit realization fields are changed: this item is a created descendant, not the unit's statement node.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id, relative nerve, projective cofibrancy and free boundary terminology found no declaration. The corresponding search of the read-only upstream master likewise found no exact declaration. The item has no existing Lean-audit declaration to attach. No Lean source was written and no compiler was run.

## Wanted literature

WANTED: local archive of Lurie, Higher Topos Theory, §3.2.5, especially Lemma 3.2.5.15(2), for lem-cbc-relative-nerve-projective-cofibrancy. The referenced PDF was read online at https://www.math.ias.edu/~lurie/papers/HTT.pdf (printed pp. 195–203, PDF pp. 212–220), without downloading into the shared repository. The item's proof is recorded as agent-written because the explicit free-cell calculations are supplied here. There is no Stacks tag for this specific marked relative-nerve construction; no Stacks result is claimed or silently substituted.

## Findings and corrections

The item is mathematically correct. Its former source place made the explicit free boundary and marking attachments sound like statements in Lemma 3.2.5.17(2). Reading the source shows that Lemma 3.2.5.15(2) is the preservation-of-cofibrations result, while 3.2.5.17(2)(D)–(F) uses marking and skeletal reductions and projective cofibrancy. The source-place description now makes this distinction. The formula for the functor, both canonical squares, and every hypothesis and conclusion of the item are retained.

In self-review I corrected two defects in my first draft before delivery. First, a general marked monomorphism must start the filtration from the given marked X, not from X with all nondegenerate markings erased. The final steps 6–7 retain its markings, construct Y_0, and add only markings missing in Y_0. Second, the image of the nondegenerate edge in a free marking cell has label h at its terminal vertex, not h composed with the base edge; the composite occurs at the initial vertex only. Step 4 now states the correctly typed edge pair. I also replaced an appeal to unspecified generating cofibrations by the explicit free-evaluation lifting adjunction and the short lifting proof of closure, so that the stronger coherent-diagram node is unnecessary.

The current blueprint ancestor is thm-cbc-finite-level-proetale through the inherited comparison/descent chain. I read the current blueprint theorem and proof in `main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/` and the inherited comparison node's proof steps 4–5 and 12–14. The created item's ancestry is retained. Its proof supplies exactly the free-cell projective-cofibrancy ingredient used at parent step 5, not a replacement for the compact-support base-change unit route.

## Mathlib searches and existing-node search

Before splitting, `blueprint_refs.py ancestor` confirmed the inherited ancestor. Whole-blueprint searches for “relative nerve projective cofibrancy”, “slice diagram”, and “boundary marking” found no matching blueprint statement; the broad “projective” search was also inspected. DAG searches for free diagrams, projective cofibrations, relative nerve and marking cells found the existing projective-calculus and boundary-cell nodes and the parent comparison node. The cone-boundary-projective-cells node concerns a different coherent-realization cone, and was read rather than confused with the pairs functor. No new auxiliary lemma is needed.

Q89 ran LeanFinder for “projective cofibrancy of marked slice diagram L_C(X) via free boundary and marking attachments” and a second formulation beginning “The last vertex slice pullback…”. The returned results are generic cofibrant-object declarations and unmarked simplicial-set boundary/horn declarations, not the marked diagram squares. LeanSearch for “marked relative nerve slice diagram is projectively cofibrant by cellular filtration” similarly returned the generic IsCofibrant definition and unmarked Kan–Quillen results. The first Loogle query was rejected for the unknown identifier Projective.cofibration; it is recorded as unavailable. The second, `"IsCofibrant", "Functor"`, returned only the inclusion of cofibrant objects into the localization. The first grep incorrectly repeated Mathlib as the subdirectory and is explicitly not used as absence evidence; the corrected root grep `projective.*cofibr|relative.?nerve|MarkedSSet|marked.*simplicial` returned zero hits. The exact queries and result names are in searches.jsonl and the appended mathlib_searches. None is a one-line specialization of the item.

## Not duplicates

No new node pairs require comparison: the delivery has no new node. The statement of the item is not moved into a child node. All its geometric/combinatorial content is carried by its own proof steps.

## Review by Q89

I read the full statements of all four cited nodes, and HTT's relative-nerve definitions and Lemmas 3.2.5.15(2) and 3.2.5.17(2). The item only assumes a small ordinary category and an arbitrary marked simplicial set over its nerve; no fibrancy, cancellation, faithfulness, finite-dimensionality or finite-marking hypothesis is used. Regarding the category as simplicially enriched means discrete mapping sets, so the free diagram of the projective-calculus statement really is the displayed coproduct indexed by C(b,c).

Step 1 uses the standard simplex/operator/ordinary-nerve conventions in def-cbc-enhanced-diagrams-cones and the marked-object convention in lem-coef-marked-point-cartesian-model. The composition equality is written out; neither node is cited for a theorem about straightening. Step 2 uses only the marked-object definition: I checked the degreewise colimit construction against its universal property, then decomposed by the fixed base simplices. This explicitly proves preservation of colimits and markings instead of assuming it from an adjunction whose existence has not been cited.

Step 3 uses the standard simplex formula and the boundary node's union-of-proper-faces definition. A simplex misses a vertex precisely when it is in that boundary; the complement consists of the surjective order maps. On this complement its last vertex is n, hence the label is exactly an arbitrary arrow from sigma(n). This is the degreewise pushout argument, including possible noninjectivity of the map on boundary labels. The source/target of every displayed composite is correct. Minimal markings produce only degenerate pair edges, so the marked square follows from step 2, not from an unmarked claim alone.

Step 4 uses the marked-object definition and the degree-one standard simplex. The underlying pushout is the identity-on-underlying-sets pushout; its only new markings are the pairs (identity,h). The terminal label is h. In particular, a degenerate base edge does not make the domain's nondegenerate edge degenerate. This is why no assertion about reflecting base degeneracies is used.

Step 5 uses exactly two assertions of existing nodes: the absolute model has underlying-injective cofibrations and the cofibration/trivial-fibration weak factorization system; the projective model has objectwise weak equivalences and fibrations and the free-evaluation adjunction. These are all in their statements, and the citation quotes include the whole relevant paragraphs. The free-map lifting test and closure under coproduct, pushout and continuous transfinite composite are each proved directly by constructing lifts. This step uses no unquoted theorem about projective generating cofibrations, no hypothesis about their chosen generating sets, and no blanket claim that objectwise cofibrations are projective cofibrations.

Step 6 uses the boundary-cell decomposition for exactly a degreewise injective map, identified with its image. It supplies all nondegenerate simplices not already in X with their actual Y base maps. I checked that every boundary is in the preceding stage and that attaching minimally marked cells retains the old source markings. Thus its limit is Y_0 with all of Y's simplices and just the old markings plus degeneracies. The colimit and pushout arguments are previous steps' constructions, not extra claims attributed to the cited boundary statement. Step 7 adds precisely the remaining marked edges by a single small coproduct pushout; the diagram pushout is the iterated pushout from step 4, using step 2 and the free-map lifting from step 5. This finishes the general map, including a map whose underlying function is the identity but whose target has more markings. Step 8 uses the initial map criterion for cofibrancy in the projective model already in force and the explicitly proved preservation of the initial object.

For edge cases I checked n=0, where both boundary terms are empty and the free vertex is the whole slice value; n=1, where the two old vertices may have additional incoming label identifications but the new edges are freely indexed at the last vertex; C terminal, where L_C is the identity and the two squares reduce to their ordinary boundary/marking squares; C empty, where X must be empty and the diagram category has its unique initial object; and an object c with C(b,c) empty, where a boundary term may still be nonempty but no new full simplex is attached. I also checked a nonfaithful composition map on outgoing labels: the proof never cancels it and does not require vertical maps to be monomorphisms. The relative marking argument covers X already marked, an isomorphism on underlying simplices with strictly more target markings, and infinitely many added simplices or markings. Smallness of C and of all simplicial sets in a containing universe is sufficient for every coproduct and sequential colimit.

Against delivery-errors B–E: there are no statement-only children to contain disguised proofs, duplicates, unsupported new notions, or unrun searches. All non-elementary inputs are statements of the four existing cited nodes. Fifteen exact citation quotations were tested against those statements. No parent node is cited, so the proof does not import a circular assertion from its user. The three off-unit generic tools are declared in split_report.tool_uses. The parent route is preserved. The proof has no non-elementary step above 2000 characters; the largest such step is the explicit boundary pushout, about 1200 characters, and it contains one degreewise argument rather than an omitted comparison lemma.

## Unfinished work

No mathematical part is left open in the item. Downstream existing nodes retain their own statuses; no claim is made to have proved their Lean implementations. The required server checks and delivery result are recorded below when available.
