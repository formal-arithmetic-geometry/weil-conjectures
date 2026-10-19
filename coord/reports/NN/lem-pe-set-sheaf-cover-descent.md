# Stage-1 split: lem-pe-set-sheaf-cover-descent

## Files written

- dag/nodes/sec-proetale-coefficients/lem-pe-set-sheaf-cover-descent.json: existing statement, split into eight steps; no exact Mathlib match found.
- citations.json: one verbatim statement quotation for every citation of every step.
- report.md and searches.jsonl: report and actual search records. prepare.py is sandbox-only preparation scratch.

New nodes: 0. New Mathlib leaves: 0. The item is not a unit key node, so no unit realization fields are changed.

## Attachments

None. Searched the project source under /home/ubuntu/weil-src-slopmaster2/WeilConjectures by the exact id, blueprint tag, gluing names and the set-sheaf descent notion; no declaration states both clauses of this item. The master checkout was also searched as reference material, not as proof evidence. Existing module-sheaf descent declarations have different coefficient objects.

## WANTED

None. The Stacks sources needed for the proof are present.

## What was wrong or incomplete

The item was a statement-only dependency with no proof. Stacks sites.tex Tag 04TR (lemma-glue-sheaves) gives the compatible-tuples formula but omits restriction maps, the sheaf verification, local inverse construction and overlap compatibility. Tag 04TQ (lemma-glue-maps) omits naturality. The delivery supplies those arguments. No statement dispute or statement change was necessary. In particular the repeated-index cocycle does not say phi_aa is identity on the entire self-overlap: only its diagonal restriction is identity; the local graph maps correctly use precisely that consequence.

The shared working snapshot does not contain this recently created item or its parent split. The project's configured live DAG mirror /home/ubuntu/weil-nt-live-dag/nodes does contain it, with status unsplit and creation item det-pe-torsor-comparison-affine. I copied that existing node into the authorized sandbox and preserved its statement, creation record and blueprint ancestry. No shared or live file was modified. Delivery fetch/preflight will test the current authoritative overlay.

The blueprint parent is det-pe-torsor-comparison-affine, whose current text is the sk-lem-pe-torsor-comparison-affine.md / .proof.md pair in main-20261015. Its torsor gluing and comparison-isomorphism descent use exactly the two clauses proved here. The unit and chapter records were read; the proof remains the sheaf-gluing tool on their specified route. The generic sectionwise-limits theorem is declared as a tool use in split_report, rather than replacing a unit step.

## Not duplicates

No new nodes are created. The existing live-mirror lem-pe-site-sheaf-gluing states only effective object gluing, without the morphism clause. It overlaps the first clause of the assigned existing item, but I did not create it, copy it into this delivery, or replace the requested proof by a restatement of it. The module-compatible-tuples and module-sheaf-gluing nodes concern modules and require module gluing data, so they are not interchangeable statements about the given set sheaves. lem-pur-sheaf-hom-cover-gluing concerns linear morphisms of module sheaves. Blueprint searches for 04TR, 04TQ, gluing sheaves, descent sheaves, gluing sets and glue found no imported blueprint statement of this full generic theorem.

## Review by NN

I read Stacks sites.tex, lemma-glue-sheaves (04TR, lines 5813–5896 including the preceding gluing datum), and lemma-glue-maps (04TQ, lines 5638–5705), checking the tag-to-label mapping in tags/tags. I also read the current blueprint unit, chapter, affine torsor statement/proof and the live parent steps that call this tool. No new node needs a separate source check.

Step 1 uses def-weil-pbc-sites-and-cohomology clause (1), whose statement explicitly supplies base-change coverings and the equalizer sheaf condition, and def-pur-localized-ringed-site, whose statement supplies the slice topology, restriction formula and relocalization. Their statements justify the two displayed component-sheaf diagrams. The only pullback identifications are verified by their defining universal property. def-weil-size-convention fixes the larger universe; the item's additional product bound ensures that A and A x A and the slice objects are small there.

Step 2 uses exactly clause (1) of lem-weil-pbc-site-sheaf-sets-limits-sectionwise: the sectionwise limit is a sheaf. I read that node's statement, not just its proof: it covers all small index categories, hence both displayed products and the equalizer, on the slice site. No arbitrary-large-limit claim is used. It is a generic tool unavailable in this unit and is declared as such. The explicit formula also constructs restriction maps and checks the functor laws; there is no unconstructed chosen object.

Steps 3–6 use the hypothesis cocycle and the formula already proved in step 2. They are elementary calculations, not references to hidden descent theorems. Step 3 cancels the invertible diagonal automorphism. Step 4 uses the slice restriction notion of def-pur-localized-ringed-site (its full statement is quoted) to evaluate phi_ab on W_b using the given W -> U_a; on W_bc the triple cocycle is exactly the matching-tuple equation. Step 5 pulls the original matching equation back along the indicated graph to show the other inverse identity, and writes out how functoriality makes the inverses natural. Step 6 pulls that same equation back along the graph of the two structural maps to prove the demanded transition identity, with its direction unchanged.

Steps 7–8 use the sheaf equalizer axiom and base-change axiom explicitly stated by def-weil-pbc-sites-and-cohomology (1). The matching family consists of the local images of the same restricted section; its equality follows from the assumed equality of f_a and f_b and naturality. Uniqueness of amalgamation proves naturality on W' -> W and uniqueness of the resulting morphism. On an object already over U_a, the graph W -> W_a is an arrow in C/U_a, so naturality of f_a proves the restriction is exactly the prescribed map. Thus no locality-of-isomorphisms or effective-epi theorem is silently used.

For B–E of delivery-errors: every object is introduced in the unchanged statement; no new statement-only node or definition is needed. Sources name the correct Stacks tags and labels. All searches in the node were run with msearch.py and their exact log records are copied into results. I used two distinct LeanFinder formulations as well as LeanSearch, Loogle and two source patterns. I read the candidate pseudofunctorOver definition, the IsStack conditional theorem, typesGlue, topological section-gluing and dense-subsite morphism construction: none establishes the set-sheaf slice pseudofunctor's stack property under these hypotheses. No Mathlib leaf is asserted. The proof contains no dependency on the item itself or its parent, no new clause nodes, and no SGA reference.

I tested the identity singleton cover (the local graph inverse returns the original sheaf), a singleton cover with nontrivial self-overlap (phi_aa is retained off the diagonal), repeated cover members, empty section sets and an empty covering. For an empty covering of U, the equalizer construction is the terminal sheaf; the local assertions are vacuous, and the empty base-changed covers force P(W) and Q(W) to be singleton sets, so the unique-morphism clause remains valid. No nonemptiness, subcanonicity, finite-cover condition, or monomorphism of cover members is assumed. All products are set-indexed and all required fibre products exist by the item's hypotheses. I corrected the temptation to normalize phi_aa globally by using only its diagonal pullback; the source statement itself needed no repair.

## What remains unfinished

Nothing in this one-level split. The existing sectionwise-limits node is reused and no additional proof obligation was introduced.


## Second reading by NN

I independently opened Stacks sites.tex Tag 04TR, lemma-glue-sheaves and its preceding gluing datum (5813–5896), and Tag 04TQ, lemma-glue-maps (5638–5705); tags/tags confirms both labels. The item's statement matches these two results, with the stated all-fibre-products and universe conventions, and is byte-for-byte the existing live-mirror statement. The local sheaves, direction of the transition isomorphisms, repeated indices, triple cocycle, effective object gluing and unique morphism gluing all agree. No statement dispute was found. I also read the current main-20261015 affine torsor proof, Steps 4–5, and the unit/chapter records: these are precisely the two descent operations needed there.

- Step 1: checked the complete statements of def-weil-pbc-sites-and-cohomology (1), def-pur-localized-ringed-site and def-weil-size-convention against the component-sheaf argument; PASS. The two pullback identifications follow by specifying the same projections, and the sheaf diagrams are those for the base-changed covers. No subcanonical-site hypothesis is used.
- Step 2: checked the complete statement of lem-weil-pbc-site-sheaf-sets-limits-sectionwise, not its proof, against the two small products and equalizer; PASS. It explicitly covers every small diagram, including empty products. Read Stacks 00W2, lemma-limit-sheaf, and Mathlib CategoryTheory/Sites/Limits.lean:139–151: this dependency is already a Mathlib leaf, so it needs no route exception. Expanded its citation quote to include its hypotheses.
- Step 3: checked the (a,a,a) cocycle on the triple diagonal against the datum before 04TR; PASS. Invertibility cancels the diagonal automorphism. This does not normalize the transition map away from the diagonal.
- Step 4: checked the full restriction formula of def-pur-localized-ringed-site and the cocycle against both graph-map definitions; PASS. On W_bc the map to the triple overlap has a-coordinate supplied by W to U_a, and b,c supplied by projections, so the displayed cocycle has exactly the required domain.
- Step 5: checked both composites against Steps 2–4 and the graph W_b to W_ab; PASS after making naturality explicit. The graph identity h_a d'_a = d_a h proves naturality of e, and the displayed component equation using naturality of phi proves naturality of i. The inverse identity only uses the diagonal normalization of Step 3.
- Step 6: checked the pulled-back tuple equation against the prescribed transition direction in 04TR; PASS. The graph of both structural maps yields phi_ab e_a = e_b, sectionwise on every double-slice object.
- Step 7: checked def-weil-pbc-sites-and-cohomology (1), base-change-cover and equalizer clauses, against the t_a matching equation and unique amalgamation; PASS. The assumed agreement of f_a and f_b is evaluated on W_ab, so no unproved local-isomorphism theorem is used.
- Step 8: checked separatedness and uniqueness in the same cited definition against naturality, local restriction and uniqueness in 04TQ; PASS after displaying the projection/graph identity r_a d_a = id and the full restriction calculation. Naturality is tested on each W'_a, which is a covering by base change.
- New nodes: none (zero new statement nodes, zero definition nodes, zero Mathlib leaves). B1–B7 and the removal tests introduce no additional obligations. Existing lem-pe-site-sheaf-gluing was opened: it is only the effective-object clause of this already-existing item, is unsplit, and is not being created or used to hide the proof here.

Edge cases checked independently: for an identity singleton cover the construction recovers the original sheaf; for repeated members and a nonmonomorphic singleton cover the graph section, not an inverse to the cover map, is used. To test the latter concretely, take the site of finite sets with jointly surjective coverings, U a singleton and U_a a two-point set, and the sheaf F_a(W to U_a) of functions W to a fixed two-point set. Relabelling by different permutations on the two fibres produces a valid transition on the self-overlap which is nonidentity off the diagonal and identity on the diagonal; Steps 3–6 retain this transition. Empty section sets cause no choices of elements. For an empty covering of U, every W over U has an empty covering by base change, so every sheaf on the slice has singleton section sets: the constructed terminal sheaf and unique morphism have the required properties. No nonempty-cover assumption is introduced.

Independent searches: ran msearch.py LeanFinder with “The category of sheaves is a stack for the canonical topology; compatible sheaves on over categories descend along a covering”, grep with “pseudofunctorSheaf|sheafOver|IsStack|IsPrestack”, and Loogle for CategoryTheory.GrothendieckTopology.pseudofunctorOver. Their actual records are appended to searches.jsonl and mathlib_searches. I opened PseudofunctorSheafOver.lean:34–50 and Descent/IsStack.lean:42–80: the former constructs the pseudofunctor, the latter supplies conditional results assuming a stack; neither proves this item's assertion. Grep of the project and master CategoryTheory source found no matching effective-descent declaration. Master was used only as reference material. Searches by 04TR/04TQ in the existing DAG found the already-reported object-gluing and module-gluing results; no new duplicate was introduced.

Changes and reasons:

- Expanded Step 5's naturality sentence into its graph identity and coordinate equation, so the elementary claim can be checked directly (E5).
- Expanded Step 8's local restriction equation using the projection and its graph section, making the functoriality calculation explicit (E5).
- Removed split_report.tool_uses for the sectionwise-limits dependency: it is already status mathlib, and the stage-1 route rule exempts Mathlib leaves. The first worker's descriptions of this declaration as a required tool-use exception are superseded by this check.
- Expanded the Step 2 verbatim citation to the complete cited statement, including the small-diagram hypotheses; all seven citation records were checked against their nodes and remain verbatim.
- Recorded the three independent searches and their actual outcomes. The statement, substantive proof construction, other citations and first worker's sections are preserved.
