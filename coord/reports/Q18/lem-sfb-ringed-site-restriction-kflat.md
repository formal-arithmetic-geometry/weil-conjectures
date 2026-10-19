# Stage-1 report: lem-sfb-ringed-site-restriction-kflat

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-restriction-kflat.json`: statement, split; not a Mathlib leaf. Five proof steps following Stacks Tag 0E8K, with the source statement unchanged and all inherited metadata and searches retained.
- `citations.json`: 11 entries, one for each step/node pair, with verbatim excerpts of the current cited statements.
- `searches.jsonl`: five actual Q18 searches recorded by msearch.py. The item also retains its five original Q63 search records.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file was changed.

## Attachments

None. Searched the slopmaster2 project under WeilConjectures for the exact blueprint id and restriction/K-flat terminology, and read the relevant module-site source paths. No project declaration states exact module restriction together with preservation of arbitrary unbounded K-flat complexes on every ringed-site slice. In particular the source's unrelated restriction of the localization functor to K-flat objects does not state this item. The read-only master search likewise supplies no attachment; its sorry declarations would not establish one.

## WANTED

None. All sources used are present in literature/stacks-project.

## Problems found and repaired

The imported item is mathematically correct and matches Stacks Tag 0E8K, `lemma-restriction-K-flat`, with exact restriction explicitly included. It had no proof. The delivered proof reuses existing arbitrary-ringed-site nodes instead of introducing duplicate exactness, reflection or tensor-projection lemmas. The claimed generality includes complexes whose terms are not flat: no termwise-flat replacement is made.

The brief's generic ban on changing statements does not require an exception here: no statement dispute or change was necessary. The current blueprint ancestor is `lem-sfb-module-mapmod-pullback-kflat`, through `lem-sfb-ringed-site-kflat-stalk-criterion`; its unit is `sk-prop-sfb-module-derived-factorization`, clause (2). This split supplies the already prescribed local restriction tool in that route.

## Mathlib and duplicate searches

Ran msearch.py, using this item's id, with LeanFinder, Loogle, grep and LeanSearch, and tried a second semantic formulation with LeanFinder. All five completed successfully; none was marked unavailable. Read every returned hit. The first semantic search found ordinary module localization/flatness and flat scheme morphisms. LeanSearch also found module restriction for schemes, limits of module sheaves and global sections; none concerns K-flatness on an arbitrary ringed site. The second LeanFinder search found good tensor-associativity hypotheses, Tor, and `HomologicalComplex.extend_exactAt`; the last extends a complex's index shape, not sheaves along a localized site. Loogle and the targeted Mathlib grep returned no hits. Thus none is an exact match or one-line specialization for the item.

Searched the whole DAG by the Stacks tag and restriction/K-flat terminology and the whole blueprint using blueprint_refs.py (`restriction K-flat`, `0E8K`, and the broader `K-flat` and `restriction` searches). No blueprint node states this arbitrary-ringed-site assertion in another form, so `blueprint.same_as` remains empty. Read the existing open-scheme restriction nodes: their object is an open immersion of schemes and their coefficient is the structure sheaf, so they do not replace this general-site item. Reused the existing ringed-slice tensor and exactness interfaces without changing them.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs requiring a duplicate distinction.

## Review by Q18

I read the chapter and unit records, the current blueprint ancestor text, and Stacks `sites-cohomology.tex`, Tag 0E8K (`lemma-restriction-K-flat`), including its full proof. I also read Definition 06YN (`definition-K-flat`) and the total tensor setup in the same flat-resolutions section. For the tools I read `sites-modules.tex`, the localization definition (`definition-localize-ringed-site`, Tag 04IX), the extension adjunction (`lemma-extension-by-zero`), exactness (`lemma-extension-by-zero-exact`, Tag 03DJ), preservation/reflection of exact triples (`lemma-j-shriek-reflects-exactness`, Tag 0E8G, including its proof), and the tensor projection formula (`lemma-j-shriek-and-tensor`, Tag 0E8I, including its Hom proof). There are no new-node sources to review.

For step 1 I opened `lem-pur-site-restriction-module-adjunction-exact` and checked its actual statement: it asserts exact restriction of module sheaves, exact extension by zero, and the natural module Hom adjunction on an arbitrary ringed-site slice. It applies with the given commutative ring sheaf R and the specified R_U; it is not merely a statement for abelian sheaves or an open subscheme. This proves the first clause and fixes the same extension-by-zero functor used by the two other tools.

For step 2 I opened `def-pc-acyclic-complex-modules`, `lem-weil-pbc-ringed-slice-extension-exactness` and `def-pc-kflat-complex`. The first explicitly equates acyclicity with exactness of all consecutive triples, the second explicitly preserves exactness of each such triple, and the third explicitly quantifies over every acyclic complex with the order test-complex tensor K. Thus LG is an allowed test complex for the given K-flat K; no claim that G has flat terms or that restrictions of global test complexes exhaust slice complexes is used.

For step 3 I checked that the cited adjunction is natural in its module arguments and that `def-pc-tensor-complex-sheaves` states existence of module direct sums. The three Hom bijections are just the adjunction and the coproduct universal property. They identify L of the direct sum, together with the images of the coproduct injections, as a coproduct. This is a few-line universal-property argument, marked elementary and kept as a step rather than a new lemma. It requires only small sums. The diagonal subsets of Z squared are small in the chosen coefficient universe, and C/U is small because C is; the original small-site hypotheses suffice.

For step 4 I opened `lem-weil-pbc-ringed-slice-extension-tensor` and read its statement, not only its proof. It gives exactly the sheafified extension-by-zero tensor isomorphism for arbitrary modules and is natural in both variables. I checked `def-pc-tensor-complex-sheaves` gives the direct-sum total, with coefficient (-1)^p on the second differential. The proof applies the isomorphism separately to every (p,q), writes the comparison in each degree, and checks both differential components by the two naturality assertions. The additive functor L preserves addition and the sign, and the coproduct comparison respects injections. This verifies a chain isomorphism, not merely a degreewise identification. This is the single routine bidegree calculation in the source's displayed equality; it hides no separately quantified comparison result. The step is 978 characters, and every proof step is below 2000 characters.

For step 5 I again checked the exactness interface's statement includes the reverse implication for every complex of three modules. Applying it separately to the consecutive triples of A recovers all the exactness needed on the slice. The acyclic and K-flat definitions then give precisely the desired conclusion for every acyclic G. This uses neither enough points nor a subcanonical topology, neither boundedness nor termwise flatness, and neither a fully faithful extension functor nor an identity j^*j_! = id. For a general site object such an identity is not available, so using the existing reflection statement matters.

I tested the proof on the terminal site (restriction at its unique object is the identity), on the zero complex and zero ring sheaf, and on a general slice object that is not subterminal. In the latter case the proof still uses only the extension adjunction and reflection, never a false full-faithfulness claim. A two-term identity complex M -> M is contractible and K-flat even for M = Z/2 over Z: tensoring it with any complex is contractible. This small case checks the explicit absence of a flat-terms assumption. For genuinely unbounded complexes the diagonal terms remain countable direct sums; no infinite products or bounded-support hypothesis have slipped into totalization.

Against delivery-errors B–E: no new nodes can violate B1–B2; every notion in the unchanged statement retains its definition dependency (B3); all inserted mathematics uses TeX with ordinary single backslashes after JSON decoding (B4); sources specify Stacks tags and labels (B5); no Mathlib match is claimed without its statement (B6, B8); the meaning is written out rather than delegated to a tag (B7); the original blueprint ancestry is preserved and its place is specific (B9). The project-source search rules out an attachment (B10). Every non-elementary input occurs in a step's uses and is quoted from its statement in citations.json, not from its proof (C1–C4). No new duplicate, self-reference or ancestor dependency was introduced (C5–C6). The three off-unit statement tools are declared in split_report.tool_uses with reasons; they are the generic ringed-site interfaces explicitly needed by Stacks 0E8K, not a replacement for a unit step (C7–C8). The five steps give the extension/tensor/reflection argument rather than moving the item's conclusion into another node (D1–D3), with all universal-property and differential details written (D4–D5). The hypotheses, exact coefficient rings, signed differentials and potential slice/full-faithfulness confusion were checked as above (E1–E6); no source error was found (E7).

## What remains unfinished

Nothing within this one-level stage-1 split. Existing cited nodes retain their own status and proofs. No Lean was written and no compiler, Lake or build tool was run. The required server dry run and final push are the delivery validation steps.
