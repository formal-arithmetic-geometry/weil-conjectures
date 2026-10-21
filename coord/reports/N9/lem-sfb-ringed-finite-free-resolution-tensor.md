# Stage-1 report: lem-sfb-ringed-finite-free-resolution-tensor

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-ringed-finite-free-resolution-tensor.json`: statement item, seven proof steps, status split; Mathlib searches found no exact match or one-line specialization.
- `citations.json`: 14 entries, one per cited node per step, with verbatim substrings of the cited statements.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log. `split_item.py` is a sandbox-only writing script, not a delivery node.

No new nodes and no new Mathlib leaves. No Lean files, unit records, repository files or launcher files were written. The sandbox initially contained no item, proof or report, so the live unsplit item was copied. Its statement, source, provenance, statement dependencies and pre-existing Mathlib searches were retained. Only split-owned fields were set.

## Attachments

None. A search under `lean/WeilConjectures/` for the exact id/docstring tag returned no declaration. Concept searches found ModuleCatFiniteResolution (ordinary modules, not sheaves on arbitrary sites), TensorResolution (pro-etale A-valued sheaves, without the supplied finite-coordinate and augmentation clauses), MonoidalFree (free tensor free, without resolution and arbitrary N), and the generic K-flat modules. Reading these does not give a project declaration of every clause under the item's hypotheses. Therefore this is a split, not an attachment. Sorry-bearing upstream proofs were not counted as finished proofs.

## WANTED

None. All sources needed here are already in `literature/`.

## Problems and changes

The mathematical statement is retained in full. There is no statement dispute or established source error in this item. The original item had no proof. The important C4 risk was to use `lem-weil-pbc-site-derived-tensor-descent` as though it directly gave computation with arbitrary N: its displayed comparison only covers two flat-term K-flat representatives. I instead cite the existing `lem-weil-pbc-kflat-fixed-tensor-triangulated`, whose statement explicitly allows every other complex and identifies both resulting derived functors. This avoids an unjustified flatness hypothesis on N and avoids creating a duplicate one-sided-computation node.

The three generic structural tools are declared with reasons in `split_report.tool_uses`; no maintainer-owned top-level `tool_uses` was set. They supply site bounded-flat K-flatness, ordinary sheaf tensor symmetry, and one-sided K-flat tensor computation. The unit's Local models route is followed. This auxiliary item is not the statement of the unit, so its still-unfilled realization fields were not edited.

The prior item's search records are preserved; six searches were actually run for this item in N9 and appended with the same tool and query strings. Both semantic phrasings were read. LeanFinder returned module-level flat exactness and projective Tor, and LeanSearch returned free sheaves, Cartesian sheaf tensor and projective Tor. Reading Mathlib `Sheaf/Free.lean` and `CategoryTheory/Monoidal/Tor.lean` confirmed that free sheaves are a construction and Tor assumes projective resolutions; neither states the asserted unbounded K-flat ringed-site formula. Loogle returned quasi-isomorphism/localization and truncation lemmas. Two grep patterns found no K-flat/derived-tensor sheaf-resolution declaration. Every service answered, so no failure was recorded as absence.

## Not duplicates

No new node was created. Whole-DAG tag/concept searches and whole-blueprint searches (`finite free`, `K-flat`, `06YQ`) found existing bounded-flat, tensor-structure and derived-tensor nodes, which are reused. None of the blueprint matches states the whole supplied-resolution, matrix and augmentation assertion; `blueprint.same_as` remains empty. The nearest blueprint ancestor is `det-def-localizing-closure-ctf-equals-bc`, and the existing exact Local models place and via chain were retained.

## Review by N9

I read `coord/brief-stage1.md`, the stage-1 contract, SETUP's three levels, GOAL, the item's chapter and unit, and delivery-errors B–E whole. For the item's source I read the current blueprint's `sk-def-localizing-closure-ctf-equals-bc.proof.md`, especially Local models, and Stacks `sites-cohomology.tex`: 06YQ/lemma-bounded-flat-K-flat, 06YP/lemma-K-flat-quasi-isomorphism, 06YS/lemma-K-flat-resolution, and 06YU/definition-derived-tor with its surrounding construction and symmetry. I also read `sites-modules.tex` Section 03EK and 03EO, and the DAG's explicit flatness, total-complex, quasi-isomorphism and cohomology statements. There are no new nodes needing additional sources.

For each step I opened the cited node and checked its actual statement, not its proof:

1. `def-pur-sheaf-tensor-product` says exactly that tensor is sheafification of sectionwise tensor. `def-weil-presheaf-modules-sheafification` gives the universal factorization needed to descend the coordinate map and its identities. I wrote the inverse and both composites; no stronger sheafification description is assumed. This proves the finite-coordinate identity directly, without a new node.
2. `def-weil-sheaf-of-modules-category` supplies the abelian category. The elementary finite-biproduct kernel and cokernel universal-property argument makes finite powers exact. `def-pc-flat-sheaf-modules` defines flatness by exactly this tensor exactness. I do not claim epimorphisms of sheaves are sectionwise surjections.
3. `lem-weil-pbc-independent-bounded-flat-kflat` explicitly covers bounded-above flat complexes on essentially small ringed sites, without points. K is bounded above by b and has flat terms by step 2. The cited site definition makes objects and arrows sets, so the common coefficient-universe convention supplies essential smallness. There is no attempt to substitute the ringed-space-only bounded-flat lemma or to use the general monoidal version without its colimit hypotheses.
4. `lem-pc-sheaf-modules-tensor-closed` supplies the ordinary module-induced symmetry, and `def-pc-tensor-complex-sheaves` gives the displayed signed total differential. I checked both coefficients of the cochain-map equation and the square of interchange. The result is an explicit elementary signed map, not an unproved comparison lemma hidden behind the word transport.
5. `lem-weil-pbc-kflat-fixed-tensor-triangulated` really states preservation of every quasi-isomorphism and identifies the descended fixed-tensor functor with the derived tensor. Its hypotheses are K-flatness and flat terms of K only, both established. `def-weil-abstract-derived-category` says Q inverts quasi-isomorphisms, which justifies inverting the given Q-epsilon. The three maps and their directions are written out, ending in the scalar-first total tensor, using the signed interchange of step 4.
6. `def-pc-tensor-complex-sheaves` has exactly the bidegree-(0,i) term and differential used. The two adjacent gammas cancel in delta-squared; the matrix formula is expanded on basis vectors and pure tensors. No cohomology-tensor interchange or stalk argument enters.
7. `def-weil-abstract-derived-category` states cohomology as kernel modulo image, `def-weil-sheaf-of-modules-category` gives its abelian ambient category, and `def-pc-quasi-iso-modules` defines the required isomorphism in every degree. The exact-sequence hypothesis gives kernel f zero and cokernel f equal to M via the specified g, so these are the actual augmentations. The degree-zero isomorphism case is even a cochain isomorphism. These checks do not replace the specified matrix by a chosen resolution.

I verified the C1 list: the non-elementary facts are the three cited generic tools; the remaining deductions are written elementary algebra or universal-property calculations. I verified C4 by checking all 14 quotes verbatim against the live statements. I corrected the last step's cohomology quotation to quote the cohomology formula itself. Each step is under 1000 characters; no non-elementary step exceeds 2000 characters or hides a separate lemma.

I tested zero ranks, the zero ring, N=0, the empty/degenerate site, a degree-zero resolution, a two-term resolution with m=0 or n=0, and an arbitrarily long negative tail. All sums in the coordinate formula are finite, the zero-rank maps are the unique zero-object isomorphisms, and only boundedness above is used. For a nonflat test take the singleton site with B=Z, M=N=Z/2 and K=[Z --2--> Z]: tensor gives [Z/2 --0--> Z/2] in degrees [-1,0], as required, so the argument has not erased Tor or assumed N flat. The sign check also works in characteristic two, where minus signs coincide. No new false statement, added hypothesis, weakened conclusion, SGA source, or different coefficient category was introduced.

The preliminary server `review_split` returned PASS with zero new nodes. It noted that the unit has no realization recorded yet; this is an existing unit-level condition outside this auxiliary item's remit. The required full dry run and push are performed after writing this report.

## Unfinished

No part of this one-level split is left unfinished. Existing cited nodes retain their own statuses and future work. Maintainer independent review remains the normal next stage after delivery.
