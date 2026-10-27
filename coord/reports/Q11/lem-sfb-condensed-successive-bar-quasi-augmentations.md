# Worker report: lem-sfb-condensed-successive-bar-quasi-augmentations

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-successive-bar-quasi-augmentations.json: statement, split; existing Mathlib searches preserved and seven actually executed Q11 searches appended; no Mathlib match.
- citations.json: 17 verbatim statement quotations, one for every cited node in every proof step.
- report.md and searches.jsonl: this report and the unmodified search-command log.

No new nodes and no Mathlib leaves. The eight-step proof reuses the existing injective bar rows rather than creating parameterized copies of them. The statement, statement dependencies, source, created record and existing blueprint ancestry are unchanged. No unit realization fields apply: this item is not a unit's key statement.

## Attachments

None. Searches in lean/WeilConjectures/ for the exact blueprint tag, successive/internal bars and condensed invariants found no declaration giving all the clauses. The condensed ring files in the source construct coefficient objects, not this bar comparison. No sorry declaration has been treated as a completed proof.

## WANTED

WANTED: an independent reference specifically treating ordinary internal condensed-module group bars with arbitrary profinite parameters and the successive augmentation maps; exact document and theorem/place not identified, for lem-sfb-condensed-successive-bar-quasi-augmentations. The current blueprint paragraph (3) supplies the geometric context but does not prove this formal condensed input. The proof is consequently marked agent-written, not attributed to Bhatt–Scholze or to a discrete representation theorem. The totalization input does have the precise available source: literature/stacks-project/homology.tex, Tag 0133, lemma-double-complex-gives-resolution, with Tag 0132, lemma-first-quadrant-ss.

## Findings and corrections

The imported item was unsplit. Its statement is retained verbatim. The main possible false inference would be to apply internal Hom to an exact H bar without an exactness hypothesis. Instead step 2 uses the existing sectionwise injective-bar theorem at S times G^a. It supplies exactness at that whole parameter; no exactness or projectivity of A[G^a] is asserted. Similarly, the H-invariants complex is used as the K-injective representative of derived H-invariants, not incorrectly as an injective resolution of underived N^H.

The order of totalization requires a sign correction. Grouping (a,q) and totalizing b first gives delta_H + (-1)^b delta_G + (-1)^(a+b)d_q. Step 7 writes the cochain isomorphism (-1)^(ab) to the required order, checks all three arrows, and checks that it fixes the actual b=0 inclusion. A comparison of unnamed cohomology objects would not establish the requested arrow.

The blueprint ancestor helper returns None on this preexisting created chain. I retained blueprint.from.node=null and its recorded via list, filled no invented ancestor, and recorded the specific paragraph (3)/parent steps 5–7 in split_report.blueprint. Whole-blueprint searches for homogeneous bar, successive bar and injective bar returned no matching blueprint node. The inherited chapter/unit placement is retained.

## What remains unfinished

No part of the stage-1 split remains unfinished. The cited existing DAG lemmas remain their own items; their statements, not unrecorded material from their proofs, are used here. No Lean, compiler, Lake, repository mutation, source download or sub-agent was used.

## Mathlib searches

Seven Q11 searches were run through the mandated msearch.py and recorded exactly as returned in searches.jsonl. They comprise two LeanFinder phrasings, two LeanSearch phrasings, Loogle `"quasiIso", "invariants"`, a whole-Mathlib grep for bar augmentations/injective invariants, and a second grep under Condensed. Both semantic phrasings were read. The first finds Rep.standardComplex augmentation results and generic injective resolutions. The second finds ordinary Rep.barResolution, abstract group-cohomology exact sequences, and generic quasi-isomorphism composition statements. The Condensed grep hits are bibliographic mentions of Barwick, not bar complexes.

I read Mathlib/RepresentationTheory/Homological/Resolution.lean:270–325, especially quasiIso_forget₂_εToSingle₀ at line 306 and the instance at line 312, and GroupCohomology/Basic.lean:138–166, inhomogeneousCochainsIso at line 148. These are over an ordinary commutative ring and abstract group in Rep; they do not specialize in one line to internal condensed actions, profinite-parameter sections, or the two augmentation maps in this statement. All services answered; none was logged as unavailable. Existing imported searches were preserved.

## Not duplicates

No new node was created. The parameterized H row is an application of lem-sfb-condensed-injective-bar-rows at S times G^a; the G row is a second application of the same node. The two total arguments reuse lem-sc-first-quadrant-column-augmentation. The finite sum and sign calculation are steps of this proof, not extra nodes. I also read lem-sfb-condensed-product-bar-resolution-model, lem-sfb-condensed-bar-total-augmentation, lem-sfb-pointed-free-deletion-contraction and the parent product comparison, and did not duplicate their statements.

## Review by Q11

I read coord/brief-stage1.md, stages/1-dag.md, the human's three blueprint levels in SETUP.md, GOAL.md, the chapter and unit records, and delivery-errors B–E in full. The source for the item is the current main-20261015 direct-images proof paragraph (3), read in its file. It only names the open direct-image step, so the formal assembly below it is explicitly agent-written. There is no new node with a missing source. For the generic total comparison I read the actual Stacks proof and hypotheses at Tag 0133 and the adjacent convergence lemma 0132, and checked the tag-to-label table.

For step 1 I opened lem-sfb-condensed-action-injective-restriction and lem-sfb-condensed-product-action-inflation. The former explicitly says Res_H I^q and (I^q)^H are injective and that (I^bullet)^H is K-injective and represents derived H-invariants. The latter explicitly supplies Grothendieck abelian categories. I corrected the citation audit so this abelian-category assertion has its own citation, rather than relying on an implicit assumption in the restriction lemma.

For step 2 I opened the statements of lem-sfb-condensed-injective-bar-rows, lem-sfb-condensed-free-linearization-tensor and lem-pc-sheaf-modules-tensor-closed. The first explicitly gives exactness on every profinite section parameter and the homogeneous equivariant Hom presentation, not just internal exactness. The second explicitly identifies A[X] tensor A[Y] with A[X times Y] and detects maps by generalized generators. The third gives the closed tensor-Hom adjunction. Together with evaluation of the free adjunction on the identity of S, these give the displayed section identifications with no appeal to an unasserted construction inside a cited proof. S times G^a is profinite in the same fixed universe. The augmentation term and the Hom complex carry trivial H-actions on both parameter factors as required.

For step 3 the bar-row statement explicitly gives the homogeneous-to-inhomogeneous formula, the action first face, every other face and degeneracy, and naturality under profinite base change. I wrote out why its coefficientwise residual G action commutes with h_0 and why the first G and H faces commute: the two group factors commute in their product action. The restriction lemma explicitly reflects exactness, so sectionwise exactness gives the equivariant exact complex. Compatibility with d_q follows from equivariance of the resolution maps; parameter operations in disjoint directions commute. This does not claim that the G coface itself is equivariant for a coefficientwise G action.

For step 4 the same bar-row statement applies because (I^q)^H is injective in the G action category. Its initial term is ((I^q)^H)^G. The product-inflation statement explicitly identifies that module, by the identity and with its inclusion, with (I^q)^(G times H). Thus the augmentation is the one stipulated in the item, not an unspecified isomorphism in degree zero.

For steps 5 and 6 I read lem-sc-first-quadrant-column-augmentation: it asserts a quasi-isomorphism for the actual chain map supported in first index zero, assuming each augmented row is a quasi-isomorphism. For step 5 the indices are (a,q); for step 6 they are (b,r), r=a+q. I verified nonnegativity, finite sums, annihilation by the next bar differential and compatibility with the other differential in both applications. The finite sum exactness is written componentwise on sections, including its preimage argument. The cited definition def-sp-double-complex-total explicitly supplies the finite-diagonal differential convention. The off-unit total criterion and closed adjunction are declared in split_report.tool_uses as generic tools; they replace no geometric unit route.

Step 7 is an elementary calculation and cites no hidden comparison lemma: all three exponents are displayed, the same signs give the inverse, and their restriction to b=0 is one. All eight steps are below 2000 characters, and the finite regrouping and sign comparison introduce no independently hypothesized hidden lemma.

For step 8 I reread sk-def-sfb-derived-categories: quasi-isomorphisms are inverted and ordinary right derived functors are computed on K-injective resolutions. The restriction lemma supplies the needed K-injective representative before applying G-invariants. The product-inflation statement identifies the resulting actual complex with J. This establishes derived-object identifications with the specified augmentations, without reducing them to degreewise cohomology equalities.

I tested the boundary cases a=0, b=0 and q=0, empty S, zero ring, zero coefficient module, G=1 and H=1. For a trivial group the unnormalized cochain terms persist: the differentials alternate 0 and identity, so the exact-row argument remains applicable. A resolution of zero need not be the zero complex, but the cited injective-resolution assertions still apply to it. No hypothesis excludes these cases. Statement and all statement dependencies were compared with the live item and retained. Every step-use has a quotation in citations.json that is an exact substring of the cited live statement. The union of those uses equals proof_deps. No new statement is elementary, a duplicate, a clause relabeling, or an unexamined Mathlib match, because no new statement node was needed.


## Returned delivery repair (2026-10-22)

Return L refused landing because the statement of lem-sfb-condensed-free-linearization-tensor moved after the review. I continued the retained delivery (ready record e88cac595a1), rather than replacing its proof or search history. Compared with the current live item, the statement, statement dependencies, source, ancestry and created record still agree; the live item remains unsplit. The required initial dry run exited with one diagnostic: the step-2 free-linearization quotation was no longer a verbatim substring. The current statement inserts the explicit citation [lem-pe-internal-section-tensor-comparison] into the sentence about sheafifying the tensor maps, and names the section-tensor and free-module notions explicitly. It retains the same canonical maps and all their generator normalization, naturality and coherence assertions. These are the substantive inputs step 2 needs, so no hypothesis or conclusion of this item changes.

I reread the current statements of all eight proof dependencies, not only the node named by the return. All other 16 step quotations still occur verbatim. In particular, the injective bar rows still assert sectionwise exactness at arbitrary profinite parameters; the restriction lemma still supplies both injectivity and the K-injective representative; and the totalization criterion still concerns the actual degree-zero augmentation. Step 2 now explicitly uses the free-linearization node's generalized-generator assignment and its compatibility with the underlying-sheaf-preserving internal-to-section equivalence before transporting the closed tensor-Hom adjunction. The equivalence is used for morphism bijections and the canonical tensor comparison; no sectionwise freeness or sectionwise surjectivity of sheafification is inferred. I replaced the stale quotation with the current verbatim text including the named tensor-comparison citation. The node files of dependencies are read only and are not bundled or overwritten.

This revalidation preserves the eight-step argument, the specified augmentation maps and all total signs. The parameter S times G^a stays in the same profinite universe, including a=0 and empty S; the current tensor statement permits arbitrary condensed sets and the zero ring. I rechecked b=0, trivial groups and zero coefficients against the row formulas and the sign computation. There are still zero new nodes and zero Mathlib leaves. I read the retained seven-search log and reused its results, because neither the item statement nor its Mathlib search question changed. The report, original searches and all prior proof arguments are retained. No agents, Lean compilation, repository git commands or launcher changes were used.
