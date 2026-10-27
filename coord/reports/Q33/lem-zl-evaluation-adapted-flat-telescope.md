# Worker report: lem-zl-evaluation-adapted-flat-telescope

1. Files written: `dag/nodes/sec-zeta-weil/lem-zl-evaluation-adapted-flat-telescope.json` (statement, split; no exact Mathlib match). Supporting sandbox files: `citations.json`, `searches.jsonl`, this report. No new nodes, no new Mathlib leaves.
2. Attachments: none. The project search for the exact blueprint tag and for evaluation-adapted / flat-telescope notions found no declaration proving the whole item. Existing Lean declarations for the tower, telescope comparison and closure prove ingredients only and are reused through their existing DAG nodes.
3. WANTED: none.
4. The imported item had no proof. Its statement is unchanged. It is true under its stated smallness, exactness, colimit preservation and flatness preservation assumptions. Independent bounded flat replacements would not give strict transition compatibility; the existing tower node gives exactly that compatibility. No unit-route error or source error was found.
5. Unfinished: none in this one-level split. The dependencies retain their live statuses; none was re-split. No Lean, compiler, Lake, or local DAG/preflight check was run.

## Sources and searches

Read Hemo–Richarz–Scholbach, *Constructible sheaves on schemes*, arXiv:2305.18131, Lemma 4.1(1) and its proof, from the local PDF: the source asserts the unbounded monoidal sections functor. This item expands the chain-level flat-model ingredient of that argument; it does not claim the paper itself states this telescope lemma verbatim. Read the Stacks source `sites-cohomology.tex`, Tag 077J (`lemma-resolution-by-direct-sums-extensions-by-zero`) and Tag 06YS (`lemma-K-flat-resolution`), together with 06YQ, 06YR and 07A3. Read `derived.tex`, Tag 0949 (`lemma-colim-hocolim`), and `homology.tex`, Tag 010N (`lemma-exact-functor`). No SGA source is used.

Read the chapter and unit records and SETUP's three-level rule. This is a generic homological tool below the fixed smooth-proper-purity route; it changes no chapter, unit or target. Whole-DAG searches for 077J/06YS, compatible flat towers, telescopes and K-flat closure found the existing picard-framework nodes used below. Blueprint searches for `K-flat`, `K-flat resolution`, `flat truncation`, `evaluation telescope`, `telescope`, `exact evaluation` and `flat complexes` found no equivalent blueprint statement for the whole item. Its `same_as` remains empty and its existing precise ancestor place is retained.

Ran the required msearch command under Q33/item for LeanFinder, Loogle, grep and LeanSearch. Read every result, and ran a second LeanFinder phrasing and second source grep. The search logs and exact queries are preserved; all services answered. The LeftResolution source was opened: it constructs ordinary resolutions from an existing resolving functor, not this compatible unbounded tower with its evaluated K-flatness. Truncation functors, representably-flat Kan extensions and module flatness criteria do not state the whole item. The previous item's recorded Q27 searches remain untouched; the new Q33 searches are appended.

## Not duplicates

No new nodes were created. The existing `lem-pc-flat-truncation-tower`, `lem-pc-complex-hocolim-colimit`, `lem-pc-kflat-hocolim-truncations`, `lem-pc-kflat-closure` and `lem-sp-exact-functor-preserves-homology` supply all needed non-elementary facts.

## Review by Q33

I read each cited node's statement, not just its proof or source tag, and wrote a verbatim quotation for each of the seven step citations in citations.json.

Step 1 uses the complete statement of lem-pc-flat-truncation-tower: it supplies natural-number indexing starting at zero, bounded-above flat terms, termwise epic quasi-isomorphisms, and strict compatibility into K. Its small ringed-site hypotheses hold in the module universe fixed by this item. Tag 077J gives a stronger tower with split-injective transitions, which this proof does not need. The argument never substitutes arbitrary unrelated resolutions.

Step 2 uses the actual cone convention in def-weil-abstract-derived-category. I checked the matrix differential and the equality a(1-s)=0 on every coproduct injection; together these prove the chain-map equation for the displayed zero shifted component. Thus no cone extension or unspecified homotopy is being assumed. All other operations here are the coproduct universal property and addition of module maps.

Step 3 uses lem-pc-complex-hocolim-colimit exactly for its canonical map from the cone of 1-shift to the termwise colimit of a sequence of module-sheaf complexes. It assumes neither flatness nor injective transitions. The component calculation identifies the composite with this item's specific p, rather than merely proving that some map P to K is a quasi-isomorphism.

Step 4 uses only the final, filtered-colimit-of-quasi-isomorphisms assertion of lem-pc-kflat-hocolim-truncations. I checked that compatibility into K descends to compatibility of q_n with truncation transitions by the monomorphism of each good truncation into K. The degreewise eventual equality is used for n strictly greater than i; at n=i the term is ker(d^i), not K^i. The bound max(0,i+1) covers negative degrees too. This establishes both comparison quasi-isomorphisms and their composite, without relying on the unrelated first clause about a truncation homotopy colimit.

Step 5 uses all the relevant clauses of lem-pc-kflat-closure: bounded-above flat complexes are K-flat; countable sums and cones preserve K-flatness; countable sums of flat sheaves are flat. The degreewise cone terms are two such sums. Reindexing their direct sum by the disjoint union of two countable sets is elementary and proves termwise flatness separately; K-flatness alone would not prove it.

Step 6 uses the same closure node on the one-object category with trivial topology and ring A. Its sheaf modules and tensor product are literally the usual module data. I checked that evaluation preserves the vanishing upper bound and term flatness by the stated hypotheses. The coproduct comparison sends each evaluated injection to the designated module injection, so it conjugates the shift to the shift with E(t_n). Applying the additive functor to the cone matrix gives an isomorphism of complexes, with its differential signs, rather than only an identification of graded terms. The rest is the cited bounded-flat, sum and cone closure. No claim about arbitrary K-flat images, and no tensor-monodality assumption on E, is used.

Step 7 uses clause (c) of lem-sp-exact-functor-preserves-homology, which explicitly gives a natural homology comparison for any exact additive functor between abelian categories. Evaluation is additive by its definition and exact by hypothesis. Naturality gives the exact comparison for E(p), and applying a functor to an inverse proves it is an isomorphism. This avoids citing a definition of exactness for an unrecorded derived comparison theorem.

I tested K=0, complexes concentrated in one degree (including negative degree), and identity evaluation on the one-object site. None requires a uniform upper bound in n. Non-injective transition maps are allowed by the telescope comparison, and the construction and cone formula still apply. I checked the zero coefficient ring as well: all terms and comparisons become zero complexes. All indexing categories used here are countable and small in the fixed universe. All proof steps are below 2000 characters; there is no long step hiding an independent lemma. The non-elementary homological ingredients are all existing nodes; the explicit cone and evaluation calculations are short applications of definitions.

The four picard-framework lemmas are declared as generic off-unit tool uses in split_report, with their purposes, for the maintainer to judge. The exact-functor homology node is already a Mathlib leaf. I corrected no mathematical statement: the repairs are to the missing proof, in particular strict compatibility, the strict truncation bound, and the actual canonical comparison map.
