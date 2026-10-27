## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-equal-dimension-isogeny-criterion.json` (statement, split; no Mathlib match). The sandbox also contains `citations.json` with the 13 verbatim step citations and the actual `searches.jsonl` log. No Lean, repository, or launcher file was written.

## New nodes

None: 0 new nodes, 0 Mathlib leaves. The source's image/kernel dimension input is already `lem-sfb-abelian-hom-image-dimension`; zero-dimensional closed-subscheme finiteness is already `lem-pc-zero-dimensional-closed-subscheme-finite`. Creating either again would duplicate existing nodes. The former is in the item's own unit. The latter is a general geometric tool from the Picard chapter, declared in `split_report.tool_uses`; it supplies Stacks 06LH without replacing the Milne argument.

## Attachments

None. Searched the live project's `lean/WeilConjectures/` by the item id, `IsIsogeny`, isogeny, and surjectivity/dimension combinations. `GroupScheme/Defs.lean:291` defines `IsIsogeny`; `AbelianVariety/Isogeny.lean:288` proves finiteness assuming an isogeny, and `:341` proves the multiplication-map case. These do not prove the converse for an arbitrary surjective equal-dimensional homomorphism. The existing translation declaration `exists_isPullback_kernel` at `:239` does not by itself supply the dimension argument. No full attachment was found.

## WANTED

None. The necessary Milne PDFs and Stacks sources are present.

## Sources and route

Read Milne, *Abelian Varieties*, Chapter I, Proposition 7.1, printed p.32 (PDF page 38), including the preceding definition, scheme-theoretic-kernel footnotes, translation-of-fibres argument, dimension formula, and proper-image argument. Our statement is exactly (a) iff (b), with equal dimensions already imposed; the final endomorphism assertion follows because a proper dense image is the entire target. We do not need the finite-flat clause (d).

Read the existing dimension-input node, then its source: Milne, *Algebraic Groups*, Theorem 1.72 and proof, printed p.29 (PDF page 41), and Theorem 5.39/Remark 5.42, printed p.108 (PDF page 120). The latter explicitly states dimension of the source equals dimension of the image plus dimension of the scheme-theoretic kernel; the former gives a geometrically reduced image from a smooth source. We only use the already-stated dimension formula, not an unrecorded identification from the node's proof.

Read Stacks `varieties.tex`, Tag 06LH (`lemma-algebraic-scheme-dim-0`, lines 3736 onward): a finite-type zero-dimensional scheme is affine and finite over its field. This is precisely the existing closed-subscheme finiteness node used in step 3. Read Stacks `morphisms.tex`, Tag 01W6 (`lemma-image-proper-scheme-closed`, lines 9949 onward): a morphism from a proper scheme to a separated scheme over the same base is proper and has closed image. Its two inputs are already Mathlib leaves in the DAG.

Read the recorded chapter and unit and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`. This small abelian-variety input stays within the inherited alteration/level-structure prerequisite route named in the item's `blueprint.from.place`. `blueprint_refs.py ancestor` returns `None` for this inherited chain; I preserve that value and its detailed place/via list. Searches of the whole imported blueprint for `isogeny`, `kernel dimension`, and `zero-dimensional` found no alternate blueprint statement of this whole criterion. The multiplication-isogeny statements do not cover arbitrary homomorphisms.

## Search results

All five original item query texts were run with the required Q156/item `msearch.py` command and their printed hits were read. The file log has successful results for every service, so no unavailable service is misreported as no match. LeanFinder's first phrasing returned scheme-surjectivity instances and finite-dimensional linear results. Its second phrasing, about a nonisogeny endomorphism's smaller image dimension, returned linear rank/determinant statements and no abelian-variety criterion. Loogle's `"IsIsogeny", "Surjective"` returned zero hits; grep's `isogeny|IsIsogeny|IsAbelianVariety` in Mathlib `AlgebraicGeometry` returned zero hits. LeanSearch returned abstract group-range and elementary scheme-isomorphism criteria. None has the required algebraic-geometric dimension/kernel content. The inherited query records were retained and their generic verdict text was made specific to this item. No query was invented.

## Corrections and unfinished work

The item was unsplit and had no proof. I retained its statement, statement dependencies, source and provenance, and supplied the argument in four steps. The equivalence is not replaced by a new node restating it. No statement dispute or source error was found. Nothing in the assigned stage-1 split remains unfinished; the existing unsplit dimension-input node remains its own item, rather than being split here.

## Review by Q156

I read every cited node's actual statement before writing its use, including all six statements used in step 2. I also generated `citations.json` by checking literal containment in those statements, rather than reconstructing a quote from the proof. This is a direct-delivery self-review; the maintainer still independently reviews the delivery.

Step 1 is the elementary forward implication. The quoted definition of isogeny contains both surjectivity and finite kernel, so it supplies exactly the surjectivity used. It requires no dimension calculation.

Step 2 uses `lem-sc-image-subgroup` for a closed image and the surjective factorization, with proper source and separated finite-type target provided by `def-sc-abelian-variety`. A closed immersion is a homeomorphism onto its image by the actual statement of `def-weil-closed-immersion`; surjectivity makes that image all of B. This only identifies the underlying spaces, not a possibly nonreduced closed subscheme with B, and suffices for equality of their topological dimensions. `lem-sfb-abelian-hom-image-dimension` states exactly dim A = dim I + dim K for arbitrary fields, without perfectness or separability. Its assertion that I is abelian allows `lem-kun-dimension-finite-type` to be applied to I as well as A. Finite dimension is essential before cancellation, so it is cited explicitly. `def-sc-group-scheme` gives the scheme-theoretic fibre-product kernel and the identity maps; the identity supplies its nonemptiness. Thus no subtraction of infinity and no empty-kernel convention occurs. I did not use a translation theorem under a nonexistent rational lift: that content is already in the cited image/kernel dimension statement.

Step 3 uses the exact closed-subgroup conclusion of `lem-sc-kernel-subgroup`. The ambient A is finite type over the same arbitrary field k. The exact statement of `lem-pc-zero-dimensional-closed-subscheme-finite` takes a closed subscheme of such an X with dimension at most zero and concludes scheme-theoretic finiteness, affineness and finite-dimensional global functions. It therefore applies to K with the zero dimension obtained in step 2. The isogeny definition then assembles surjectivity, the given homomorphism and finite kernel. This use does not replace finiteness by a finite underlying point set and does not assume K reduced.

Step 4 specializes `lem-weil-pbc-proper-to-separated` to A -> A -> Spec k, exactly the triangle in its statement; A is proper and separated. `lem-weil-pbc-proper-closed-image` supplies a closed underlying image. Dominant here means dense image. A subset that is both closed and dense is all of A, so the established equivalence applies with B=A. No claim about k-rational-point surjectivity is made.

For the B–E checklist: there are no new nodes, no proof-bearing supposedly unsplit leaves, no new notions or duplicate lemmas, and no new Mathlib-leaf claims needing line checks. TeX uses a single escape layer. All sources are present; no forbidden source route is used. Each non-elementary fact is a cited node statement, and the non-elementary steps are labelled false for `elementary`. Every proof step is shorter than 1000 characters, so no long-step lemma is concealed. All cited ids were opened; the dependency checks are left to the required server preflight as well.

Small cases checked: the identity map gives a zero-dimensional trivial kernel and is an isogeny; on a zero-dimensional abelian variety the argument still works with dimension 0 and a nonempty kernel. The zero endomorphism of a positive-dimensional abelian variety is neither surjective nor dominant and has positive-dimensional kernel. In characteristic p, multiplication by p may have a nonreduced kernel: the proof uses scheme dimension and scheme finiteness, so it still applies and never assumes etaleness or separability. The arbitrary-field hypothesis is preserved throughout; surjectivity is on underlying scheme points, not on k-points. These checks required no statement correction.

The first dry run required a longer citation excerpt for the finite-dimension lemma. I replaced the short formula by that node’s whole statement; the proof and its hypotheses were unchanged.
