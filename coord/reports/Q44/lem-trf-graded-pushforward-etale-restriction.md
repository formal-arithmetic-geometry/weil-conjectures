# Stage-1 delivery: lem-trf-graded-pushforward-etale-restriction

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-graded-pushforward-etale-restriction.json`: statement, now split in six steps, with its original statement and statement dependencies retained. No Mathlib match for the whole assertion.
- `citations.json`: one verbatim statement quote for every node cited in every step.
- This report. `searches.jsonl` is the search command's own log.

New nodes: 0. New Mathlib leaves: 0. Existing nodes suffice.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for graded pushforward/direct-image and etale restriction terminology. No project declaration gives the item's entire arbitrary-algebraic-space statement. Scheme etale localization declarations and ordinary open-immersion counits do not cover it.

## WANTED

None. All sources used are available locally.

## Corrections and route

The item was statement-only, rather than a completed split; no earlier sandbox split or report existed. I preserved its statement, source, ancestry and prior search entries. No statement dispute was found. The missing work was the actual homogeneous multiplication/unit argument, the coproduct assembly, and evaluation on arbitrary scalar tensor generators, not merely on the adjunction unit.

I read the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof, together with the chapter and unit records. The current ancestor follows contracting correspondences; its current proof does not mention the historical polarized-descent branch recorded in the item's ancestry. I retained this ancestry and explicitly identified this split as the existing historical foundation through space-section-algebra-etale-base-change and Stacks 0D3C. This work makes no change to the chapter or unit route and makes no new claim that the current ancestor uses that branch. Blueprint searches for `graded direct image` and `section algebra` found no blueprint nodes stating the item; broader etale-base-change and tensor-product searches supplied no exact alternate statement. Therefore `same_as=[]`.

The existing generic localized tensor comparison and bilinear universal property are declared as tool uses in `split_report.tool_uses`. They concern all ringed sites and sheaves of modules; they replace no geometric step of this unit. The coproduct result is already a Mathlib leaf.

## Sources and searches

I read Stacks `spaces-properties.tex`, Tag 03LX (`lemma-pushforward-etale-base-change-modules`), including its pullback footnote and the preceding description of etale pullback as restriction. It imposes no quasi-compactness, separatedness, or quasi-coherence for this etale base change. I also read `spaces-descent.tex`, Tag 0D3C (`lemma-descending-property-ample`), specifically the paragraph constructing the section algebra and identifying the pullbacks of the maps psi_d. Its flat-base-change and ampleness arguments are outside this item; only their etale section/evaluation subargument is used here.

For the generic tensor input I read `sites-modules.tex`, Tag 03EL (`lemma-tensor-product-pullback`), the tensor/bilinear universal property immediately after Tag 0GMW (`lemma-sheafification-tensor`), and the localization construction, Tag 03DH (`definition-localize-ringed-site`). For coproducts I read `categories.tex`, Tag 0038 (`lemma-adjoint-exact`), part (1). This split's elementary assembly and triangle-identity calculation are written by me; `proof_origin.by=agent` records that explicitly. No SGA source is used.

The required msearch commands were run for this item with LeanFinder, Loogle, grep and LeanSearch, followed by a second semantic phrasing and a targeted grep. Their actual queries, results and dates have been appended to the retained search records. The first semantic results included scheme open-immersion counits; the second returned projective-spectrum formulas. LeanSearch returned ring-level graded actions/tensor products, etale ring base change, and `SheafOfModules.PullbackConstruction.adjunction`. I read that adjunction's source (`PullbackContinuous.lean`, declaration at line 79) and its surrounding pullback-composition constructions; it is an input for general sheaf module operations, not this graded base-change theorem. I read the open-immersion restriction/counit portion of `AlgebraicGeometry/Modules/Sheaf.lean` (counit formula at line 447); its Zariski scheme hypotheses do not give arbitrary algebraic-space etale restriction. The targeted grep returned only general continuous pushforward adjunction and colimit machinery. No result states the full item or gives it by a one-line specialization. Every newly recorded query appears in searches.jsonl; no unavailable result is called a negative search.

## Not duplicates

No new nodes were created. In particular I reused the exact existing arbitrary-module base-change node rather than making a node for its degreewise instances, reused its chart-adjunction tensor realization rather than another counit-normalization lemma, and reused localized tensor restriction and left-adjoint preservation of coproducts. Tensor powers and homogeneous products remain proof steps, not new nodes restating clauses of the item.

## Review by Q44

I checked the node files against the actual statements cited, not their proofs. I read every statement in the item's unchanged stmt_deps, including the algebraic-space definition, which defines a line module locally isomorphic to its structure sheaf, and the sheaf-tensor definition. I also read every proof input. The arbitrary-module restriction lemma expressly fixes all compatible chart sections and includes the scalar-normalized pullback comparison. The chart-adjunction realization expressly compares the specified adjunction unit with ringed tensors and gives both composition and etale scalar formulas; it is not just an abstract existence statement. The localized tensor lemma gives an isomorphism with the pure-tensor normalization for an arbitrary ringed site. The bilinear universal property is a bijection, so it detects equality, not just existence. The coproduct node preserves the colimit cocone, with its canonical comparison. Module sheafification has the required unique extension property.

Step 1 uses exactly the arbitrary-module restriction lemma with F=B_d. The base-change square is cartesian by the item's setup and g is etale, so every hypothesis holds, with no quasi-coherence or finite-type input.

Step 2 uses localized tensor restriction on scheme charts of the localized etale sites, the bilinear bijection to identify the comparisons on overlaps and in associativity/symmetry diagrams, and the chart-adjunction realization's etale formula a tensor b maps to ab for the structure unit. This checks the normalization of the actual pullbacks in the item instead of silently replacing them by some isomorphic functors.

Step 3 uses the base-change lemma's identity on compatible sections and the chart-limit definition to compare each projection of a product. Each side has the same component mu(s_T tensor t_T); the pure-tensor-normalized restriction and bilinear bijection promote that calculation to the homogeneous sheaf map. The degree-zero component is the image of the same section 1. It checks ordinary commutativity, without inserting graded signs.

Step 4 uses the specified module adjunction and the left-adjoint colimit lemma. The index is the small discrete category of nonnegative integers. The constructed isomorphism is the sum of the beta_d with inverse the sum of their inverses. The grading and algebra equalities are tested on homogeneous summands. No incorrect equality between coproduct sections and direct sums of section modules is used.

Step 5 uses the chart definition and realization to represent a local tensor by a times the projected adjunction unit. Applying the counit, the triangle f_*epsilon composed with eta = identity gives exactly a times the chart projection of s, so this computation applies to every local scalar a. The base-change node fixes that section and gives the scalar-normalized composite comparison. Both paths thus give a times s restricted to W. The cited module-sheafification uniqueness extends equality of the finite tensor sums; preservation of coproducts then tests the total equality on each summand. This is the explicit argument missing from a bare assertion that evaluation 'transports'.

Step 6 iterates Step 2 with base cases d=0 and d=1 and a specified successor comparison. The scalar products and ordered list of tensor factors are identical under concatenation, including m=0 or n=0. The bilinear bijection gives equality of the product maps. The chart realization supplies the actual degree-zero unit. No local trivialization theorem is needed: these comparisons hold even for arbitrary module sheaves, so they certainly apply to a line module.

I checked empty spaces/charts, zero module components (including the zero algebra case), identity base change, nonsurjective etale g, arbitrary non-quasi-compact f, and d=0,1. The restriction argument is local on the target and needs no surjectivity. Infinite gradings use categorical coproducts throughout. In the single-chart ring example the counit is ordinary scalar multiplication and both sides of the square agree; scalar coefficients need not be invertible or constant. I traversed the statement and proof dependencies of every cited theorem and found no return path to this item. All proof steps are below 2000 characters, and none hides a separate comparison lemma: the non-elementary comparisons are the cited existing statements.

I checked delivery-errors B--E point by point: no new unstated notion or node, no doubled TeX escapes, no unrun searches, no duplicate or relabelled clause, no use of another node's proof, no uncited non-elementary theorem, no missing geometric hypothesis, no confusion between sheaf and presheaf tensors or between a global section and its local representative. The unchanged statement is true in these edge cases; no correction of it was required.

## Unfinished work

No stage-1 work remains in this item. Existing unsplit dependencies remain their own items. No Lean was written and no compiler, Lake or build tool was run.
