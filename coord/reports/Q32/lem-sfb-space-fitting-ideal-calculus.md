# Q32: lem-sfb-space-fitting-ideal-calculus

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-fitting-ideal-calculus.json`: existing statement, now split into six proof steps; no exact Mathlib match for the item.
- `citations.json`: 26 verbatim statement quotations, one for every step/dependency pair.
- `report.md`: this report. `searches.jsonl` records the five Q32 searches actually run. `write_split.py` is a sandbox-only drafting artifact, not a proposed project file.

New nodes: **0**. New Mathlib leaves: **0**. The existing Mathlib leaf `lem-pc-fp-module-base-change` is reused. Statement and statement dependencies are unchanged; all original fields, blueprint provenance and inherited search records are retained. There was no prior sandbox node or report to recover, and no repair note for this item.

## Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint tag, Fitting-ideal names and kernel/presentation terminology found no project declaration of this item. The `Sheaf/` material includes ring kernel-row Fitting ideals, not the algebraic-space theorem. In particular those declarations are not grounds for an ATTACH disposition. The inherited item has no finished Lean attachment.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## What was wrong or incomplete

The item was statement-only and had no proof. Its statement correctly uses the image of the pulled-back ideal, and correctly includes the rank-zero determinant convention; neither needed correction. Its inherited Mathlib queries mentioned direct sums, but its actual current statement has no direct-sum clause. The new searches address this statement. No statement dispute or change of route was necessary.

The inherited `blueprint.from.node` is null: `tools/blueprint_refs.py ancestor lem-sfb-space-fitting-ideal-calculus` reports `None`. I retained the existing provenance, including its long prerequisite chain and the precise final Tag 087B construction input. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its proof: compactification remains the direct-image route. This small commutative-algebra/chart construction does not replace any chapter or unit argument. This item is not the unit's key statement, so no realization fields were edited.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. Searches over the whole DAG and `tools/blueprint_refs.py search` for fitting, Fitting ideal, maximal minors, and 03LZ led to reuse rather than duplication. In particular:

- `lem-trf-fitting-ideal-independence-base-change` already gives the ring theorem for all indices and arbitrary ring homomorphisms.
- `lem-trf-fitting-ideal-sheaf-pullback` already gives the scheme construction, affine characterization and pullback. It does not itself state the theorem for algebraic spaces, so it is used to build the chart family.
- `lem-sfb-space-qcoh-cartesian-chart-family` already gives the exact object-and-map gluing needed here.
- `lem-sfb-space-qcoh-affine-chart-calculus` already gives chartwise exactness, image computations and finite-presentation/finite-type tests.
- `lem-trf-split-tensor-quotient-finite-fitting` concerns two special split quotients. Its special hypotheses are unnecessary here; the two-line determinant expansion in step 3 is elementary and was not made into a duplicate general lemma.

## Mathlib searches

I ran the required wrapper with Q32 and this item's name: LeanFinder on the complete space theorem; Loogle `"Fitting"`; grep `([Ff]itting[Ii]deal|[Ff]itting_[Ii]deal|[Ff]itting.*[Mm]inor)`; LeanSearch on finitely presented module Fitting ideals and base change; and a second LeanFinder phrasing using maximal minors and scalar extension. All five actual calls are recorded in the log, including both LeanFinder phrasings.

All services answered. Loogle returned Lie-module Fitting decompositions, not presentation ideals; grep returned zero hits. LeanSearch returned module finite-presentation/base-change facts, already available through the existing leaf. LeanFinder returned local quasicoherent presentations and Jacobian determinants. I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`, around lines 265--285, and `Mathlib/RingTheory/Extension/Presentation/Submersive.lean`, around lines 108--139. The former makes finitely presented sheaves quasicoherent and finite type; the latter defines a Jacobian for an algebra presentation. Neither constructs the ideal of all maximal minors of a module presentation or gives its space pullback theorem. I also read the tensor finite-presentation instance at `Mathlib/Algebra/Module/FinitePresentation.lean:338`, confirming the existing leaf `lem-pc-fp-module-base-change`. Results in the node are factual summaries of the calls, preserving their exact tool names and query strings; inherited records remain intact.

## Generic tool uses

The seven cross-unit statements in `split_report.tool_uses` are generic ring, scheme, atlas and tensor comparison tools. The ring/scheme Fitting theorems and the Zariski--etale and chart tensor comparisons serve exactly the reduction in Stacks 0CZ3--0CZ5, without using a trace-formula or Poincare-duality theorem. The affine cover and base-change-of-covering tools are general space geometry, and the affine tensor-sections comparison is general module pullback. The current unit supplies no alternate version of these foundational tools. Same-unit cartesian-family, affine-chart, kernel/image and quasicoherent-pullback nodes are reused directly. The finite-presentation base-change node is already a Mathlib leaf.

## Review by Q32

I read `spaces-divisors.tex` Tags 0CZ3 (section-fitting-ideals), 0CZ4 (lemma-base-change-fitting-ideal) and 0CZ5 (lemma-fitting-ideal-of-finitely-presented). Their proof reduces to scheme Fitting ideals and etale localization. I followed that argument, opening `divisors.tex` Tags 0C3C--0C3E and `more-algebra.tex` Tag 07ZA, especially (3) and the finite-presentation proof of (4). No new node needs a separate source review. I checked the supporting chart arguments in `spaces-properties.tex` Tags 03LZ, 03M0, 03M1, 03LV, 03FX and its section on module properties, and the scheme comparison and affine tensor formulas in `descent.tex` Tag 03LC and `schemes.tex` Tag 01I9. The Stacks tag-to-label table confirms these places. The proof follows those sources, with the finite determinant expansion written out rather than hidden behind the source's reduction.

For step 1 I opened the statements of `lem-sfb-space-qcoh-cartesian-chart-family`, `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`, `lem-sfb-space-qcoh-affine-chart-calculus`, `lem-trf-fitting-ideal-sheaf-pullback`, and `lem-trf-space-chart-adjunction-tensor-realization`. The first provides restrictions to all etale scheme charts and cartesian transition maps; the comparison provides ordinary scheme modules and compatibility with every scheme pullback. The chart calculus tests finite presentation on every affine etale chart, hence provides the finitely generated modules required by the scheme Fitting theorem. That theorem states both the affine formula and the image-ideal pullback formula. I used the final etale clause of the chart-tensor theorem to identify tensor pullback with restriction, so the pulled-back inclusion is an inclusion. This avoids treating an arbitrary pullback as left exact.

For step 2 I checked the map part and full faithfulness of the cartesian-family equivalence, not merely its object existence clause. Maps between the ideals obey the cocycle because they preserve their monomorphic inclusions into the structure ring. Compatible inclusions descend. I added `lem-sfb-space-qcoh-kernels-colimits` explicitly during self-review, so that the global kernel is known to be quasicoherent before using the affine-chart kernel computation to show it vanishes. The scheme Fitting theorem states the claimed affine characterization, and `lem-trf-fitting-ideal-independence-base-change` explicitly gives kernel-row determinants for every generating surjection. Equality/uniqueness is equality as subobjects with the inclusion fixed, not an arbitrary isomorphism of modules.

For step 3 I read `def-sc-finitely-presented-module` and `def-weil-pbc-matrix-determinant`. The former gives the finite exact presentation, so the finitely many images of the relation basis generate the kernel. Substitution into the latter's Leibniz formula and distribution of finite sums gives exactly the displayed expansion, including repeated rows. Each generator on the right is itself a kernel-row determinant, so both ideal inclusions are proved. This needs no additional lemma or Noetherian hypothesis. The chart calculus states exactly the final finite-type test. I marked just this calculation elementary: it is a direct finite expansion from the cited definitions and the existing ring description.

For step 4 I checked `lem-a1-space-affine-etale-cover` and `lem-trf-space-fibre-products-etale-covers`: the first provides arbitrary small affine etale covers, the second their joint-surjective etale base changes along any space morphism. No quasi-compactness of the spaces or of the covers is used. Refining the pulled-back cover by affine etale charts gives actual scheme maps into the affine target charts; I never assume the map from an arbitrary affine source chart factors into one fixed target chart. The quasicoherent-pullback lemma applies without any flatness or finite-presentation hypothesis on the morphism. The chart-tensor theorem gives composition and etale restriction, including local tensors and unit normalization. The Zariski--etale comparison and the natural affine pullback-sections theorem then compute both the module and the ideal-inclusion map on those charts. I verified the latter statement's naturality in the module map, so the ideal's map is specifically multiplication after scalar extension, not an unspecified isomorphism.

For step 5 I opened `lem-pc-fp-module-base-change`: it assumes exactly a commutative ring map and a finitely presented source module. It imposes no flatness condition and gives the correct scalar-extended module. The affine-chart calculus translates these finite presentations back to local module presentations on the source charts. Since these form an etale cover, they give exactly the definition of finite presentation used in this item. Quasi-coherence was established separately in step 4.

For step 6 I checked the arbitrary ring-map clause (2) of `lem-trf-fitting-ideal-independence-base-change`, not just its localization corollary. The image of the natural tensor map is the extended ideal by the explicit finite-sum formula. The quasicoherent-pullback and kernel/image closure statements make its sheaf image quasicoherent; the affine-chart calculus computes that image by the ordinary module image. Thus both ideals have equal restrictions as submodules of the same structure ring. Membership of sections is local for any subsheaf, so the covering equality is a global ideal equality. No claim is made that the tensor map is injective.

I tested the theorem and the determinant expansion on the zero module, a free module of positive rank, a cyclic quotient $A/(a)$, the zero ring, and the empty space. For the rank-zero presentation the one empty determinant is 1. For no relation generators and positive free rank the Fitting ideal is zero. For a cyclic quotient the construction gives $(a)$ and after scalar extension gives $(\rho(a))$. The nonflat map $\mathbb Z\to\mathbb Z/2$ with module $\mathbb Z/2$ gives $J=2\mathbb Z$; its tensor pullback is nonzero while its multiplication map into $\mathbb Z/2$ has zero image, equal to the Fitting ideal of the resulting rank-one free module. This checks why the image formulation matters. No intersection of affine opens is assumed affine, and no smallness or finiteness assumption on a covering family was silently added.

Against delivery-errors B--E: all nodes cited already exist, no new statement-only nodes or search records were fabricated, and the statement uses its existing definitions or spells out the finiteness notions. Every non-elementary input is a node, and every cited statement was opened. `citations.json` uses exact substrings from those statements for all 26 uses; the longer quotations include all clauses taken from the chart, scheme-Fitting and tensor-comparison nodes. The actual argument glues a chart family and performs ring calculations, rather than reassigning the item's clauses to new nodes. Every step is below 2000 characters, and none conceals a source's omitted comparison lemma: the required comparisons are explicitly cited. No SGA source, Lean editing, compilation, repository writes, or sub-agents were used.

## Validation and unfinished work

The preliminary server `review_split` returned PASS with zero new nodes and the declared generic tool uses. It notes the inherited absence of unit realization, which this non-key helper is not authorized to change. The required full delivery dry run and push follow this report. No mathematical subtask remains unfinished in this one-level split; existing unsplit dependencies remain the responsibility of their own future items.
