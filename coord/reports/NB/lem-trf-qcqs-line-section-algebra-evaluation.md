# Stage-1 delivery: lem-trf-qcqs-line-section-algebra-evaluation

Group NB; 2026-10-23. This is a first split, not a repair of a returned delivery. The sandbox initially contained only dispatcher markers; the item was copied from the live read clone. There was no prior proof, report or search log to discard.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-qcqs-line-section-algebra-evaluation.json`: statement, split in seven steps; no exact Mathlib match.
- `citations.json`: one verbatim statement excerpt for every step/node pair (23 pairs).
- `report.md`: this report. `searches.jsonl` was written by the required search command.

New nodes: 0. New Mathlib leaves: 0. The statement and all its hypotheses are unchanged. The item retains its original source, chapter, unit, ancestry and other maintainer-owned fields. No unit record is edited because this is not its key node.

## Attachments

None for the item. Searched `lean/WeilConjectures/` by the exact blueprint tag and by sectionAlgebra, section_algebra, sectionRing, pushforward/coproduct and pushforward/directSum, then read the relevant relative-Proj declaration listings. Section-ring and relative-Proj declarations handle individual ingredients; none states all the coproduct, evaluation, fixed-affine-domain and compatibility clauses of this item. No ATTACH claim is made. The existing dependency `lem-weil-pbc-qcqs-cohomology-direct-sum` already records the closed project theorem `AlgebraicGeometry.Scheme.moduleCohomology_directSum_bijective`; its source in `QcqsCohomologyDirectSum.lean` was read, not compiled.

## WANTED

None. All proof sources are present in `literature/stacks-project/`.

## What was wrong or incomplete

The item had a statement and searches but no proof. No statement dispute or source error was found. The subtle points are that sections of an infinite sheaf coproduct cannot be identified with the algebraic sum on arbitrary opens, and that the generation locus over one fixed affine base open needs its own check. The proof now limits the section identifications to qcqs opens, uses the canonical map specified by the existing cohomology theorem, and proves the fixed-affine generation test using the affine pullback tensor formula and the unit-ideal test in a local ring. It never treats intersections of affine opens in a quasi-separated scheme as affine.

During review I corrected my draft source tag for `lemma-glue-relative-proj`: the local tags table gives 01NQ, not 01O6. This was a draft citation error, not an error of the imported statement or of Stacks.

## Unfinished work

None within this one-level split. No Lean was written and no compiler, Lake or build tool was run. The global formalization of the existing dependency nodes is outside this item.

## Searches and blueprint route

All new Mathlib searches ran through `/home/ubuntu/weil-launcher-all/batch2/msearch.py`, with this item's group and id; their queries are recorded exactly in the item and in the command's log. LeanFinder and LeanSearch returned general graded-algebra or absolute-Proj constructions, not this theorem. Loogle's pushforward/coproduct query and the initial algebraic-geometry grep returned no hits. A second LeanFinder phrasing asked about global sections and arbitrary sums, returning colimit existence and unrelated qcqs localization results. A targeted grep located `AlgebraicGeometry.Proj.fromOfGlobalSections` at Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:443; I read lines 406–456. Its input is a map to ordinary global functions with the irrelevant ideal generating the unit ideal; it does not supply this line-bundle section algebra, qcqs comparison or relative evaluation. All services answered successfully; none is recorded as unavailable. Existing inherited searches are retained.

Read the three levels of SETUP.md, GOAL.md, the worker and stage-1 briefs, the chapter and unit records, and delivery-errors B–E (including the merged copy). The blueprint ancestor command identifies `lem-trf-local-term-locality`. Whole-blueprint searches included section algebra, section ring, graded section, 01LC, 01O9, 01FF and coproduct. The only relevant imported theorem hit was `pqf-lem-pushforward-qcoh` for 01LC, which is reused. The section-algebra criterion is below the polarized-descent chain already recorded in the item's `blueprint.from`; this split does not replace a chapter or unit step. Off-unit generic tools are declared in `split_report.tool_uses`, with the operation required from each.

## Not duplicates

No nodes are created, so there are no new/existing pairs requiring a same-tag distinction. Reused existing statements include arbitrary coproduct closure, qcqs cohomology of a direct sum, the module adjunction, affine pullback sections, relative-Proj existence and its chart atlas. In particular I did not create a qcqs-pushforward-coproduct lemma: its needed instance is assembled in step 4 from the existing H^0 theorem and restrictions.

## Review by NB

I read Morphisms Tag 01VJ, `lemma-characterize-relatively-ample`, the proof of (3) implies (5). This item isolates its section algebra and adjunction map, without assuming ampleness or claiming an open immersion. I also read Schemes 01LC (`lemma-push-forward-quasi-coherent`), 01ID (`lemma-colimit-quasi-coherent`) and Section 01LA; the affine module mapping property and equivalence at 01I7/01IB and pullback formula at 01I9; Cohomology 01FF; Modules 01AI; Sheaves 0096; Constructions 01NK and 01O9, including the latter's fixed-affine restriction clause (3). Tags and labels were checked in the local tags table. No forbidden SGA source is used.

For step 1 I opened `def-sc-invertible-module`, `def-pur-sheaf-tensor-product` and `pqf-def-coherent`. They give locally free rank one, the sheaf tensor product, and affine-local quasi-coherence. The written frame computation supplies the remaining argument for every tensor power; no separate tensor-closure lemma is presumed. The zeroth tensor power is the structure sheaf with unit 1.

For step 2 I opened `pqf-lem-pushforward-qcoh`: its hypotheses are qcqs on the morphism, not properness, finite type or noetherianness, so it applies degreewise. I opened `lem-weil-pbc-quasi-coherent-module-coproduct-closure`, which allows an arbitrary small family, and applied it with the small index set N on both schemes. `def-weil-pbc-graded-sheaf-structures` defines homogeneous operations on sheaf coproducts, not pointwise sums on all opens; `def-weil-pbc-quasi-coherent-algebra` asks exactly for quasi-coherence of the underlying module. The explicit section products and structural unit supply these data.

For step 3 I opened the module restriction/colimits statement and `lem-weil-pbc-affine-tilde-gamma-adjunction`. The latter states the counit isomorphism for quasi-coherent modules, the unit isomorphism and preservation of all small colimits by tilde. These give the claimed affine section identification using the actual coprojections. `def-sc-invertible-section-ring` gives the same tensor multiplication and unit, so the identification is graded and multiplicative, rather than merely a bijection of ungraded groups.

For step 4 I checked the statements of `lem-weil-pbc-affine-scheme-qcqs` and parts (2),(3) of `lem-weil-pbc-qcqs-morphism-permanence`. They justify the qcqs hypotheses on W after restricting the morphism to affine V. The restriction theorem preserves precisely the coproduct inclusions needed here. `lem-weil-pbc-qcqs-cohomology-direct-sum` states that the canonical map induced by those inclusions is an isomorphism, for any family and p>=0. The resolution definition in `def-sc-ringed-space-module-cohomology` permits the two-line kernel computation identifying degree zero with ordinary sections. Consequently the map proved invertible is the specified c, not an unrelated existence isomorphism. Multiplication and the unit are checked on homogeneous local sections and extended through local finite sums. Only affine opens of T are used to detect the sheaf isomorphism.

For step 5 I opened `lem-pc-module-pullback-adjunction` and `def-pc-module-pullback`. They explicitly use tensor pullback and direct image by inverse-image opens. Taking the mate of c is therefore the required evaluation. The formula and its balancing check are written; in each degree the induced section map is literally s->s. Restriction, multiplication and the unit are verified in that same formula, without an unspecified claim that a comparison transports them.

For step 6 I opened `lemma-nagata-relative-proj-exists` and the scheme clause of `lem-trf-space-line-module-proj-map`. The former supplies the affine restriction isomorphisms and their further compatibility; the latter supplies the canonical map and its domain as the positive-degree surjectivity locus on schemes. I did not use an unstated Zariski/etale equivalence from its proof. `lem-weil-pbc-module-pullback-affine-sections` gives the tensor formula for every affine O lying over affine V, with no flatness hypothesis. Thus the global sections on the fixed V generate the source stalks. The local-ring argument then proves the fixed-V union formula. `def-sc-section-generating-locus` explicitly identifies generators of an invertible module with its nonvanishing locus.

For step 7 I opened `lem-trf-line-proj-affine-chart-atlas`: its statement gives the exact fraction map, uniqueness, agreement on overlaps of different degrees and compatibility with refinements. Evaluating the two numerator/denominator sections by step 5 proves agreement with the absolute section-ring map. Further restriction sends a numerator and denominator to their restrictions, with the same coefficient; the relative-Proj existence statement gives the target chart compatibility. The final covering conclusion is a direct inclusion argument.

I tested empty X and empty affine V (all constructions and covers are empty), degree zero (the unit is f-sharp, not an assumed equality A_0=O_T), the trivial line bundle (the formulas reduce to the tensor polynomial algebra), a line bundle with no nonvanishing positive global sections on a chart (both generation loci are empty there), and positive degree d>1 (the charts use b/s^k in degree kd and never assume generation in degree one or invertibility of O_P(1)). The only pointwise unit-ideal argument takes place in the local ring at x. No separatedness, noetherianness, finite generation, flatness, ampleness or surjectivity was added. Every step is below 2000 characters; no long inline lemma is hidden. Citations were generated from the actual live node statements and checked for literal containment.
