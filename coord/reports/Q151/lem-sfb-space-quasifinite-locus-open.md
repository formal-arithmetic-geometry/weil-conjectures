## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-quasifinite-locus-open.json`: statement split in four steps; unchanged statement, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-scheme-quasifinite-at-base-change.json`: one new statement-only scheme lemma, Stacks 01TM(1); unsplit, no Mathlib match.
- `citations.json`: verbatim statement quotations for every use in every step.

Attachments: none. Searches of `lean/WeilConjectures/` for the exact blueprint tag, quasi-finite locus, and pointwise quasi-finiteness found only scheme/ring ingredients, not this algebraic-space theorem. Existing project proofs do not justify ATTACH for the item or the new scheme equivalence.

WANTED: none. All sources used are present locally.

The item originally had no proof. Its hypotheses and conclusion agree with Stacks 04NW for a scheme target; no statement correction was needed. Its references to local finite type on algebraic spaces and pointwise quasi-finiteness explicitly give chartwise meanings, so the scheme-only definition node is not being asked to define an additional notion. I retained all prior searches and metadata. There was no earlier sandbox split or report. The inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor` explicitly returns None. The concrete place and complete via chain are retained, and the new node adds the item to that chain.

Nothing remains unfinished in this stage-1 split. The new scheme lemma is deliberately left statement-only for a future worker, as required.

## Sources and route

I read spaces-morphisms.tex, Tag 04NW, lemma-locally-finite-type-quasi-finite-part, together with its neighboring relative-dimension argument (04NS, 04NV and openness). I implement its scheme-chart reduction directly rather than introduce an entire separate theory of relative dimension at algebraic-space points. For the chart inputs I read morphisms.tex Tag 01TI (scheme locus openness), Tag 01TM(1) (exact equality under arbitrary base change), descent.tex Tag 03X4 (etale source locality), and spaces-properties.tex Tags 03BZ and 03IR (open-subspace construction and open etale point maps). I also read the algebra.tex proof of lemma-quasi-finite-base-change underlying 01TM, to check that the reverse implication really holds without flatness or surjectivity of the base map.

The latest blueprint is main-20261023-1620, as identified in COMMITS.txt. I read its sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and det-thm-sf-ctf-stability-direct-images statement/proof. This item is a foundational geometric input reached through the recorded isolated-lci/alteration chain, under direct-image preservation (3); it does not replace the unit's six-functor route. The unit record is not edited: this is not its key node. Existing generic scheme/space lemmas from other units are individually declared in split_report.tool_uses for the maintainer to review.

## Searches

I searched the full DAG by quasi-finite locus, etale source locality, base change, and tag 01TM; opened the matching statements before selecting dependencies. Blueprint searches included `quasi-finite`, `quasi-finite at`, `04NW`, `01TM`, `01TH`, and combined quasi-finite/base/locus searches. The blueprint hits include scheme Zariski-main factorization and quasi-affineness, neither of which states the missing pointwise equivalence. No new algebraic-space openness node was created.

All new Mathlib searches ran with the required msearch.py command and are recorded in searches.jsonl. Two distinct scheme phrasings, Loogle on Scheme.Hom.QuasiFiniteAt, and source grep were checked. Mathlib's scheme quasi-finite locus and its isolated-fibre-point criterion are genuine ingredients, but the scheme base-change hits give global stability or forward pointwise ascent. In particular Algebra.QuasiFiniteAt.baseChange, Basic.lean:361, gives only the forward direction. I read QuasiFinite.lean:339-444 and the Basic.lean definition and baseChange proof. The scheme stalk predicate does not by itself provide the Stacks chartwise finite-type equivalence. The new lemma therefore remains unsplit rather than being mislabeled a Mathlib leaf. Semantic descriptions claiming Mathlib.LocallyQuasiFinite includes finite type were rejected after reading QuasiFinite.lean:19-24,55-60, which explicitly says it does not.

## Not duplicates

lem-sfb-scheme-quasifinite-at-base-change vs lem-weil-pbc-isolated-fibre-point-base-change: the existing node has only the implication from an isolated original fibre point to an isolated point after base change; the new lemma includes the reverse implication at each specified lifted point, needed for equality of loci.

lem-sfb-scheme-quasifinite-at-base-change vs lem-weil-pbc-separated-lqf-base-change: the existing node proves global preservation of local quasi-finiteness (and separatedness); it neither reflects pointwise quasi-finiteness nor describes the inverse image of the original locus.

The new scheme lemma is a strictly smaller input than the algebraic-space item: it constructs no open subset/subspace, proves no chart independence, and has only scheme objects. The algebraic-space argument remains in the item, especially its arbitrary-chart descent and point-set equality.

## Review by Q151

I checked every proof citation against the statement actually on disk, not its proof or source title. In Step 1, def-trf-algebraic-space supplies a representable surjective etale atlas; lem-sc-quasi-finite-points-open supplies both scheme openness and local quasi-finiteness on the resulting open; lem-a1-space-point-open-calculus says representable etale maps are open on points. Thus taking the image gives an open candidate, not yet an unproved assertion of chart independence.

In Step 2, lem-trf-space-fibre-products-etale-covers supplies the schemes and etale projections in V times_E A. The atlas restriction is etale because its scheme tests are open restrictions, exactly the assertion of lem-a1-etale-open-restriction. The image formula in lem-a1-space-point-open-calculus gives the precise image a^{-1}(p(V)), not surjectivity onto all of A. Only after restricting to that image is the projection surjective. Lem-a1-scheme-lqf-etale-source-locality has both etale precomposition and surjective etale descent, so it gives W -> S and then A_O -> S. No quasi-compactness is inserted. The affine witnesses in pqf-def-quasifinite are still affine open neighborhoods in A; that is the explicit reason the restricted conclusion is pointwise quasi-finiteness in the original chart. The reverse inclusion uses the atlas as one of the charts quantified in the item's definition, so p^{-1}(Q_h)=V follows without any unquoted pointwise etale-locality theorem.

In Step 3, lem-a1-space-invariant-open-quotient explicitly constructs the algebraic space and says its inclusion is representable by open immersions with the prescribed point image. It is stronger than a definition of open subspace and supplies the required existence.

In Step 4, lem-a1-space-lqf-atlas-refinement explicitly identifies U times_S S' with the pullback atlas and makes it representable surjective etale; its additional global-local-quasi-finite consequence is not used. Lem-weil-pbc-lft-base-change gives local finite type of the scheme atlas composite. Steps 1 and 2 then apply on this atlas without presuming the theorem's base-change conclusion. The new 01TM(1) statement gives exactly the equality V' = inverse-image(V), including reflection. Surjectivity on point classes and the commutative atlas square turn equality of inverse images into equality of subsets. The point-image formula and open-subspace inclusion criterion in lem-a1-space-point-open-calculus also identify the pulled-back open subspace. I checked that all four steps stay below 2000 characters and none hides an auxiliary comparison theorem.

For the new lemma I checked the full source statement of 01TM(1), not just its slogan of stability. Empty source and empty base change cause no exception: it is quantified over points of X'. Non-surjective changes test only points actually lifted. Nilpotent changes and arbitrary residue-field extensions are allowed. For A^1 over a field, every point remains outside the quasi-finite locus after field extension; for a finite scheme every point is inside it; a disjoint union of finite and positive-dimensional components tests the mixed locus. The atlas proof also works for an empty atlas/source and does not assume separatedness, quasi-separatedness, finite presentation, Noetherianness or global finite type. Every cited node was checked for these potential extra hypotheses.

The B–E audit found no new definition, no proof in the new node's statement, no clause simply renamed, and no statement dispute. TeX is written once, every new notion has a definition dependency or an inline meaning, and source places include verified tags and labels. The only correction during drafting was to avoid using the existing one-way isolated-point base-change node for equality: the new two-way scheme statement is cited instead. The only outstanding proof obligation is that intentionally unsplit supporting node.
