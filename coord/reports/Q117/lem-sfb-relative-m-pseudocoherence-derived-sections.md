# Q117: lem-sfb-relative-m-pseudocoherence-derived-sections

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-m-pseudocoherence-derived-sections.json: item, statement, now split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-m-pseudocoherent-criterion.json: one new statement-only unsplit node, fixed-degree absolute affine pseudo-coherence, Stacks 08E7; no Mathlib match.
- citations.json: verbatim statements for every cited node in each numbered proof step.
- searches.jsonl: genuine output log from msearch.py, retained unchanged.

## Attachments

None. Searched lean/WeilConjectures by the exact item/blueprint tag and relative pseudo-coherence names, and by affine m-pseudo-coherence names. No project declaration states the item or new node. Read AlgebraicGeometry/AffinePseudoCoherentCriterion.lean: AlgebraicGeometry.isPseudoCoherent_affine_iff states only the all-degrees pseudo-coherent clause. It cannot attach either fixed-m statement.

## WANTED

None. All proof sources needed are available locally.

## Findings and changes

The item's imported statement is faithful to Stacks 09VF, clauses (1)-(3), and remains unchanged, including module-valued sections, quasi-coherence, arbitrary fixed m, covers that can depend on m, and absence of global boundedness and Noetherian assumptions. Its empty proof was replaced by four steps. No statement dispute arose.

The important gap in the existing interfaces is that lem-pc-affine-pseudo-coherent-criterion gives the all-m assertion only. This split does not apply that assertion at a single m, and does not use the all-m polynomial-presentation invariance lemma in place of its degreewise version. It adds exactly the fixed-m clause of 08E7. This is an absolute affine comparison for an arbitrary commutative ring, independent of any relative base, morphism, covers or polynomial embeddings, so it is a genuine smaller input, not a renamed clause of the item.

The derived-image identification is written out: the affine equivalence supplies a termwise associated-sheaf representative; the existing affine pushforward resolution lemma compares its pushforward with the K-injective computation; the natural associated-sheaf scalar-restriction isomorphisms commute with differentials. The result is an isomorphism of derived objects, not just a family of cohomology isomorphisms. This argument is two direct applications of cited results, so no new comparison node is needed.

Whole-DAG searches covered 09VF, 09UJ, 08E7, pseudo-coherence, fixed-degree affine comparisons, derived images and scalar restriction. Whole-blueprint searches with tools/blueprint_refs.py covered pseudo-coherent, m-pseudo, 08E7, and derived sections. No blueprint node states the new lemma or item. The ancestor command returns None, matching the inherited null ancestor; the precise inherited place and via chain are retained and extended for the new node. Read the current latest six-functors-basics unit _section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, clause (3). This is an existing supporting branch of that direct-image route, with no route change.

Mathlib searches were run only through msearch.py and their printed signatures were read. Both natural-language phrasings of the new lemma return underived quasicoherence/finite-presentation facts or support bounds in a t-structure; neither supplies finite-free approximations. The relative item queries return locality of ring-map properties and ordinary finite type/presentation, not this derived property. Loogle finds no PseudoCoherent name and the logged source grep finds no pseudo-coherence/strictly-perfect implementation. All recorded verdicts correspond to successful searches; no unavailable service is called a negative match.

## Unfinished work

None for this stage-1 item. The one new node deliberately remains statement-only for a later worker, as required. No Lean was written and no compiler, Lake or build command was run. Only the sandbox was written.

## Review by Q117

I read more-morphisms.tex at definition-relative-pseudo-coherence (09UI), lemma-relative-pseudo-coherence-characterize (09UJ), and the full statement and proof of lemma-qcoh-relative-pseudo-coherence-characterize (09VF). For the new node I read perfect.tex lemma-pseudo-coherent-affine (08E7), including the fixed-m finite-principal-cover argument. I checked the two definitions against cohomology.tex definition-pseudo-coherent (08CB) and more-algebra.tex definition-pseudo-coherent and definition-relatively-pseudo-coherent (065I). The new statement retains the fixed m and arbitrary commutative A; it does not assert all-m pseudo-coherence or a bounded representative of the supplied M.

For step 1 I opened lem-weil-pbc-lft-affine-pairs: it says exactly that every affine pair under a locally finite type morphism has a finite type ring map. Thus polynomial generators exist without adding quasi-compactness of f. I read def-nagata-relative-affine-space, whose affine formula is Spec of the polynomial ring, and def-weil-closed-immersion, whose quotient description says precisely that this surjection defines an affine closed immersion. These statements justify both translations, including n=0 and zero rings.

For step 2 I opened lem-pc-affine-qcoh-derived-equivalence: it explicitly gives termwise associated sheaf and module-valued derived sections as quasi-inverse functors on the unbounded quasi-coherent subcategory. Restricting E preserves quasi-coherence because it restricts its quasi-coherent cohomology sheaves; this is the local meaning of quasi-coherence. The representative F therefore has quasi-coherent terms. I read def-pc-ringed-spaces-derived-direct-image, which supplies the K-injective construction and its value for any chosen resolution. I read lem-pc-affine-pushforward-resolution-quasi-iso, whose hypotheses are exactly that i is affine, F is termwise quasi-coherent, J is K-injective, and s is a quasi-isomorphism. These are checked explicitly in the step. That node imposes no boundedness on F or J. Finally I read lem-weil-pbc-pushforward-tilde-spec: its isomorphism is natural in the module, so applying it to every differential gives a chain isomorphism and retains the polynomial scalar action. The derived comparison uses no exactness claim for arbitrary affine pushforward on all module sheaves.

For step 3 I checked the new fixed-degree criterion against 08E7 and applied it to the scalar-restricted module object over the commutative polynomial ring P. The definition def-sfb-ring-relative-m-pseudocoherent has exactly the existential polynomial-surjection quantifier used here. Composing approximation maps with an isomorphism directly preserves the defining cohomology isomorphisms/surjection; there is no extra invariance lemma hidden in that sentence. The argument takes existence over the same alpha on both sides, and so does not need presentation independence.

For step 4 I opened def-sfb-relative-pseudo-coherent-complex: it gives precisely the existential covers-and-embeddings condition, with the same fixed m, yielding (1) iff (2) from the chart argument. I opened lem-sfb-relative-pseudocoherence-all-affine-charts: its statement gives every embedding on every affine pair and supplies existence, exactly what (1) implies (3) needs. For (3) implies (2), I corrected an initial citation of the general scheme-definition node, which did not explicitly state the affine-basis theorem, to lem-weil-pbc-affine-opens-basis. I read its actual statement; it supplies an affine neighbourhood inside every open, including the inverse image of a base chart. This is the only citation correction needed during the self-review.

I checked B1-B10: new node is statement-only and self-contained, notions cite their actual definitions, TeX escapes render once, sources are labeled Stacks tags, search records are genuine, there is no unsupported Mathlib leaf, no duplicate, and blueprint provenance is filled. I checked C1-C8 by reading each cited statement, not its proof, and putting its exact text in citations.json. The generic affine equivalence, affine resolution comparison, associated-sheaf scalar restriction, finite-type affine characterization and affine-basis theorem are declared as tools in split_report.tool_uses. The relative locality result remains on the inherited unit route. No node created here depends on the item, and the new node is not split. D1-D5 are satisfied because the proof performs the chart identification and cover assembly; the one new node is an absolute comparison. E1-E6 are checked by the hypotheses above and the explicit derived-object comparison. No source error or forbidden SGA route is used.

I tested zero complexes, the zero ring/empty affine, n=0, positive and negative m, and complexes with cohomology in arbitrarily negative degrees. Over a field, an infinite-dimensional vector space in degree -1 is 0-pseudo-coherent (use the zero approximation), but is not pseudo-coherent. This tests the distinction from the existing all-m affine criterion and confirms that no finiteness below m was imposed. A non-quasi-compact scheme can require different local upper bounds: the proof is chartwise and does not select a global bound. Every proof step has fewer than 2000 characters; no long step hides a lemma.

## Not duplicates

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sc-pseudo-coherent-fiber-bounded-above-model: the existing statement concerns A local bounded-above finite-free algebraic model of all derived fibre degrees; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs def-pur-pseudo-coherent-complex: the existing node defines Pseudo-coherent complexes; it does not assert the fixed-m affine sheaf/module equivalence.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-pc-affine-finite-free-sheaf-complex-lift: the existing statement concerns Affine finite-free sheaf complex lifts to modules; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-pc-affine-principal-sheaf-complex-transport: the existing statement concerns Principal-open restriction transports a finite-free sheaf complex; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-pc-affine-pseudo-coherent-criterion: the existing statement is all-degrees pseudo-coherence and a bounded-above finite-free model; the new statement compares a single prescribed m, with no pseudo-coherence hypothesis in other degrees.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-pc-affine-pseudo-coherent-localization-cover: the existing statement concerns Finite principal-open cover carrying pseudo-coherent localized module models; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-pc-affine-pseudo-coherent-principal-model: the existing statement concerns Finite-free sheaf model gives a module model on one principal open; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-pc-affine-pseudo-coherent-principal-sheaf-model: the existing statement concerns Principal-open finite-free model before derived reflection; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-pc-perfect-affine-bounded-projective: the existing statement concerns Perfect objects on an affine scheme are bounded finite projective complexes; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-pc-proper-cohomology-finite-free-resolution: the existing statement concerns Actual affine finite-free resolution of a quasi-coherent complex; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-pc-proper-flat-single-open-noetherian-comparison: the existing statement concerns Noetherian source data and termwise comparison for a proper flat single image; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-pc-proper-flat-single-open-pseudo-coherent: the existing statement concerns Pseudo-coherence of open restrictions of a relatively flat proper image; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-pc-pseudo-coherent-finite-tor-perfect: the existing statement concerns Pseudo-coherent complexes of finite Tor dimension are perfect; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sc-affine-open-localized-model: the existing statement concerns Module representative and localization comparison on an affine open; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sc-affine-open-pseudo-coherent-localization-point: the existing statement concerns Pointwise pseudo-coherent localization on an affine open; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sc-affine-principal-cover-quasi-iso-detection: the existing statement concerns Quasi-isomorphism detection on a principal-open cover of an affine open; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sc-coherent-pseudo-coherent: the existing statement concerns Coherent modules on Noetherian schemes are pseudo-coherent; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sc-pseudo-coherent-rhom-qcoherent: the existing statement concerns Derived internal Hom from a pseudo-coherent module preserves bounded-below quasi-coherence; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs def-sfb-space-pseudocoherent-complex: the existing node defines Pseudo-coherent complexes on an algebraic space; it does not assert the fixed-m affine sheaf/module equivalence.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-affine-etale-derived-hom-realization: the existing statement concerns Affine etale realization commutes with derived Hom from a bounded-above coherent source; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-affine-polynomial-embedding-pseudocoherence-invariance: the existing statement concerns Independence of polynomial embeddings for a fixed affine morphism; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-arbitrary-base-affine-dualizing-realization: the existing statement concerns Affine realization of supplied relative dualizing pairs without Noetherian assumptions; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-flat-fp-quotient-pseudocoherent: the existing statement concerns Pseudo-coherence under a quotient between flat finitely presented algebras; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-flat-lfp-structure-relative-pseudocoherence: the existing statement concerns A flat locally finitely presented structure sheaf is relatively pseudo-coherent; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-relative-pseudocoherent-pullback: the existing statement concerns Pullback along a pseudo-coherent morphism preserves relative degreewise pseudo-coherence; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-relative-section-image-flat-fp: the existing statement concerns Flat finitely presented relative image from an acyclic section algebra; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-scheme-relative-perfect-base-change: the existing statement concerns Relative perfection of scheme complexes under arbitrary base change; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-space-flat-proper-pseudocoherent-direct-image: the existing statement concerns Flat proper algebraic-space direct image preserves pseudo-coherence; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-space-flat-relative-pseudocoherence: the existing statement concerns Relative and absolute pseudo-coherence agree for flat finitely presented space morphisms; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-space-inverse-module-polynomial-model: the existing statement concerns Polynomial finite-free model of the infinitesimal derived limit; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-space-noetherian-pseudocoherent-criterion: the existing statement concerns Noetherian algebraic-space pseudo-coherence criterion; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-sfb-space-relative-perfect-fibre-criterion: the existing statement concerns Relative perfection from lower bounds on the complex and its fibres; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-trf-affine-relative-dualizing-comparison: the existing statement concerns Affine comparison for a given coherent relative dualizing pair; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

lem-sfb-affine-m-pseudocoherent-criterion vs lem-trf-affine-relative-tor-diagonal-finiteness: the existing statement concerns Relative affine Tor bounds and pseudo-coherent diagonal finiteness; its hypotheses/conclusion do not give the fixed-m affine sheaf/module equivalence for arbitrary A and M.

