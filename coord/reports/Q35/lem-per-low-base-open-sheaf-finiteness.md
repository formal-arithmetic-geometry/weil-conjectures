## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-low-base-open-sheaf-finiteness.json: statement item, split in six steps; no Mathlib match. Its statement is unchanged.
- dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-base-generic-open-finiteness.json: new statement-only input, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-dvr-open-image-closed-fibre-finiteness.json: new statement-only input, unsplit; no Mathlib match.

The sandbox also contains citations.json and the actual msearch search log. No unit record is changed: this is not the unit's key node. No Lean files, compilers, git commands in the shared repository, live project files, or launcher files were changed or run.

## Attachments

None. Searched the project Lean by the blueprint tag and by open direct-image finiteness, generic constructibility and trait/DVR terms. The closest project result is AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_singleFunctor_of_isOpenImmersion, WeilConjectures/SixFunctors/Etale/Derived/Finiteness/DirectImage.lean:266. It assumes a finite-type scheme over a field and does not cover an arbitrary regular one-dimensional base. It cannot attach this item. Master is reference material only.

## Literature wanted

None: both source PDFs cited in the item are present and were read. The substantive finiteness inputs are sourced to ILO and Zheng, not SGA. No SGA route is used.

## Corrections and scope

The item had no proof. Its explicit warning against adding excellence or purity hypotheses is retained. ILO Expose XIII Theorem 2.3.1(i), printed p.197 (PDF p.203), supplies the low-dimensional route. Read the theorem and proof in full, including its separate local-dimension-two alternative, and read Zheng Proposition 3.16(1), printed p.19 and the preceding regular-base assumptions. The proof now handles dimension zero directly: an integral zero-dimensional component has no points outside a nonempty open. It does not need the source record's disjoint-union trick.

The generic and local inputs are different subproblems, not two renamed copies of the conclusion: the former gives an answer only after an unspecified dense shrinking over an arbitrary integral Noetherian base; the latter gives an answer only on the closed fibre of a DVR. The actual proof reduces the exceptional locus to finitely many points, establishes localization comparison, and assembles finite stratifications and one finite bound. Neither new node alone proves either global clause of the item. No definition is hollow and neither new statement contains a proof.

A source-pointer issue in an existing node was noticed but not edited: lem-sc-regular-dim1-dvr says the correct algebraic theorem, but its external tag 00DV is Nakayama's lemma in this Stacks snapshot. The correct source is Algebra lemma-characterize-dvr, Tag 00PD, whose equivalence (3) with (1) was read at algebra.tex:29103. This does not change the cited node's statement.

## Searches and duplicates

Before creating nodes, searched the whole DAG for generic constructibility/finiteness, dimension-one open direct images, trait/DVR and special-fibre finiteness, the item source place, and the existing source-node statements. Ran blueprint_refs.py searches for finiteness, generic, generic bounded, trait, closed fibre, Noetherian integral and discrete valuation, and ancestor on the item. Read the current chapter, unit and main-20261015 ancestor. There is no exact blueprint equivalent; same_as remains empty. The new from entries use the exact ancestor and via chain, with this item prepended.

All new-node queries were run through msearch.py, and the signatures returned were read. Both nodes have LeanSearch, LeanFinder, Loogle and source-grep evidence, plus a second semantic phrasing. Hits concern Chevalley constructible subsets, finite-type morphisms, affine inverse limits, open immersion properties or DVR algebra. They do not concern constructible etale higher direct images. Grep found no generic-constructible or trait-constructible higher-image theorem. The original item's search records are retained, with this run's related searches appended. No unavailable service was treated as a negative theorem search.

## Not duplicates

lem-per-noetherian-base-generic-open-finiteness vs thm-fin-deligne-generic-open: the existing statement assumes the base is of finite type over a field; the new generic input allows arbitrary integral Noetherian bases and imposes no universal-base-change conclusion.
lem-per-noetherian-base-generic-open-finiteness vs sk-thm-geo-generic-open: the imported unit uses the standing field and a finite-type-over-that-field base, which does not include arbitrary arithmetic or nonexcellent bases.
lem-per-noetherian-base-generic-open-finiteness vs lem-per-low-base-open-sheaf-finiteness: the new input has no regularity or dimension assumption but only gives finiteness over an unspecified dense open; the item proves finiteness on the entire low-dimensional base.
lem-per-noetherian-base-generic-open-finiteness vs lem-per-low-base-constructible-internal-hom: derived internal Hom is a different operation; its proof uses this item, so citing it would be circular.
lem-per-noetherian-base-generic-open-finiteness vs lem-per-quasi-excellent-etale-direct-image-finiteness: the existing finiteness theorem assumes a quasi-excellent target (or properness), neither available here; the new input is generic in a base and assumes neither.
lem-per-dvr-open-image-closed-fibre-finiteness vs lem-per-low-base-open-sheaf-finiteness: the new statement concerns only the closed-fibre restriction over a local DVR, not the entire nonlocal base or even the entire trait. The item carries the dense-open and finite-stratification assembly.
lem-per-dvr-open-image-closed-fibre-finiteness vs lem-per-low-base-constructible-internal-hom: the latter concerns internal Hom, not higher direct images restricted to a closed fibre; it is an ancestor and cannot be used without circularity.
lem-per-dvr-open-image-closed-fibre-finiteness vs lem-trf-nearby-cycle-sheaf-finiteness: nearby cycles use the geometric generic fibre map and a strictly henselian trait; the new statement uses an arbitrary open immersion of total schemes, arbitrary DVR, and the arithmetic closed fibre.
lem-per-dvr-open-image-closed-fibre-finiteness vs lem-per-quasi-excellent-etale-direct-image-finiteness: a DVR need not be quasi-excellent, whereas the existing theorem requires that for a nonproper open immersion.
lem-per-dvr-open-image-closed-fibre-finiteness vs lem-per-gabber-open-immersion-sheaf-finiteness: that node imposes quasi-excellence on the target, which is not a hypothesis on this DVR or its finite-type schemes.

## Review by Q35

I read ILO XIII Theorem 2.3.1 and its proof on printed p.197, the preceding generic-finiteness discussion, and Zheng 3.16(1) with its paragraph of assumptions. They permit precisely invertible finite coefficients over the regular dimension-at-most-one base; no excellence or dualizing assumption was imported from the alternative cases. The new generic node isolates the first sentence of the dimension-one proof, and the DVR node isolates the local regular dimension-one finiteness input only on its closed fibre. These are statement-only future work. I also read Stacks theorem-higher-direct-images (03Q9), properties lemma-regular-normal (0569), lemma-normal-Noetherian (033M), and algebra lemma-characterize-dvr (00PD). The source review corrected the temptation to use the field-only existing theorem and caught the wrong source tag in the existing DVR node.

In step 1 the finite-type-over-Noetherian node supplies Noetherianity of T, the open-subscheme node supplies quasi-compactness, and the qc-open-immersion node supplies finite type of j. The two clauses of rem-pc-regular-normal supply normality and the finite disjoint integral component reduction. The open-restriction node states exactly the required restriction isomorphism. These are generic tools, explicitly declared in split_report.tool_uses, not a replacement of any Fourier/perverse unit route.

In step 2 the generic node actually states both constructibility and a common high-degree vanishing bound on a nonempty open. The existing field-only generic theorem does not state this for our base, so it is discussed as a nonduplicate and is not cited in the proof. Open restriction identifies its direct images with the restricted original sheaves.

In step 3 finite components of a closed subset are supplied by lem-sc-noetherian-closed-subset-finite-components. The dimension definition makes each component a closed singleton, because a further proper specialization would make a chain of length two. Regularity is asserted for all stalks by the regular-scheme definition, and lem-sc-regular-dim1-dvr supplies exactly the local DVR assertion. This tests the dimension-zero case correctly: the exceptional set is empty. No affine-intersection assumption or excellence of the local ring is used.

In step 4 the constructible definition and pullback-stratification statement give the pulled-back finite trivializing stratification; constructible preimage supplies the constructible-subset clause. Localization is explicitly written as a filtered colimit of principal-open localizations, matching the ind-etale definition. I opened lem-trf-ind-etale-strict-local-invariance: its statement gives an isomorphism of the strict localizations for locally ind-etale maps, including base changes. I opened prop-weil-pbc-strict-henselization-stalk-formula: its statement computes the cohomology on precisely the fibre product that is unchanged by that isomorphism. The inverse-image stalk node identifies the source stalk; the higher-direct-image forgetful comparison and exact constant-coefficient inverse-image theorem justify passing between module and abelian sheaves. Scalar naturality makes the comparison A-linear, and geometric-stalk conservativity proves invertibility. This is a written stalk calculation, not an invocation of closed-fibre base change.

In step 5 the local input states exactly constructibility and eventual vanishing after restriction to the arithmetic closed fibre. Its hypotheses are checked: the residue field is unchanged by localization, ell remains a unit, and the cited separated finite-type and open-immersion base-change nodes give the scheme hypotheses. F_a is constructible by step 4. Nothing about j on the special fibre alone is substituted for i inverse-image of Rj_*.

In step 6 the definition of constructibility is enough: composing the chosen strata with the complementary open and finitely many closed-fibre inclusions gives a finite partition into locally closed subsets of Noetherian T. The finite constant A-module values and trivializations remain the same. For vanishing, take the maximum over the genuinely finite family of bounds and use inverse-image stalks and conservativity. This also handles an empty exceptional set, empty open source, the zero sheaf, disconnected bases and components of dimension zero. All steps are shorter than 2000 characters; the only comparison calculation is fully exposed in step 4 with the statements that supply each ingredient. No arbitrary-sheaf uniform bound is asserted.

I checked the new statements on j equal to the identity, empty V, zero F, a field base for the generic node, and a nonexcellent DVR for the local node: none of their hypotheses excludes a case required by the item. Both carry complete objects, finite constant coefficients and ordinary small etale categories. I checked every proof citation against the statement itself; citations.json records verbatim statements, not text from proofs. No citation points to an ancestor depending on this item. B1-B9, C1-C8, D1-D5 and E1-E7 were checked against these specific sources and statements; the one-level split keeps the substantive generic and local finiteness facts open rather than assuming them proved.

## Unfinished work

No delivery work is intentionally left unfinished. The two new finiteness inputs remain unsplit as required for a one-level split; neither is claimed proved or a Mathlib leaf. The required dry run and delivery results follow from the delivery tool.
