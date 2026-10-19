# Q133: lem-dl-a1-constructible-fibres-exact

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-constructible-fibres-exact.json`: statement, now split into twelve proof steps. Mathlib searches find general exact-functor and site-point results, but no match for this adic common-stage assertion.
- `citations.json`: verbatim statement excerpts for every step/node citation.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The existing DAG already supplies the required mathematical tools; none is renamed or duplicated. `prepare.py` and `searches.jsonl` are sandbox preparation/search records, not DAG deliveries.

## Attachments

None. I searched the slopmaster2 project by the exact blueprint tag and by constructible/fibre/stalk/exactness terminology. `AlgebraicGeometry.WeilSheaf.preservesMonomorphisms_stalkFunctor` and `preservesEpimorphisms_stalkFunctor` in `WeilConjectures/WeilSheaf/StalkFunctor.lean` cover exactness for their concrete Weil-sheaf category, but do not state the full rationalized/common-stage-heart detection and locality assertion. `AlgebraicGeometry.Etale.isZero_iff_stalkZeroLocus_eq_univ` in `ConstructibleSheaf/Simple.lean:86` concerns ordinary etale module sheaves, not this coefficient category. They are not attachments. No Lean was written or compiled. The exact upstream master is not treated as proof evidence.

## WANTED

None.

## Problems in the imported item or blueprint

No statement correction. The item intentionally concerns constructible adic coefficient fibres, not arbitrary pro-etale sheaves. Its source references alone are not a proof of detection at points with domain `Spec k`: those points do not see generic residue fields. The split explicitly chooses a k-point in each connected lisse stratum and then uses finite recollement. This is a necessary argument, not a replacement of the unit's route. The unit remains the weight-gap proof; this node just supplies the final stalk-detection tool at Steps 1 and 5 of `p-dl-a1-exact.proof.md`.

The common-stage category is kept separate from discrete constant-coefficient rational sheaves and from the condensed-module categories. The only passage to continuous coefficient sheaves uses the existing explicit finite-stage realization lemma, with its coefficient and pullback comparisons. No result for arbitrary pro-etale sheaves is used as a conservativity theorem.

## Unfinished work

None at the requested stage. The cited nodes retain their existing status; this delivery splits just the assigned item by one level.

## Not duplicates

No new nodes; therefore no new/existing-node pairs need disambiguation. Whole-DAG and blueprint searches found and reused the existing geometric-stalk, coefficient-realization, exact-functor, and connected-stratification tools. In particular `lem-wf-rational-stalk-exact` is narrower: it gives preservation at closed points of Weil sheaves, whereas this item also proves detection, the ordinary constructible heart, and locality.

## Review by Q133

I read the source PDF, Section 6.8, in particular Proposition 6.8.4, Corollary 6.8.5 and its representation argument, Definition 6.8.6, Lemma 6.8.7, Proposition 6.8.14 and Remark 6.8.15. The last remark restricts the naive-pullback assertion to locally closed immersions; the proof only uses it there. I also read the local Stacks source for 03PU (`etale-cohomology.tex`, `theorem-exactness-stalks`), the Nullstellensatz in `algebra.tex`, and the good-stratification and noetherian connectedness statements in `topology.tex`. No SGA source was used. There are no new nodes needing a separate source review.

I checked each cited node's statement, rather than taking facts from its proof. The step-by-step checks were:

1. The finite-type-over-noetherian statement supplies Noetherianity, and the separated-section statement supplies a closed immersion. The structure morphism is separated by the item's hypothesis. A non-k-linear point causes no gap: a self-embedding of the algebraic closure of a finite field is an automorphism, so it only changes the parameterization of a k-point.
2. The immersion-completed-pullback statement actually asserts exactness, preservation of completeness and constructibility, and agreement with ordinary inverse image. Rational transport is explicitly an exact extension of supplied integral data. The standard-pair definition specifies the integral representatives of each rational half. None of these statements is used for an arbitrary non-immersion.
3. Point sections really are exact and commute with cohomology; point finiteness supplies finite-dimensional cohomology after rationalization. Localization-module exactness supplies exact rational tensor. The heart-triangle lemma gives the precise implication from a t-exact triangulated functor to exactness on the heart.
4. Common-stage calculus states finite-diagram descent including asserted equalities. Constructible truncations commute with field transitions, and the heart lemma gives kernels/cokernels from cones. Point scalar-extension comparisons and cohomology/scalar extension identify the finite-stage fibres with the specified Qbar_l vector spaces. Thus neither objects nor exactness are silently moved to a different rational coefficient category.
5. The realization statement gives an equivalence induced by the actual completed-to-continuous scalar extension, stratified locally free cohomology, and pullback comparisons. The scalar-extension exactness and cohomology lemma justify its preservation of the two standard halves; for the heart object this produces an actual degree-zero sheaf. I additionally checked `lem-tw-lisse-rational-realization`: its essential image is exactly the continuous locally free sheaves and its explicit point-fibre normalization is used in Step 7. This removes an implicit identification between two lisse models. I did not cite the discrete constant-sheaf realization, which would not identify the required constructible category.
6. The good-stratification lemma has the frontier property needed by the recollement induction. I additionally read the full statement of `lem-sfb-etale-local-monodromy-realization`: it supplies an etale cover and a normalized realization from invariant finite free lattices, rather than claiming a global lattice on the original stratum. I refined the cover by affine opens and their finite open-and-closed connected components. These are connected affine finite-type k-schemes, so the classical fibre equivalence has all its hypotheses. Nullstellensatz (1) identifies a maximal-ideal residue field with k; the composite point on Y is one of the tested fibres.
7. The representation equivalence is used only after the etale-local monodromy realization supplies an actual integral finite-system lattice. The connected affine cover members are separated, finite type and Noetherian, with l invertible. The finite-system fibre equivalence is therefore applied on a cover member that actually carries a compatible finite-level system. Its fibre at a chosen k-point is zero by the hypothesis and faithful field extension, so the local system vanishes; the general-site cover criterion then gives vanishing on the stratum. The realization comparisons identify restriction, and the lisse-realization point-normalization explicitly identifies the coefficient fibre, and faithful scalar extension of vector spaces detects zero. Faithfulness of the realization equivalence then returns the zero object to the rational category.
8. Recollement is cited at E coefficients, where its statement applies to separated finite-type schemes and an open/closed pair. The good partition supplies an open stratum; induction on the remaining finite partition gives zero on the closed complement. This avoids an invalid inference from all strata vanishing without gluing.
9. The exact-functor/homology statement explicitly includes kernels, cokernels and images. These are applied to the already proved exact fibre functors. Zero-object detection therefore gives joint reflection of isomorphisms and detection of zero maps without assuming that joint conservativity alone implies faithfulness.
10. The existing categorical short-exact reflection lemma matches exactly: the categories are abelian, the functors preserve zero maps and finite limits/colimits, and Step 9 proves the required joint reflection. I read its Mathlib declaration and hypotheses in `CategoryTheory/Functor/ReflectsIso/Exact.lean`.
11. Constructible truncations commute with Frobenius pullback because Frobenius is an automorphism. In fixed pairs I wrote out the induced kernel/cokernel structure maps using their universal properties, including invertibility from the inverse structure maps. This elementary construction proves that forgetting structure creates the relevant defects.
12. Open restriction is the immersion case already established. The exact-functor statement identifies restrictions of kernels, middle homology and cokernels. The sheaf local-isomorphism criterion is for general sites and categories, so it applies to pro-etale continuous module sheaves; the narrower etale/topological-space criteria were deliberately not used. On a quasi-compact test open a finite subcover and common-stage calculus suffice, so no global coefficient field is assumed on a non-quasi-compact scheme.

I tested the empty scheme (empty partition and zero category), a single geometric point (finite-dimensional vector spaces), zero arrows, nonzero kernel/cokernel defects, disconnected strata, torsion integral representatives killed on rationalization, and an infinite cover of a locally finite-type scheme. The argument does not confuse integral torsion fibres with rational fibres or all geometric stalks with just generic points. All steps are shorter than 2000 characters. Elementary steps are direct finite topological, recollement, fixed-pair, or kernel/image deductions from the named tools; no new claim is hidden in a long step. The citations file quotes the actual statements verbatim. The report and JSON retain the imported statement and ancestry, and declare the off-unit tools in `split_report.tool_uses`.

The first dry run stopped at four citation excerpts shorter than the required forty characters. I replaced the citation excerpts with the complete verbatim statements, so the reader can check all hypotheses and clauses in context; no mathematical statement was changed. A subsequent local review added the already-existing lisse-realization comparison in Steps 5 and 7 to make that identification explicit.

The final refinement in Steps 6 and 7 addresses the distinction between a pro-etale locally free continuous E-sheaf and a globally integral classical lisse system: Proposition 6.8.4(6) gives lattices etale locally, and the existing monodromy-realization node gives the exact normalization. I use the classical representation equivalence only after this local passage, and cite sheaf locality to return to the stratum. No additional node was created. All final steps remain below 2000 characters.
