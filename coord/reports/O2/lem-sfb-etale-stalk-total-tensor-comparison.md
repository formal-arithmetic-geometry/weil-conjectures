# Stage-1 delivery: lem-sfb-etale-stalk-total-tensor-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-stalk-total-tensor-comparison.json`: item, statement; split into six steps; no Mathlib match for the whole normalized two-complex assertion.
- `citations.json`: fourteen verbatim statement quotations, one for each citation in each proof step.
- `report.md`: this report. `searches.jsonl` is the search command's retained log.

New nodes: 0. New Mathlib leaves: 0. The original statement, statement dependencies, provenance and previous search records are retained.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item id, stalk/tensor notions and complex comparisons found no declaration stating every clause. `AlgebraicGeometry.Etale.sheafFiberTensorIso` and its naturality theorem (`SixFunctors/Etale/UpperLowerStar/StalkMonoidal.lean:63,91`) supply ordinary sheaf tensor comparison only. `sheafFiberMapHomologicalComplexTensorRightIso` (`SixFunctors/Etale/Derived/Finiteness/ResidueTorTest.lean:76`) tensors a complex with a sheaf, not two arbitrary complexes. Neither is an attachment of this item.

## WANTED

None.

## Findings and corrections

The item is true as stated. Its source invokes the last paragraph of Stacks 07A4, which constructs the total comparison from ordinary constituents. That paragraph is inside a derived/K-flat proof; the ordinary total-complex argument itself does not require flatness. I kept this distinction explicit and wrote an agent-origin expansion of the ordinary argument, including its normalization and uniqueness, rather than citing the derived conclusion for arbitrary complexes.

The generic `lem-sfb-ringed-site-point-tensor` asserts only existence of a chain isomorphism. It does not state a coprojection normalization, uniqueness or two-variable naturality. I do not take those assertions from its proof. Instead the steps construct the canonical map directly using existing, smaller ordinary sheaf tensor and coproduct tools.

I checked `lem-kun-stalks-commute-colimits` together with its live Lean record: its applicable coefficient category is abelian sheaves. Step 2 therefore also cites `lem-weil-pbc-module-sheaves-colimits-forgetful`, clause (3), and checks that the resulting comparison is A-linear. Its old blueprint proof includes an incorrect inference that evaluation on a fixed etale object preserves sheaf colimits. This delivery uses only the valid colimit-preservation statement, whose live proof is the point/skyscraper adjunction, and does not repeat that inference.

The A_T versus constant-A tensor notation is handled in step 1: a bilinear map of sheaves balanced over A is balanced over A_T locally, since the latter's sections are locally constant, and the equality glues. Thus the sheafified tensor, rather than the raw sectionwise tensor, is the object to which the existing etale tensor lemma applies. No coefficient equivalence is assumed for arbitrary ring sheaves.

## Not duplicates

No new node is proposed. Existing Zariski ringed-space stalk tensor and direct-sum nodes are not applied to the etale site. `lem-pod-etale-stalk-tensor-scalar` supplies exactly the ordinary etale ingredient, and `lem-kun-stalks-commute-colimits` the abelian coproduct ingredient. The normalized ringed-site point total comparison is broader in its ambient site but does not state this item's normalization and uniqueness; this split reuses its underlying ordinary route without creating a parallel lemma.

Whole-blueprint searches were run for `stalk tensor`, `total tensor`, `stalks commute`, `tensor product of stalks` and `stalk.*tensor`; DAG searches also covered 03EL, 07A4, stalk tensor and coproduct titles. No imported blueprint node states the complete assertion, so `blueprint.same_as` stays empty. The ancestor command gives `det-ctf-finite-proper-tor`, with this item reached through `lem-sfb-etale-derived-tensor-stalk`. Its existing precise `from.place` is retained.

## Review by O2

I read the chapter and unit records, the current main-20261015 proof of `det-ctf-finite-proper-tor`, and the parent derived-stalk statement. This item realizes the unit's stalkwise tensor computation under the paragraph “From constant modules to all sheaves.” It is not the unit's key statement, so no unit realization fields are changed. The three off-unit theorem tools are declared with their purposes in `split_report.tool_uses`; definitions are used as notions.

For the item I read Stacks `sites-cohomology.tex`, Tag 07A4, label `lemma-pullback-tensor-product`, especially the final total-complex construction. For the ordinary tool I read `sites-modules.tex`, Tag 03EL, label `lemma-tensor-product-pullback`, and the preceding bilinear universal property. For the coproduct tool I read Tag 03DB, label `lemma-limits-colimits`, and the point/stalk constructions at Tags 04EN, 04EP and 04EQ. The cited colimit lemma's original blueprint and its live node/Lean record were also inspected. There are no new nodes requiring further sources.

Step 1 uses the constant-sheaf and sheaf-tensor definitions to identify the coefficient convention locally. Clause (1) of `lem-pod-etale-stalk-tensor-scalar` explicitly supplies a unique invertible pure-germ map natural in both module sheaves. Its inverse has exactly the direction and germ formula in this item. The hypotheses match: an arbitrary scheme, a geometric point, and an arbitrary commutative ring A; there is no lisse or finite-coefficient hypothesis.

Step 2 uses the module colimit theorem's explicit assertion that forgetting to abelian sheaves commutes with all small colimits. The abelian stalk-colimit theorem then supplies the underlying isomorphism. The scalar-linearity and additivity assertions are checked directly on germs using the stalk definition, so no exactness, flatness or change-of-rings theorem is smuggled into this step. The index sets here and in step 3 are countable sets inside the coefficient universe.

Step 3 uses only the total-tensor definition and the colimit universal property. It writes both maps and checks their composites on summands, giving normalization and joint determination. Step 4 uses the total differential formula from `def-pc-tensor-complex-sheaves` and the simultaneous naturality explicitly present in the ordinary tensor lemma. The displayed computation includes the two target bidegrees and the factor (-1)^p, with unchanged first index in the vertical term. The chain property of the inverse follows by multiplying the chain equation by the degreewise inverses.

Step 5 again uses the ordinary lemma's stated naturality, now at (f^p,g^q), and the total-tensor functoriality definition. Its displayed equation gives the precise naturality square, not merely existence of some natural isomorphism. Step 6 uses the colimit universal property to prove uniqueness from normalization. It also explains why no infinite sum of output components is involved in a differential: each input summand has only two outputs.

I checked zero complexes, complexes in one arbitrary degree (including negative odd degree), zero differentials, and a zero coefficient ring. For single-degree complexes the map is precisely the ordinary gamma; in negative odd degree the vertical term keeps the negative sign on both sides. For unbounded complexes with infinitely many diagonal summands, every construction is a coproduct construction and the differential remains column-finite. No finite support of the whole diagonal, boundedness, flatness, constructibility or finiteness of A is assumed. All six steps are shorter than 2000 characters; none hides a separately invoked comparison lemma. The deductions after the two ordinary input steps are elementary applications of their stated formulas and the coproduct universal property.

All fourteen uses have their cited node open and their full statements copied verbatim into `citations.json`. No tag-only non-elementary assertion is used. The Mathlib searches were run through msearch, read, and recorded with the exact queries. Two semantic phrasings returned ordinary stalk or total-tensor APIs, not the whole theorem; the relevant `Point/Monoidal.lean` and `Algebra/Homology/Monoidal.lean` hits were read. No search was invented and no service failure was recorded as absence.

## Unfinished work

None in this one-level split. The reused theorem nodes retain their own proof obligations independently. No Lean was written, compiled or built; only the assigned sandbox was written.
