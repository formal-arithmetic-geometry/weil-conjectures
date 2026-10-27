# Worker report

## Files written

- `dag/nodes/sec-nagata-compactification/lemma-nagata-proper-open-dense-iso.json`: statement, split, unchanged mathematical statement; searches find partial criteria but no complete Mathlib match.
- `citations.json`: verbatim statement quotations for every step/node pair.
- No new nodes and no new Mathlib leaves. `searches.jsonl` contains the six actual search-command records, retained unchanged.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint id and for proper/dense/open-immersion/isomorphism terminology. Read `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`, including `Scheme.Opens.eq_of_isProper_of_isSchemeTheoreticallyDominant`: it is a related result for nested open subschemes but explicitly assumes a quasi-compact dense-open inclusion, which the item does not assume. Its conclusion is equality of opens rather than the arbitrary morphism's isomorphism. It is not an exact attachment. The source has no declaration tagged with the item's id. No compiler was run.

## WANTED

None. The current blueprint statement and separate proof, and the necessary Stacks source, are available locally.

## Corrections and route

The statement is correct and remains verbatim. The imported paragraph had no dependencies and unjudged elementary status. The split supplies those dependencies and expands the schematic-density inference explicitly. It uses the existing Mathlib leaf `lem-weil-pbc-proper-closed-image`, avoiding an unnecessary theorem that proper immersions are closed immersions. This preserves the blueprint's open-and-closed-image and empty-complement argument. The chapter and unit were read; this is a supporting node, not the unit key statement, so no unit record is changed.

The definition `def-nagata-scheme-theoretically-dense-open` restricts itself to quasi-compact open immersions. Applying it to the open supplied by this item's hypothesis would add an assumption. Instead the item cites the already existing `def-trf-schematically-dense-open`, whose statement gives the injectivity on every open with no quasi-compactness condition, exactly Stacks 01RE. This is a definition used as a notion, not an off-unit proof route. No statement dispute is needed.

## Searches and duplicates

Read all six logged search results. The first LeanFinder and LeanSearch searches return surjective-open-immersion criteria, notably `AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective` (read at Mathlib/AlgebraicGeometry/Morphisms/IsIso.lean:24–26). Loogle returned no hits. The second phrasing finds universally closed dominant morphisms are surjective, which still requires an additional argument from the schematic-density hypothesis. The source grep finds `Scheme.Hom.isClosedMap` and scheme-theoretic dominance; the latter uses the kernel ideal predicate and its topological implication assumes quasi-compactness (SchemeTheoreticallyDominant.lean:45–50). These are partial ingredients, not an exact match for the item with an arbitrary dense open. Every recorded query is identical to an actual msearch.py query, and no service failure was reported as absence.

Searched the whole DAG by the phrases scheme-theoretically/schematically dense, proper closed image/map, surjective open immersion, and open immersion plus surjective; read the chosen existing statements. Ran `tools/blueprint_refs.py ancestor` for this item, and `search` for `proper dense open`, `proper open immersion`, and `scheme-theoretically dense`. No different blueprint node states the full item. `same_as` is therefore empty. Nothing new is created, so there are no same-tag new/existing pairs to distinguish.

## Not duplicates

No new nodes.

## Unfinished work

None in this one-level split. Existing definition dependencies retain their existing states. Lean and library builds are outside the authorized stage and were not run.

## Review by NC

I read the current main-20261015 statement and its proof file, the chapter and unit records, and Stacks morphisms.tex Tag 01W1 (`definition-proper`), Tags 01RB/01RE (`definition-scheme-theoretically-dense`/`lemma-characterize-scheme-theoretically-dense`), and schemes.tex Tags 01IJ/01IO (`definition-scheme`/`definition-immersion`). The item has no noetherian, quasi-compact, reducedness, or nonemptiness assumption; the proof uses none. No new node needs a separate source review.

For Step 1 I opened `lem-weil-pbc-proper-closed-image`: its statement says precisely that the image of any proper morphism is closed, with no extra hypotheses. The given q meets its only hypothesis. I also opened `def-weil-open-immersion`: it gives a homeomorphism onto an open subset. Thus the complement W is open and disjoint from the chosen U by the hypothesis U contained in the image. The only non-elementary assertion here is an already cited Mathlib leaf; the set-theoretic complement operations are elementary.

For Step 2 I opened `def-trf-schematically-dense-open`: it explicitly states injectivity on sections over every open, so the step uses the node's statement, not something hidden in its proof. I opened `def-pc-scheme` and checked Tag 01IJ's affine-neighbourhood condition; every point of an open W has an affine neighbourhood inside W. I opened `def-weil-affine-spectrum`: the statement supplies the ring of sections R and identifies its spectrum's points with prime ideals. Since the target of the restriction is sections over the empty open, the empty-cover sheaf axiom makes it the one-element ring. Injectivity forces 0=1 in R. Every ideal in that ring contains 1 and hence is the whole ring, so there is no proper prime ideal. This is the complete elementary contradiction, not an uncited schematic-density-to-topological-density theorem. I corrected the initially tempting use of the Nagata density definition because its quasi-compactness hypothesis was unavailable.

For Step 3 I reopened `def-weil-open-immersion`: its equivalent description states that q identifies its source isomorphically with the open subscheme of its image. With that image equal to X from Step 2, the structure sheaf restriction is the original structure sheaf. The isomorphism conclusion is consequently a substitution into the cited definition, with no missing surjective-monomorphism principle. This also explains why a new surjective-open-immersion node would be unnecessary here.

I checked B–E against these files: all cited statements actually supply what the steps take, quotations are copied verbatim, proof_deps is exactly the union of uses, and there is no new statement, duplicate, cycle-producing theorem, or disguised restatement. All three steps are under 2000 characters. Tested X empty, U empty, and disconnected and nonreduced X. For X empty the complement argument is vacuous and the open-immersion identification is the empty isomorphism. For U empty injectivity forces every affine coordinate ring of X to be zero, hence X is empty. A proper inclusion of a proper clopen component fails the density hypothesis because its nonempty complementary affine has nonzero sections. Nilpotents make no difference to the injectivity argument. Conversely D(t) into Spec k[t] shows why properness cannot be omitted: it is schematically dense but its image is not closed. No source or target statement was weakened.
