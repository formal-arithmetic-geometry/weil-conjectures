# Stage-1 report: lem-sfb-group-space-unramified-identity-test

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-group-space-unramified-identity-test.json — statement, split in four steps; not a Mathlib leaf.
- citations.json — eight step/node entries, with each quote checked against the current node statement.
- report.md — this report. searches.jsonl is the search command's own log.

No new nodes; no Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for identity/unramified/group-algebraic-space terminology. The algebraic geometry hits on group schemes, isogenies, and scheme formal unramifiedness do not state the item for algebraic spaces. No compiler was run.

## Literature wanted

None.

## Corrections and findings

The item statement agrees with Stacks Tag 0DSI, spaces-groupoids.tex, label lemma-group-scheme-unramified-or-lqf, unramified clause. It needs no statement correction. The formerly empty proof now follows that source: largest unramified open, base change to a field-valued point, explicit translation, and reflection of membership in the original open. The previous searches and metadata were retained, and six actually executed searches were appended.

Read the current latest blueprint unit and direct-images proof (3). This is the inherited supporting prerequisite of the alteration/moduli route recorded in blueprint.from.place; no unit or chapter route is changed. blueprint_refs.py ancestor reports a null nearest blueprint ancestor, and that inherited field is retained. The current blueprint has no separate matching identity criterion: blueprint_refs.py search 'unramified' and 'group algebraic' and whole-DAG tag/concept searches were read. The two group-space nodes 0DSI and 0DSJ have different statements; using the base-locus node 0DSJ would be circular since it cites this item. It was not used. The existing scheme identity/dual-number criterion is only for finite-type group schemes, so it was not substituted for this algebraic-space result.

The field-valued-point/fibre-product node belongs to another unit. It is declared in split_report.tool_uses as a generic foundational tool, not as a replacement of the unit's argument. The existing unramified-locus node belongs to this item's unit.

## Mathlib search assessment

Ran LeanFinder twice with different formulations, Loogle, LeanSearch, and two grep queries, all through the required msearch.py command. All services answered. Read their hits and the local sources Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean (class at line 54) and Mathlib/RingTheory/Unramified/Locus.lean (locus at line 50, universal-locus equivalence at line 128). These concern rings or schemes and have no group algebraic-space identity-section criterion. The second LeanFinder query also returned unrelated infinite-place ramification and scheme permanence. No hit is a one-line specialization giving the item.

## Not duplicates

No new nodes were created. Reused lem-sfb-space-unramified-locus-base-change (05W2) and lem-trf-space-fibre-products-etale-covers instead of duplicating either statement. Translation and its explicit inverse are a direct application of the given group identities and naturality, so they remain an elementary proof step.

## Review by Q107

I read the whole proof of 0DSI in spaces-groupoids.tex and the statement and proof of 05W2, label lemma-where-unramified, in spaces-morphisms.tex. For 05W2, specialize its diagram to Z=Y=B: the required locally finite type hypothesis is exactly the item's hypothesis. The resulting equality of open loci is available for arbitrary algebraic-space base change, including every Spec K -> B used here; neither flatness nor finite presentation is required.

Step 1 uses the statement of lem-sfb-space-unramified-locus-base-change: it explicitly supplies the largest open, its pointwise interpretation, and arbitrary base-change equality. The forward implication and the assumed identity membership are then literal consequences. I did not use the proof of that node.

Step 2 uses the actual statement of lem-trf-space-fibre-products-etale-covers for the sheaf fibre product and the representation of every point by a map from a field. The maps are g:Spec K -> G and h=qg, so the correct fibre product is G times_B Spec K, and (g,id) is a rational point of that fibre product. Its identity maps to e(h(*)), precisely a point covered by the assumption. The locus theorem gives the required equality on that very base change. There is no claim that x was rational over the residue field of its image; arbitrary field representatives remove that potential missing hypothesis.

Step 3 uses def-trf-algebraic-space's explicit identification of morphisms with natural transformations. The formulas a -> g_T a and a -> g_T^{-1} a are natural, inverse on every T, preserve the map to Spec K, and send the identity to g. I checked def-weil-unramified-morphism and def-weil-open-immersion: an isomorphism carries an open neighbourhood to an isomorphic open neighbourhood, and reparametrizing the etale source charts leaves their scheme maps to Spec K unchanged. Hence the scheme unramified chart test used in the item's statement is identical. This is an elementary change of coordinates with the inverse written out, not a cited translation theorem or an unproved descent claim.

Step 4 again uses exactly the locus theorem's equality, then the definition of open immersion. Membership of the rational lift in p^{-1}(W) means its image x belongs to W. On any scheme chart an open containing all points is the entire open subscheme, so the open subspace W is G. The existing locus theorem then supplies global unramifiedness, without separately invoking a local-to-global theorem.

I checked B–E of delivery-errors.md against these files. Each cited node's statement was opened; every quote in citations.json is a literal substring of that statement. No new statement, duplicate, theorem disguised as a definition, or unsupported non-elementary fact was introduced. Each proof step is under 2000 characters (the total proof is 2265 characters). The source's unspecified translation argument was expanded rather than moved to a node. The source and target of every map and the direction of the pullback equality were checked.

As edge cases, an empty base gives an empty G (because G -> B exists) and a vacuous criterion; the proof has no point to choose then. The trivial group is unramified over any base. A constant etale group has the whole unramified locus. Over a field, G_a is not unramified at the identity, and in characteristic p neither is mu_p; the statement correctly does not infer unramifiedness from the existence of the identity. The proof assumes neither reducedness, separatedness, commutativity, smoothness, nor an algebraically closed field. In particular translating an arbitrary K-point works for a noncommutative group by left multiplication with the stated left inverse.

## Unfinished work

None at stage 1. Server dry run and direct delivery are recorded by the delivery command.
