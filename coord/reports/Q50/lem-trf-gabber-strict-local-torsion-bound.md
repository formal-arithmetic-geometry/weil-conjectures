# Stage-1 delivery: lem-trf-gabber-strict-local-torsion-bound

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-gabber-strict-local-torsion-bound.json`: existing statement, now split into nine steps; statement and inherited searches retained.
- `dag/nodes/sec-trace-formula/lem-trf-gabber-nearby-cycle-dimension-bound.json`: one new statement-only node for Illusie Theorem 1.14 (Gabber); not a Mathlib leaf. Its global vanishing-topos theorem is the named input to the strict-local corollary, not another copy of that corollary.
- `citations.json`: a verbatim statement quotation for every node used in every step.
- `searches.jsonl`: real Q50 Mathlib searches, read and recorded with the printed results/digests. The original preparation script is absent from the retained repair sandbox; no script is part of this delivery.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` for the exact blueprint tag, Gabber, strict-local cohomological bounds, nearbyCycles and vanishingTopos. The Gabber declarations found concern affine henselian comparison, effacement, and perverse operations; none states this item. Master was searched as reference only; its declarations do not close an item.

## WANTED

WANTED: Luc Illusie, *Around the Thom-Sebastiani theorem*, author PDF `Illusie-nearby-cycles28.pdf`, Theorem 1.14 and Corollary 1.15, printed pp. 15–16; also formulas (1.3.1), (1.12.6)–(1.12.7), for this item and the new node. The PDF is absent from this machine's literature mirror; I read the author PDF online at https://www.imo.universite-paris-saclay.fr/~luc.illusie/Illusie-nearby-cycles28.pdf. No SGA source was used. The source's omitted limit argument is expanded through Stacks 03SA, 09YU and 03S6 rather than its SGA references.

## Audit findings and corrections

The item is a faithful statement of Corollary 1.15, including arbitrary torsion coefficient rings, non-Noetherian bases and sheaf-valued vanishing. Its proof was empty. It is not legitimate to assume an arbitrary sheaf on the strict localization descends to a single pointed neighbourhood. Instead the proof forgets to the finite ring A = Z/m, writes the sheaf as a filtered colimit of constructibles, descends each constructible, and makes it a retract of the restriction of an ambient etale sum-extension. This avoids imposing finiteness or Noetherianity on the original Lambda.

The existing unbounded strict-local nearby-cycle comparison depends on this item through the universal (*) bound. It is deliberately not cited: that would create a cycle. Bounded-below oriented-point cohomology and the ordinary strict-local stalk formula supply precisely the part needed here. The already existing ind-etale invariance node handles non-closed points of the target strict localization.

Self-review also corrected the attempted use of scheme-stalk exactness on the vanishing topos: step 2 now cites exact module inverse image for an arbitrary geometric morphism. No statement change, no source dispute, no new definition, no unit or chapter change.

## Not duplicates

lem-trf-gabber-nearby-cycle-dimension-bound vs lem-trf-gabber-strict-local-torsion-bound: the former is Illusie Theorem 1.14 about R Psi of an ambient sheaf on the vanishing topos; the latter is Corollary 1.15 about every sheaf on a strict localization and ordinary direct image to the strict-local base. The explicit approximation, descent, retract and stalk arguments are the mathematical reduction between them, retained in the item.

lem-trf-gabber-nearby-cycle-dimension-bound vs lem-trf-nearby-cycle-finiteness-exchange: the latter is a trait/constructible nearby-cycle finiteness-and-exchange result; it does not supply Gabber's uniform arbitrary-base, arbitrary-sheaf vanishing-topos bound.

Whole-DAG keyword and theorem-number searches and blueprint searches for Gabber, nearby cycles, nearby-cycle and cohomological dimension found no existing statement of Theorem 1.14. The blueprint Gabber entries concern affine henselian comparison or perverse affine morphisms. The new node has no Stacks tag shared with another node. The source's finite-type-over-a-field and invertible-coefficient cohomological bounds in the DAG do not apply to arbitrary bases and arbitrary m.

## Mathlib search review

The recorded Q50 LeanFinder query for relative nearby-cycle cohomological dimension returned general DerivedCategory bounds and affine-limit section vanishing, not a bound for etale nearby cycles. The second phrasing about higher images of strict localizations returned derived fractions and t-structure lemmas. Loogle's `"rightDerived"` returned only general derived-functor existence/universal properties. LeanSearch returned group-cohomology coboundaries, projective dimension and AB4, none a nearby-cycle bound. The whole-Mathlib grep for nearbyCycles, vanishingTopos, Gabber and strict-local cohomology found only three bibliography mentions of Gabber; the AlgebraicGeometry cohomological-dimension grep had no hits. All six commands completed successfully. No unavailable search was reported as absence, and no unrun search was added. Prior item searches were retained separately.

## Review by Q50

I read the source item in Illusie's author PDF: Theorem 1.14 has exactly a Z/n-algebra, locally finite type f, uniformly bounded fibre dimensions and arbitrary module sheaf F; Corollary 1.15 has arbitrary G on X_(x) and ordinary higher direct image on S_(s). Neither adds invertibility or a Noetherian condition. I read the statement of the new node against Theorem 1.14 clause by clause, including its vanishing-topos object and coefficient category. I read the current chapter and sk-i-curve-zero unit: this item remains the universal (*) input for the external-product comparison in the normal-cone proof, with its historical blueprint ancestry preserved.

For step 1 I opened the strict-localization definition, the affine-source separation and affine-morphism statements, affine permanence (3), and higher-image forgetting. These give affine T and B, qcqs h and the comparison for arbitrary Lambda and for A. The comparison does not require the underlying forgotten injective to remain injective. A = Z/m is finite; Lambda need not be finite.

For step 2 I read the new Gabber statement, oriented-point cohomology, and constant-module inverse image. The oriented-point node explicitly gives the Milnor-tube cohomology of every bounded-below input, for second scheme S and identity second map, so F[0] is in its domain. Exact inverse image is stated for arbitrary geometric morphisms; this is also what permits taking the degree-q stalk. All fibre hypotheses remain those of the original f.

For the repaired step 3 I reopened the current strict-henselization functoriality, affine-chart ind-etaleness, ind-etale strict-local invariance and fibre-product statements. Functoriality (1) makes B a local spectrum whose closed point maps to s. The elementary unit argument makes its structural map factor through any affine open around s. The chart lemma then applies with the identity identification Spec H = B, giving precisely the local affine ind-etale hypothesis now written in the invariance statement, at every geometric point t. Taking t_0 with the same algebraically closed field verifies its geometric-field hypothesis. Its canonical isomorphism e:B_(t) -> S_(t_0) is over S; the required specialization is explicitly c=b e^{-1}, so ce=b identifies both tubes and the restricted coefficient sheaves. This does not specialize its closed-geometric-point iteration clause to an arbitrary t: it applies the general quantified clause after checking its hypothesis.

For step 4 I read the strict-local stalk formula (torsion abelian sheaves and qcqs h), the coefficient-evaluation comparison at a terminal object, the exact inverse-image comparison, higher-image forgetting and geometric-stalk conservativity. They give zero at every stalk, with no unsupported comparison of coefficient categories. Torsion follows from m acting as zero. This proves the sheaf-valued assertion for ambient restrictions.

For steps 5 and 6 I read the local Stacks text of 03SA (`lemma-torsion-colimit-constructible`) and 09YU (`lemma-category-is-colimit`), and the existing module approximation, filtered direct-image continuity, directed reindexing and module limit-descent statements. The approximation and descent are applied only to finite A, and only to affine qcqs schemes. Affine-source separation and affineness over a separated target verify affine transitions. Directed reindexing is used because the constructible descent node is stated over a directed set, not just a small cofiltered category. Each C descends, not the original arbitrary G.

For step 7 I read separation of affine-source morphisms, separation and etaleness under base change, and the full clopen-section lemma. The section is the actual limit projection a paired with 1_T; its equation follows from ua=j. Thus no henselian lifting theorem or unstated algebraization is needed. All hypotheses of the section lemma hold.

For step 8 I read local Stacks 03S6 (`lemma-shriek-base-change`) and the module base-change node, together with the sum-extension definition. I checked the explicit disjoint-open gluing argument: on the section component v is the identity and its coefficient is C; the complementary component gives the other summand. Inclusion and projection make a retract. This is a short argument from those cited statements and sheaf gluing, so I kept it as an elementary step rather than creating a redundant node. Step 9 is functorial preservation of a retraction, followed by the colimit already supplied in step 5 and the coefficient comparison already supplied in step 1.

I checked C1/C4 against every cited statement, including the correction about oriented-topos points. New-node B1–B10: its statement is self-contained, proof empty, source named, mathematical notions linked, all searches genuine, and blueprint ancestry/place filled. D1–D5: the item retains its nontrivial reduction and does not merely apply a restated new node. E1–E7: no invertibility, finite-Lambda, Noetherianity or global quasi-compactness hypothesis was smuggled in; m=1 gives the zero category, N=0 covers the identity/etale case, empty X is vacuous, and the argument permits infinite coefficient modules and points t away from the closed point. I also checked that no cited dependency reaches this item. Every step is below 2000 characters; there is no long step hiding an unrecorded comparison.

The new Gabber theorem is deliberately left unsplit and without proof dependencies. Its eventual proof is a separate stage-1 task, not silently treated as a Mathlib result. The off-unit uses are generic tools, declared in split_report.tool_uses for the maintainer to judge.

## Unfinished work

No part of the one-level split is left unwritten. The new statement-only theorem joins the queue. Server preflight and delivery results follow below when completed.


## Repair of return 2026-10-17 (head 054cf0d1aa)

The return says the independent reader approved the delivery, but landing detected a changed statement of lem-trf-ind-etale-strict-local-invariance. I retained the returned nine-step split and its statement-only Gabber input, compared the retained item with the current shared item (the item statement is identical, the current item remains unsplit), and reread every current proof citation, together with the current chapter/unit records. The now-reviewed Q51 invariance statement explicitly quantifies a locally ind-etale affine-chart hypothesis and uses the same geometric field for t and its image. Its general conclusion remains the exact canonical isomorphism needed in this item. I also read its current five-step proof to understand the structural-map scope, while relying only on its statement in our proof.

This is a substantive repair, not an unchanged re-push: step 3 now cites the existing affine-chart ind-etale lemma to discharge the current invariance hypothesis, cites strict-henselization functoriality (1) for the local-spectrum factorization, fixes the same geometric field, and writes the specialization as c=b e^{-1} with ce=b. It cites the fibre-product universal property for the resulting tube identification. The old inline cofinal-restriction argument and its two unused citations are removed from that step. No new node or weakened statement is needed. All 32 step/node quotation pairs were reconstructed verbatim from the current statements (including the retained new Gabber node), and the union of the step uses was recomputed.

The retained sandbox contained only the two nodes and report.md; the claimed citations.json and searches.jsonl were absent. The first required dry run was run before editing and stopped on the missing real search log. Since there was no search log to reuse, I reran all six recorded new-node queries with msearch.py, read their results, and appended those actual result records without discarding inherited search history. All six were available; their results agree with the original no-match decisions. The fresh grep returned only three bibliography mentions of Gabber, the semantic searches returned general derived-category bounds and ordinary group cohomology, and Loogle returned derived-functor universal properties. None is an exact match or a one-line specialization of the new theorem.

I reread Illusie's author PDF, Theorem 1.14 and Corollary 1.15, and its displayed (1.12.7), and local Stacks 03SA, 09YU and 03S6. The original reduction through finite A = Z/m, constructible approximation, directed descent and a clopen retract remains valid; none of the current cited statements imposes a missing hypothesis at its use. The new chart lemma's source is Stacks 04HX, with its precise algebra structure fixed by the chosen structural factorization. I rechecked m=1, empty X, N=0, nonclosed t and infinite Lambda, and the source/statement distinction between global nearby cycles and strict-local ordinary higher image. The local-source WANTED entry is retained. No SGA argument was introduced.

Every non-elementary step remains shorter than 2000 characters (the repaired step 3 is 1463); there is no newly hidden sublemma. The new Gabber node remains statement-only and unsplit; the new citations are existing general geometric tools, declared in split_report.tool_uses. B1--B10, C1--C8, D1--D5 and E1--E7 were checked again against the current statements and the source passages above. Only the sandbox is written. No Lean, compiler, Lake, project git command, or local execution of the prohibited validators was used. The required delivery tool will construct the repair commit on the current server base and run the full server preflight before push.
