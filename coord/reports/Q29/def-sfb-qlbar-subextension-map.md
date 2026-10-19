# Stage-1 report: def-sfb-qlbar-subextension-map

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-qlbar-subextension-map.json`: existing definition, now split; 0 new nodes and 0 Mathlib leaves. The statement and its three statement dependencies are unchanged. The construction and laws are justified in three steps using existing nodes.
- `citations.json`: verbatim statement quotations for each of the three step/node citations.
- `searches.jsonl`: actual Mathlib search records written by msearch.py; every query is copied unchanged into the item's mathlib_searches.
- `report.md`: this report and the author's source review.

## Attachments

None. I searched the done source `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint id, `padicSubfieldRingObjMap`, `padicSubfieldCondensedRing`, `continuousMapRingSheafMap`, and concept variants (subextensions, condensed rings, continuous-map rings). No matching declaration was found. No matching name appeared in dag/lean_names_upstream.json.

The read-only master file `WeilConjectures/CategoryTheory/RingObjects/Condensed/FiniteSubextension.lean`, lines 77–103, contains `Profinite.padicSubfieldCondensedRingMap`, `Profinite.padicSubfieldRingObjMap`, `Profinite.padicSubfieldRingObjMap_id`, and `Profinite.padicSubfieldRingObjMap_comp`. They agree with this node, but master is reference material and they are not claimed as attachments to the done source. Its colimit theorem is sorried and is not used.

## WANTED

None. All sources used here were available locally. No SGA source is used.

## Corrections and observations

There is no statement dispute. The current main-20261015 source states the inclusion, its meaning on sections, and both strict laws, with the same inherited topologies as the DAG. The imported single paragraph was mathematically correct but did not spell out the continuity argument; its proof step also lacked a source field. I replaced that paragraph with the three checked steps and corrected proof_origin.place: the proof is supplied by the separate `def-sfb-qlbar-subextension-map.proof.md` source file.

The notions are already supplied by `sk-def-sfb-qlbar-condensed` (finite subextensions), `def-sfb-padic-subfield-condensed-ring` (inherited topology and C(S,E)), and `def-sfb-continuous-map-condensed-ring-map` (the actual morphism of condensed rings, its underlying ring-object morphism, and strict functoriality). There is no reason to create nodes for continuity of an inclusion or for the identity/composition calculation. The general construction is an existing broader node, not a newly invented restatement of a clause of this item.

The item has no chapter/unit fields in the current shared JSON. The new chapter and the parent unit do not yet have records in dag/chapters and dag/units; I read their current main-20261015 `_section.md` files directly. This is an observation for maintenance, not a change made by this delivery. The parent unit's first paragraph explicitly uses these inclusion maps; the construction follows it. This item is not the unit's key node and does not change realized fields.

## Not duplicates

No new nodes were created. Whole-DAG searches for `padicSubfieldRingObjMap`, finite-subextension inclusions, and postcomposition, and blueprint_refs searches for `qlbar subextension map`, `inclusions`, and `postcomposition` found no separate node equivalent to this item. `def-sfb-continuous-map-condensed-ring-map` is the general construction that this item specializes. The maps into Qlb and maps pulled back to a scheme are different maps, so they are neither duplicated nor cited for these laws. blueprint.same_as is []. Its blueprint.from remains null because this is an imported blueprint node, not a created node.

## Review by Q29

I read the current main-20261015 Markdown for the item, the parent `sk-prop-sfb-qlbar-colimit-point/_section.md`, the pro-etale-coefficients chapter `_section.md`, and the full current statements and Markdown sources of all three statement dependencies. I also compared the master FiniteSubextension declarations as described above. No use is made of a proof buried inside another node: the quoted general-map statement itself explicitly gives a morphism of condensed rings, a morphism of underlying ring objects, and the strict identity and composition equations.

Step 1 uses `def-sfb-padic-subfield-condensed-ring` only for the asserted topology restricted from Qlb. Its statement says exactly this, and the fields here embed by their literal inclusions, so its embedding hypothesis applies. I wrote out the inverse-image test: an open subset F intersect V pulls back to E intersect V. This proves continuity from the definition of subspace topology without a separate topological theorem. Because E and F are actual intermediate subfields of the same ambient field, inclusion preserves each ring operation. Neither completeness, a choice of equivalent topologies, nor a new hypothesis on the extension is used. The step is elementary.

Step 2 uses `def-sfb-continuous-map-condensed-ring-map`. I checked its hypotheses are a continuous ring homomorphism of topological rings, exactly what step 1 supplies for the inherited topological fields. Its statement has the section formula C(S,T) to C(S,T') by postcomposition and says that these maps form a morphism of condensed rings and then a morphism of underlying ring objects. Thus this citation supplies the sheaf and ring-object assertions, rather than merely a definition of a condensed ring. The displayed naturality calculation is a direct equality of compositions, not an uncited sheaf-existence assertion. The step is marked non-elementary because the existing general construction is used as a result.

Step 3 again uses the general-map statement, now its explicit strict-functoriality clause. For E contained in F contained in H, the literal field inclusions compose to the literal inclusion E into H. I wrote the resulting equality on every section; taking E=F gives the identity. This calculation is elementary once the cited functorial construction is fixed. No coherence isomorphism is substituted for the equality demanded by the item. The quotations in citations.json were copied directly from the dependency statements; the two uses of the general-map node are backed by its whole statement so that both its construction and its laws are visible.

I tested the boundary cases E=F, E=F=H, E=Q_l, and either equality in a chain E contained in F contained in H. The map becomes the identity or the remaining inclusion exactly as required. For an empty profinite S all section equations remain pointwise equalities of the unique maps. No new statement needs a small-case audit. Finiteness is required by the statement's chosen indexing family but is not needed to prove continuity or functoriality, so it has not been silently replaced by a stronger assumption.

For the Mathlib check I ran all four prescribed search services and then a second phrasing plus targeted searches. LeanSearch and the second LeanFinder query found `TopCat.continuousFunctions.map` and `TopCat.commRingYoneda`. I read Mathlib/Topology/Sheaves/CommRingCat.lean lines 224–254: they give a ring homomorphism on a fixed function space and a functor to presheaves on TopCat. I also read Mathlib/Condensed/TopComparison.lean: its topological-space construction is set-valued. These are useful building blocks for the already existing general-map node, but none directly gives this morphism of condensed ring objects with the specified source, target and laws as a one-line specialization. The first narrow grep had no hits; this is recorded separately from the later related hits. No service was unavailable, and no unexecuted query has been recorded.

Against delivery-errors B–E, there are no new unsplit statements, proof sketches hidden in statements, Mathlib-leaf claims, tag duplicates, or new clauses masquerading as prerequisite nodes. Every non-elementary assertion is supplied by the precise statement cited in step 2; steps 1 and 3 contain their short elementary arguments. I checked that both dependency nodes are distinct from the item, unmerged, and do not refer to it, so these proof edges introduce no cycle. Statement dependencies retain all three notions that the exact imported statement names. All source paths are local blueprint sources, so no invented Stacks tag or disallowed SGA route is involved.

## Unfinished work

None in the one-level split. The broader existing definitions remain independent DAG work items. No Lean was written, and no compiler, Lake command, or global build was run. The required deliver.py --no-push preflight is the final verification; delivery itself belongs to the fresh second reader.

## Repair of returned delivery

The landing was returned because `def-sfb-continuous-map-condensed-ring-map` had changed since the reviewed delivery. I rebased the citation review against the current authoritative DAG copy at `/home/ubuntu/weil-nt-live-dag/nodes/sec-proetale-coefficients/def-sfb-continuous-map-condensed-ring-map.json`. Its statement now explicitly says “For every profinite set $S$” before the section maps and “for every topological ring $T''$” in the composition clause. These are the two changes visible when comparing the old verbatim quotes retained in the returned sandbox with the current statement. I re-read the full current statement and confirmed that it still supplies exactly the two facts used by steps 2 and 3: postcomposition gives the condensed-ring and underlying ring-object morphisms, and the construction is strictly functorial. I updated both verbatim quotes in `citations.json` to this current statement. In step 2 I also made the profinite quantifier explicit. Step 1 supplies topological fields $E,F$, so the general-map hypotheses apply with $T=E$, $T'=F$; in step 3 the further finite subextension $H$ is a topological ring, so the newly explicit $T''$ quantifier applies with $T''=H$. I corrected the proof-source locations from invented paragraph numbers to the first, second, and third sentences of the single-paragraph source proof. The item statement and all dependency edges remain unchanged. The other cited statement, `def-sfb-padic-subfield-condensed-ring`, still agrees verbatim with its retained quote; I re-read its topology clause and checked the literal subfield embeddings again. The item on current main remains imported with the same statement and source as the returned version, so the retained three-step split is applied to that current base by deliver.py rather than replayed on its old base.

## Earlier second reading (a previous round; superseded)

- Source statement: checked `def-sfb-qlbar-subextension-map.md` against the imported item hypothesis by hypothesis; the finite-subextension, inherited-topology, condensed-ring, underlying-ring-object, identity, and composition clauses agree.
- Source proof: checked `def-sfb-qlbar-subextension-map.proof.md`, first–third sentences; the worker's three steps expand the source's continuity, postcomposition, and strict-functoriality argument without adding hypotheses.
- Step 1: checked against `def-sfb-padic-subfield-condensed-ring`; the subspace inverse-image calculation and induced ring operations prove continuity elementarily.
- Step 2: checked against `def-sfb-continuous-map-condensed-ring-map`; its statement supplies postcomposition, the condensed-ring morphism, and the underlying ring-object morphism, while the displayed restriction calculation supplies naturality.
- Step 3: checked against `def-sfb-continuous-map-condensed-ring-map`; its strict functoriality clause plus literal inclusion equalities gives the required identity and composition, including the sectionwise equations.
- New nodes: none; there are no B1–B7 statements to audit, and no Mathlib leaves were introduced.
- Edge cases: checked $E=F$, $E=F=H$, $E=\\mathbf Q_\\ell$, either equality in a chain, and empty profinite sections; all reduce to the stated identity or remaining inclusion.

I corrected each proof-step `source` and `proof_origin.place` to cite the existing `.proof.md` file, and corrected the worker review's claim that no separate proof source existed. The prior reader changed no mathematical statement, dependency, or citation quote. The returned-delivery repair above subsequently refreshed both general-map quotes against current main and clarified the profinite quantifier and source sentence locations.

## Second reading by Q29

- Source statement: checked `def-sfb-qlbar-subextension-map.md` (blueprint `main-20261015`, node order 1531) clause by clause: finite subextensions, inherited topologies, postcomposition, underlying ring-object interpretation, identity, and composition all agree; verdict pass.
- Source proof: checked `def-sfb-qlbar-subextension-map.proof.md` (the single paragraph, sentences one through three); the three split steps realize continuity, the general construction, and strict functoriality without adding hypotheses; verdict pass.
- Step 1: checked against the full statement of `def-sfb-padic-subfield-condensed-ring`; the subspace inverse-image calculation proves continuity and the ambient field operations give a ring homomorphism; verdict pass and elementary.
- Step 2: checked against the full statement of `def-sfb-continuous-map-condensed-ring-map`; its profinite-section postcomposition clause supplies the condensed-ring and underlying ring-object morphisms, and the displayed restriction equality supplies naturality; verdict pass and correctly non-elementary.
- Step 3: checked against the same general-map statement; its strict identity/composition clause applies to the literal inclusions, and the sectionwise equalities establish the required strict laws; verdict pass and elementary.
- New nodes: none; therefore B1–B7 and new-node duplication checks are vacuous. The two cited split nodes are existing DAG nodes, and whole-DAG searches in the worker report found no duplicate item or prerequisite.
- Edge cases: checked $E=F$, $E=F=H$, $E=\mathbf Q_\ell$, either equality in a finite-subextension chain, and the empty profinite set; each reduces to the stated identity, inclusion, or pointwise equality.
- Mathlib records: re-read the recorded searches and their verdicts; they report only related fixed-space/presheaf constructions, with no direct condensed ring-object map, so no Mathlib leaf is warranted.
- Changes in this second reading: appended this audit section only. No statement, dependency, proof step, citation quote, or search record required repair. The required dry run completed successfully: `OK (not pushed) deliver/Q29/def-sfb-qlbar-subextension-map at 1224e0b7ad: preflight passed`. The final delivery then completed successfully.
