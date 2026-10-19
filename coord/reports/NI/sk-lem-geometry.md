# Stage-1 report: sk-lem-geometry

## Files written

- `dag/nodes/sec-smooth-purity/sk-lem-geometry.json`: split into two steps using existing nodes; mathematical hypotheses and all five conclusions preserved. Replaced the undefined node reference `[sk-prop-an]` by `[cor-pur-vector-bundle-purity]`, and added that statement dependency.
- `dag/units/sk-lem-geometry.json`: only `realized` and `realized_by` filled, since the item is the unit's key node. Both source proof paragraphs are realized by this item.
- `citations.json`: five verbatim entries, one for every node used by every proof step.
- `report.md` and authentic `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. The read-only slopmaster2 search for the item id, `nonempty_deformationToNormalConeData`, and `DeformationToNormalConeData` led to `WeilConjectures/AlgebraicGeometry/DeformationToNormalCone.lean`. I read its full declaration and surrounding structure. `AlgebraicGeometry.Scheme.Hom.nonempty_deformationToNormalConeData` at lines 168–172 has `sorry`, so it is not an attachment. The geometry-data structure by itself is not a proof, and does not include the item's derived family-object clauses.

The existing DAG node `lem-pur-dnc-section-geometry` carries an audit from a different, newer source snapshot which labels the same name closed in another module. The actual read-only checkout supplied in this brief has the sorried declaration above. I have not changed that other node or treated its recorded audit as an attachment for this item.

## WANTED

None. All sources used are available locally. No SGA source is used.

## Findings and corrections

The imported item referenced `[sk-prop-an]`, which is a unit with no node JSON. Its intended R-pi-shriek/vector-bundle-purity clause is stated by the existing `cor-pur-vector-bundle-purity`. Replacing that reference repairs B3 without changing the formula or any hypothesis. The first dry run identified exactly this unresolved reference; the item now names the actual node.

The source Lean interface is also discrepant: its theorem quantifies over every `NormalConeData d s`, and its docstring explains that the datum is not tied to the ideal of s. It explicitly gives a counterexample using the total space of a nontrivial line bundle L over a smooth projective curve B in place of the normal bundle of the zero section of A¹_B. The relative cotangent line along a proposed deformation section would restrict to O_B at one and L-dual at zero, contradicting Pic(A¹_B)=Pic(B). This is a defect of that Lean interface, not of the natural-language statement: `sk-def-purity-conv` already defines the canonical normal cone from the ideal-power graded algebra. I preserved that meaning and removed an unnecessary canonical-normal-bundle clarification from my initial draft. No mathematical statement dispute or hypothesis change remains in the delivered node.

The imported proof had uncited regular-immersion, coordinate, and dualizing-base-change inputs, as well as `elementary: null`. Searching the entire DAG and blueprint found the existing same-unit `lem-pur-dnc-section-geometry`, whose statement already supplies the exact five clauses. The brief explicitly requires reuse when a blueprint node states a needed fact, so I cite it rather than creating new clause nodes. The standard-pair purity input is the existing vector-bundle theorem prescribed by the unit. This is a one-level split using existing statements; no new theorem merely relabels the item.

## Review by NI

I read the current main-20261015 `sk-lem-geometry/_section.md` and `sk-lem-geometry.proof.md`, the chapter and unit JSON records, the older master section, the current `lem-pur-dnc-section-geometry.md` and its proof, and `cor-pur-vector-bundle-purity.md` and its proof. I also opened the current statements of all four distinct cited nodes and the current convention definitions that explain the older geometry theorem's notation. Both source proof paragraphs are realized: the Rees paragraph by Step 1, and the Coordinates/standard-pair paragraph by Steps 1–2.

Step 1 uses `sk-def-purity-conv` for the *definitions* of the ideal-defined normal cone, blow-up deformation, section invariant C(g,s)=Ls*omega_g, and family object F=L(s-tilde)*omega_(g-tilde). It uses `sk-def-sf-operations` specifically for clause (vi): the constructible exceptional inverse image on finite-type k-schemes with finite A=O_E/varpi^n coefficients, transported from the etale category. This verifies that the finite-field and finite-coefficient conventions in the older geometry node are the existing ambient convention, not an added hypothesis or an identification of adic categories. No ambient pro-etale exceptional adjoint is assumed.

Step 1 then uses the *statement* of `lem-pur-dnc-section-geometry`. I matched its clauses individually: (1) gives both geometric fibres and both derived family-fibre comparisons; (2) gives relative etale coordinates u_i=x_i/t and smoothness of pure dimension d; (3) identifies the punctured pair and supplies the canonical family-object isomorphism; (5) states base-change compatibility. The present item's etale-localization assertion is restriction to the etale neighborhoods in those coordinates and the same base-change clause. No regularity of B or globally affine coordinate system is inserted. I use none of the proof-internal constructions of that node as though they were additional statement clauses.

Step 2 again cites `lem-pur-dnc-section-geometry`, now for its clause (4): the standard deformation product, x_k=t u_k, and the family-object identification a*(0*omega). It cites `cor-pur-vector-bundle-purity` for its stated special case omega_pi ≅ Lambda_E(r)[2r]. Substituting the trivial rank-d vector bundle E=A^d_B and pulling back first by the zero section, then by a, gives precisely the asserted standard-pair formula. The pullback of a constant twisted sheaf is the corresponding constant twist in these conventions. The theorem explicitly includes base-change compatibility. It applies to K=Lambda_B, a degree-zero free rank-one coefficient complex, so there is no missing boundedness or finite-Tor hypothesis. No general smooth-purity theorem, and no integral/rational coefficient transport, is used.

I checked d=0 (empty coordinate list, zero-rank bundle, identity twist/shift), empty B, and the identity and zero base-change fibres. For an etale g of relative dimension zero the section image may be only an open-and-closed part of V; the proof never identifies V with B, so the complement persisting only over the punctured line is allowed. In rank one for the standard pair the ring equation is x=t u, with special fibre the normal line and unit fibre the original line. The source's nontrivial-line-bundle example is excluded by the ideal-defined normal cone already in the conventions, rather than by a new assumption.

For B–E: there are no new-node statement-only, leaf-line, or same-tag obligations; no elementary fact or clause was created as a node. Every definition and theorem cited by a step was opened, and each exact use is in its statement (C1/C4). The full theorem duplicate is reused rather than recreated; `blueprint.same_as` records it. Both theorem uses are in this unit or the explicitly cited `sk-prop-an` route; the recorded vector-bundle tool explanation does not change the unit route. The proof-dependency list is the exact union of the step uses, and every quote in citations.json is copied verbatim. I did not change a different node, any chapter, or the unit's statement/steps.

## Blueprint and Mathlib searches

Whole-DAG keyword searches for Rees, normal cone, smooth-section geometry and deformation, plus `tools/blueprint_refs.py search 'normal cone'`, `search 'Rees algebra'`, and `search 'Geometry of the deformation'`, found the same-as geometry node and the existing definitions. No new node was needed.

All searches in the item were run with `msearch.py NI sk-lem-geometry` and are recorded exactly by tool/query in searches.jsonl. Two LeanFinder phrasings returned standard-smooth local-chart results and unrelated manifold/vector-bundle results. I read the returned smooth-chart API in `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:120–230`; it defines local standard-smoothness and its stability, not DNC geometry or derived family comparisons. The first Loogle query was rejected for unknown project identifier `DeformationToNormalConeData`, so its verdict explicitly says it is not evidence of absence; a valid quoted-name query was also run. The Mathlib-source grep for deformation/normal-cone/extended-Rees terminology returned zero hits. LeanSearch returned manifold trivialization results. None supplies the whole item, or a one-line specialization proving its clauses. No unrun search was recorded.

## Not duplicates

No new nodes. `sk-lem-geometry` vs `lem-pur-dnc-section-geometry`: these existing imported blueprint nodes state the same geometry in their respective notation layers. The latter is reused, and the former records it in `same_as`. No new duplicate is introduced.

## Unfinished work and validation

No one-level split work remains. The existing supporting nodes retain their own independent status. The required second reader will review and deliver; this worker does not push. Only stage 1 was performed: no Lean edits, compiler, Lake or build commands, and no manual git commands.

The earlier attempt was blocked by temporary inode exhaustion during the delivery tool's DAG-baseline extraction, recorded in `dry-run-space-failure.log`. At resumption `/tmp` had approximately 521,000 free inodes, so the normal required wrapper was retried without changing any shared tools or temporary files.

On resumption I reread the current item, chapter and unit, both current geometry statement/proof files, the current vector-bundle statement/proof, and the actual statements of `sk-def-purity-conv`, `sk-def-sf-operations`, `def-pur-conventions`, `def-pur-dnc-section-family`, `def-pur-section-invariant`, and `def-pur-co-smoothness`. I reran the whole-blueprint searches and the item searches with all four msearch kinds, including the second LeanFinder phrasing. Its ranking changed, so an additional results entry records that actual response rather than altering the genuine earlier response. The source grep remained empty; the semantic hits still concern standard-smooth charts or differential-geometric vector bundles. I read the pinned smooth-morphism API to exclude a one-line match. No new node is needed. I verified all five citation quotes as literal substrings of the current cited statements and checked the exact union of proof dependencies.

The declared source of `def-pur-conventions` is still the older master path; the equivalent current file is under `sec-six-functors-basics/sk-def-purity-conv/`. Both its finite-stage restriction and the current exceptional-inverse-image definition agree with the finite coefficient stage used here. In particular, I checked the finite-type k-scheme and separated-morphism domains inherited through the convention's exceptional functor. I also read the actual old Lean theorem and its explicit unrelated-line-bundle counterexample; that theorem is sorried and is not attached.

Validation uses `python3 /home/ubuntu/weil-launcher-nt/deliver.py NI sk-lem-geometry --no-push`; the final result is retained in `dry-run.log`. The second reader performs delivery.

## Second reading by NI

- Item statement: checked every hypothesis and each of clauses (1)–(5) against `sk-lem-geometry/_section.md` at blueprint order 1944; verdict: exact statement preserved, including the finite-coefficient conventions, arbitrary base change, and the standard-pair twist and shift.
- Step 1: checked against the Rees-description paragraph of `sk-lem-geometry.proof.md`, the statements of `sk-def-purity-conv`, `sk-def-sf-operations` (vi), and `lem-pur-dnc-section-geometry`; verdict: the cited statements provide the ideal-defined cone, family objects, finite exceptional inverse image, fibre comparisons, coordinates, punctured trivialization, and base change. The existing geometry theorem is used through its statement, with no proof-internal fact imported.
- Step 2: checked against the Coordinates paragraph of `sk-lem-geometry.proof.md` and the statements of `lem-pur-dnc-section-geometry` clause (4) and `cor-pur-vector-bundle-purity`; verdict: the chart equation, standard-pair family object, rank-d vector-bundle purity specialization, pullback, and base-change compatibility give exactly clause (4). The empty-coordinate case (d=0) is included.
- New nodes: none; therefore B1–B7, Mathlib-leaf declarations, and new-node source checks are vacuous. I searched the DAG for the geometry and vector-bundle facts and reused the existing nodes rather than duplicating them.
- Edge cases and hypotheses: checked (d=0), empty (B), zero and identity fibres, and the rank-one chart (x=tu); the section remains closed and the proof does not identify an arbitrary open with (B). The ideal-defined normal cone excludes the unrelated auxiliary-normal-cone counterexample in the sorried Lean interface.

Changes made in this second reading: none to the item, citations, searches, or DAG nodes. I added this review section only; the prior dangling `[sk-prop-an]` reference and its citation replacement were already repaired by the worker. The dry-run delivery check was rerun and remains green.
