# Stage-1 report: pur713-def-qbar-ring

## Files written

- `dag/nodes/sec-smooth-purity/pur713-def-qbar-ring.json`: marked split and reused the existing node `sk-def-sfb-qlbar-condensed` as its statement dependency; no new nodes.
- `citations.json`: `[]`, because this is a definition with no proof steps.
- `report.md`.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for `pur713-def-qbar-ring`, the likely condensed-ring declaration names, and the exact finite-subextension wording. No sorry-free project declaration states this item. The upstream master source is reference material only and contains no finished-proof attachment for this stage-1 item.

## WANTED:

None. The current blueprint source and the existing DAG node containing the same definition are present locally.

## What was wrong

The imported item was left unsplit even though the whole definition already occurs in the existing blueprint/DAG node `sk-def-sfb-qlbar-condensed` (under the pro-etale-coefficients chapter). That node states the same presheaf of continuous maps whose image lies in one finite subextension, with the same valuation topology and precomposition restriction. It also includes additional sheaf and ring-object assertions, but those extra assertions are not silently added to this item's statement. I therefore added the existing node as `stmt_deps`, set `status` to `split`, and recorded it under `blueprint.same_as`. No duplicate child node was created.

The related node `det-def-sfb-qlbar-condensed-sheaf` is a theorem about sheafhood and is not needed to state this definition. The existing `pur713-def-continuous-rings` definition handles the finite-subfield continuous-function cases but does not state the algebraic-closure finite-subextension condition, so it is not a substitute for `sk-def-sfb-qlbar-condensed`.

## What could not be finished

Nothing remains for this one-level definition split. The existing `sk-def-sfb-qlbar-condensed` node remains the shared source of the underlying notion and carries its own downstream proof obligations.

## Review by NM

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, the worker role, delivery-errors sections B–E, the item node, its chapter and unit records, and the current main-20261015 blueprint files. The item's source is `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sp-coefficient-towers/pur713-def-qbar-ring.md`; it is definition-only and has no proof steps.

For the duplicate check I read the full statement of `dag/nodes/sec-proetale-coefficients/sk-def-sfb-qlbar-condensed.json` and its blueprint source. It introduces a prime `ell`, an algebraic closure of `Q_ell` with the valuation topology, finite subextensions, and the section formula
`{a in C(S,Qbar) | a(S) subseteq E for some finite subextension E}`, with pointwise operations and precomposition. This contains exactly every clause of the present item's definition. I also read `det-def-sfb-qlbar-condensed-sheaf`; it proves sheafhood but does not replace the definition. The statement dependency therefore says precisely what this item takes from the existing node.

I searched the whole blueprint with `python3 tools/blueprint_refs.py search 'finite subextension continuous map Qbar condensed ring'` and with the item id, and searched the DAG for `finite subextension`, `pur713-def-qbar-ring`, and the condensed-ring declaration names. The only exact blueprint duplicate is `sk-def-sfb-qlbar-condensed`; the item itself is retained because its imported chapter/unit identity and shorter definition are part of the target DAG. No new node is needed, so there are no proof-step citations and `citations.json` is correctly empty.

I checked delivery-errors B–E explicitly. There is no new statement to split, no hidden proof step, no new notation, and no new Mathlib leaf. The only cited node is the existing duplicate definition, and its statement supplies the complete presheaf formula used here (C4). No non-elementary fact is used beyond that definition (C1). I did not cite the sheaf theorem as if it were a definition, did not restate a clause as a new child, and did not introduce an off-route theorem or cycle. Edge cases are covered by the definition: the empty profinite set has the unique empty map, a constant map lands in `Q_ell`, and the finite subextension may depend on each section `a` rather than on `S` globally. The statement expressly excludes the presheaf of all continuous maps to `Qbar`, matching the source.

Mathlib searches were run through the required `msearch.py` interface for the item: LeanFinder query `continuous maps from profinite sets to Qbar with image in a finite subextension form a condensed commutative ring`, Loogle query `Condensed, RingHom, IntermediateField`, grep query `finite.*subextension|subpresheaf|PadicAlgCl` in `Mathlib/Condensed`, and LeanSearch query `Continuous maps from profinite sets to the algebraic closure of p-adic numbers with image in one finite subextension form a sheaf of commutative rings`. The hits were generic condensed constructors, continuous-function sheaves, or `PadicAlgCl`; none states this specialized finite-subextension-valued presheaf. Since the item is a project definition already represented by the existing DAG node, no Mathlib match is claimed.

## Second reading by NM

- Item statement: checked against the blueprint source `pur713-def-qbar-ring.md` (node order 2475), clause by clause; the presheaf, valuation topology, finite-subextension condition, section-dependent choice of subextension, restriction by composition, and exclusion of all continuous maps agree.
- Statement dependency `sk-def-sfb-qlbar-condensed`: checked its complete DAG statement and source section; it defines the same finite-subextension-valued continuous-map presheaf and supplies every notion used by the item. Its additional sheaf and ring-object assertions are not imported into the item.
- Proof steps: none (definition-only item); `citations.json` remains empty.
- New nodes: none; the duplicate search found the existing node, so no B1–B7 or Mathlib-leaf review is required. Existing-node searches and the recorded Mathlib searches were checked for actual queries and results.
- Edge cases: checked the empty profinite set (unique empty map), constant sections (take the base field), and the fact that the finite subextension may depend on the section; all are covered by the statement.

Changes made in this second reading: added this explicit audit section only. No node or citation data required repair.
