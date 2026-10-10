# Stage 1 report: lem-sc-lft-over-field-jacobson-space

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-lft-over-field-jacobson-space.json`: statement node, split; no new nodes.
- `citations.json`: verbatim quotes for both cited definition nodes.

## Attachments

None. No sorry-free slopmaster2 declaration carries the item (the item tag and its mathematical keywords were searched in `~/weil-src-slopmaster2/WeilConjectures`).

## WANTED

WANTED: `literature/stacks-project/varieties.tex`, Tag 0478 (lemma-locally-finite-type-Jacobson), because the imported repository contains the citation but not the source text.

## Review by K1

I read the item JSON, its blueprint ancestor `lem-sc-degree-2g1-very-ample`, the unit `sk-thm-picard-rr`, and the existing definition nodes. The item statement agrees with Tag 0478(2): it asserts the Jacobson density condition for a scheme locally of finite type over a field, with the finite-type and closed-point notions supplied by the two cited definitions. I also searched the whole DAG and blueprint for Tag 0478, Jacobson-space wording, and the item id; no existing node duplicates this statement, and no new dependency was needed.

Step 1 uses only the statement of `def-weil-finite-type-morphism`, specifically its sentence that finite type over a field refers to the structure morphism. I checked the Mathlib source at `Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:113-117`: a field's spectrum has a Jacobson-space instance, and `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace` takes a locally finite type morphism into a Jacobson space to a Jacobson-space source. The field hypothesis supplies the required Jacobson-ring instance. Step 2 uses the exact definition supplied by `def-weil-closed-points` and unfolds Mathlib's `JacobsonSpace` class (`Mathlib/Topology/JacobsonSpace.lean:70-75`), whose closure equality is precisely density of closed points in each closed subset. The elementary flag is limited to this direct unpacking.

I tested the edge cases conceptually: for `X = Spec k`, the assertion is the usual fact that the unique point is closed; for the empty scheme, the closure equality is vacuous; and for an arbitrary closed subset `Z`, the conclusion is exactly the class field `closure (Z ∩ closedPoints X) = Z`. The required Mathlib searches were run in both phrasings for LeanFinder and Loogle, with LeanSearch recorded as unavailable and the grep queries recorded as returning no hits through `msearch.py`; the positive declaration was independently read in the Mathlib source.

## What was checked

The split has no new unsplit node, no cycle, and `proof_deps` is exactly the union of the two step citation lists. The item blueprint `from.place` and `same_as` fields were already populated and remain unchanged; the split report records which blueprint paragraph each step realizes.

## Second reading by K1

- Item statement: checked against Stacks `varieties.tex`, Tag 0478, part (2), and the definitions of finite type over a field and closed points; verdict: agrees hypothesis by hypothesis.
- Step 1: checked the structure morphism convention and Mathlib's `LocallyOfFiniteType.jacobsonSpace` at `Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:113-117`, including the Jacobson instance for the spectrum of a field; verdict: valid.
- Step 2: checked against Mathlib's `JacobsonSpace` closure condition at `Mathlib/Topology/JacobsonSpace.lean:70-75` and the cited closed-point definition; verdict: elementary unpacking is valid.
- New nodes: none; B1-B7 and duplicate-node checks are vacuous. The stale maintainer metadata in the item node was corrected so `created.item` names this item.
- Edge cases checked: `Spec k` has the expected closed point, the empty scheme is vacuous, and the conclusion for an arbitrary closed subset is exactly the Jacobson closure equality.
- Delivery checks: citations quote the exact cited statements; blueprint references and search records are present; no cycle or additional dependency was introduced.

Changes: corrected `created.item` from an unrelated item id, and added this second-reading record. The source was read from the available Stacks checkout at `/home/ubuntu/c1-stacks-review/varieties.tex` because the repository mirror lacks `literature/stacks-project/varieties.tex`.
