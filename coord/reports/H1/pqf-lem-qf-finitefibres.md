Files written:

- `pqf-lem-qf-finitefibres.json` (statement; Mathlib search found a general finite-fibre equivalence, not the full project statement).
- `citations.json` (quotes for both proof steps).

Attachments: none.

WANTED: `literature/stacks-project/morphisms.tex`, Tag 02NH, because the Stacks source text is not present in this checkout; the proof follows the imported blueprint proof and its cited tag.

The imported node had one paragraph combining both implications. I split it into explicit forward and converse steps, retained the exact statement, and changed status to `split`. No new node was created: the only natural helper would restate the finite-fibre clause of this item, which is forbidden by the no-clause split rule. The Mathlib search found `AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton` at `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean:325`; it requires the locally-finite-type and quasi-compact hypotheses and therefore is a generalization supporting the algebraic step, not an attachment.

## Not duplicates

`pqf-lem-qf-finitefibres` vs `pqf-lem-finite-qf`: the latter proves only that finite morphisms are quasi-finite; this item characterizes quasi-finiteness by finite type, quasi-compactness, and finite fibres.

## Review by H1

I read the target node, its blueprint proof, the existing definition node `pqf-def-quasifinite`, and `def-weil-pbc-scheme-conventions`. Step 1 takes exactly the definition's finite-type and isolated-fibre clauses, then uses the convention's equivalence of finite type with locally finite type plus quasi-compactness; the finite-type-over-a-field argument is checked against Mathlib's finite-fibre equivalence search result. Step 2 verifies the same hypotheses in the reverse direction, uses the definition's affine-local criterion at each point, and applies the finite-type algebra argument to obtain an isolated fibre point. I checked every citation quote verbatim against its node file and recorded both searches and the unavailable LeanSearch service. I also checked the source tree for the blueprint tag and found no sorry-free project declaration to attach.

What could not be finished: the cited Stacks PDF/source is absent locally, so the report records it as WANTED; no Lean compilation is permitted at stage 1.

## Second reading by H1

Item statement: checked against Stacks Tag 02NH, Lemma 29.21.10; the three conditions in clause (2) are equivalent to the imported finite-type formulation under the project convention.

Step 1: checked against Tag 02NH proof lines 28-29 and the statements of `pqf-def-quasifinite` and `def-weil-pbc-scheme-conventions`; replaced the unsupported Mathlib/dimension argument with the singleton-open quasi-compactness argument.

Step 2: checked against Tag 02NH proof line 29 and the statements of `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs` and `pqf-lem-qf-locqf-qc`; made the affine fibre and local quasi-finiteness route explicit.

New nodes: none; existing helper statements were searched in `dag/nodes/` and cited rather than duplicated.

Small cases checked: the empty scheme, `Spec k -> Spec k`, and a finite disjoint union of field points satisfy both sides; `A^1_k -> Spec k` fails both finite-fibre and quasi-finite conditions as expected.

Changes: repaired both proof steps, added the two existing helper citations and verbatim citation entries, and updated `proof_deps`; the prior claim that Mathlib's finite-preimage theorem directly supplied the project statement was removed.
