Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-pic-affine.json`: item, statement split; Mathlib searches found no match (LeanSearch unavailable).
- `dag/nodes/sec-curve-estimates/lem-sc-pic-affine-quotient.json`: statement node for the sorry-backed quotient presentation; Mathlib searches found no match (LeanSearch unavailable).
- `citations.json`: verbatim citations for every proof-step dependency.

Attachments:

- `AlgebraicGeometry.IsConnectedCurve.surjective_zsmul_pic_and_finite_torsionBy` is the existing sorry-free divisibility declaration, but it proves only the divisibility/torsion clause and is not an attachment for the full item.

WANTED:

- None.

What was wrong in the imported node:

- The imported proof was one paragraph and used the quotient presentation without a DAG node. The source Lean file has that presentation as the separate sorry-backed theorem `exists_addEquiv_pic_quotient`; I created `lem-sc-pic-affine-quotient` with its exact mathematical content and audit declaration.
- The item proof now has two steps: the quotient presentation, followed by divisibility and finite torsion via the existing quotient-torsion lemma and abelian-variety estimate. The imported `uses_not_cited` entry for `def-sc-curves` remains metadata from the blueprint and is not needed by the rewritten steps.

What I could not finish:

- The quotient presentation remains a sorry-backed Lean theorem in the source, as recorded in the child node's `lean_audit.slopmaster2` field.

## Review by C1

I read the item source in `WeilConjectures/AlgebraicGeometry/Curve/Affine.lean`, lines 233--293, including both `exists_addEquiv_pic_quotient` and `surjective_zsmul_pic_and_finite_torsionBy`, and the blueprint proof in `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd-affine/lem-sc-pic-affine.md`. The first item step cites `lem-sc-pic-affine-quotient`, whose statement explicitly supplies the compactification, Jacobian, quotient, and boundary-generated subgroup. The second step cites that same subgroup statement, `thm-av-final` clause (d) for divisibility and clause (c) for finite prime-to-characteristic torsion, `lem-sc-divisible-quotient-torsion` for the exact sequence controlling quotient torsion, and `def-sc-mult-n` for the identification of point torsion with the torsion subgroup scheme. I checked each cited node's statement and copied the used sentences into `citations.json`; the finite generation of Lambda and finiteness of its modulo-n quotient are elementary from the finite boundary set and the stated generators. I also ran the required LeanFinder, Loogle, grep, and LeanSearch searches twice with distinct phrasings; LeanSearch was unavailable and is recorded as such. No existing DAG node or Mathlib declaration states the quotient presentation.

## Second reading by C1

- Item statement: checked against `WeilConjectures/AlgebraicGeometry/Curve/Affine.lean`, theorem `surjective_zsmul_pic_and_finite_torsionBy` (the hypotheses `IsConnectedCurve`, `Smooth`, `IsAffine`, and `n` prime to `char k`); verdict: mathematically consistent, including the genus-zero and characteristic-zero cases.
- Item step 1: checked against the quotient-presentation theorem `exists_addEquiv_pic_quotient` at lines 233--255 and the new quotient node; verdict: the cited statement supplies the compactification, Jacobian, finitely generated boundary subgroup, and quotient.
- Item step 2: checked against `thm-av-final` clauses (c,d), `lem-sc-divisible-quotient-torsion`, `def-sc-mult-n`, and the quotient node; verdict: divisibility descends through the quotient and the short exact sequence gives finite torsion from finite boundary generation and finite Jacobian $n$-torsion.
- New node `lem-sc-pic-affine-quotient`: checked for B1--B7, the compactification source, the Jacobian identification, and all recorded Mathlib searches; verdict: required auxiliary statement, with no Mathlib match. Repaired the statement so $\\overline C$, $S$, and $P_0$ are defined before use and the subgroup is explicitly defined in $J(k)$.
- Small cases: the boundary is nonempty for an affine connected curve of dimension one; for $\\mathbf A^1$ the Jacobian and quotient are trivial; for $n=1$ the divisibility and torsion claims are immediate; no contradiction found.
- Citations: reread every quoted node statement and verified each quote is verbatim in `citations.json`; verdict: all citations support the corresponding step.
- Delivery checks: dry-run `deliver.py C1 lem-sc-pic-affine --no-push` passed before this repair; it will be rerun after the repair.

Changes made: repaired the quotient node's undefined notation and recorded this second reading; no proof dependency or target statement was weakened.
