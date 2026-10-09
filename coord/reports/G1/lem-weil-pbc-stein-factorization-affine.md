# Stage 1 repair report: `lem-weil-pbc-stein-factorization-affine`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-stein-factorization-affine.json`: repaired split, now following the proof of Theorem 37.53.5 (Tag 03H2) rather than quoting its conclusions.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-stein-universally-closed-factor.json`: new unsplit Tag 03GY factorization input; no exact Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-stein-geometric-fibre-etale-criterion.json`: new unsplit Tag 03GZ criterion; no exact Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-stein-flat-base-change-global-sections.json`: new unsplit Tag 02KH proper flat base-change input; no exact Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-stein-normalized-fibre-idempotent.json`: new unsplit formal-functions/idempotent fibre argument from Tag 03H2; no exact Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-stein-integral-global-sections.json`: Mathlib leaf, exact `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` at `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean:138`.
- `coord/reports/G1/lem-weil-pbc-stein-factorization-affine.md`: this repair report.

## Attachments

None. The existing `def-weil-pbc-stein-factorization` is cited for setup. The existing conditional Stein nodes (`lemma-weil-pbc-stein-connectedness`, `thm-weil-pbc-stein-inputs`, and `lemma-weil-pbc-proper-strict-henselian-h0`) were read and not used to avoid introducing a circular dependency into 03H2.

## WANTED

None. The Stacks source is recorded as obtained in `literature/LIST.md`; the synchronized source checkout contains `more-morphisms.tex`, `cohomology.tex`, and the tag index.

## What was wrong or incomplete

- The returned delivery had a child that restated clauses (ii)–(iii) and parent steps that only said “Theorem 37.53.5, clause ...”. That did not expose the proof of 03H2.
- The repair follows the actual proof: Tag 03GY supplies the universal relative-spectrum factorization; its universal-closed q together with separated/finite-type permanence gives properness (the 03GN image lemma is not needed here); Tag 03GZ reduces geometric connectedness to etale neighbourhood fibres; Tag 02KH supplies flat base-change of global sections; and the formal-functions/idempotent argument in lines 15334--15357 gives connected nonempty fibres.
- The general fibre homeomorphism is already part of `def-pc-scheme-fibre`, sourced to Tags 01K0/01K1, so the prior Stein-specific duplicate child was removed.

## What I could not finish, and why

The four proof-level children remain `unsplit` because Mathlib has no bundled declarations for the Stacks factorization, etale criterion, proper flat base-change theorem, or formal-functions fibre argument. No Lean was written or compiled.

Validation: `python3 tools/review_split.py lem-weil-pbc-stein-factorization-affine` passes; `python3 tools/check_dag.py` reports 0 cycles and no missing references (only the repository's unrelated reachability warnings on the current tip).

## Review by G1

I checked the repaired parent against the proof of More on Morphisms Theorem 37.53.5 (Tag 03H2) in `more-morphisms.tex` lines 15312--15357, its preceding Lemma 03GY (lines 15087--15152), Lemma 03GZ, and Cohomology Lemma 02KH. The parent no longer treats the theorem as an opaque clause: each reduction and the formal-functions/idempotent argument is represented by a named child. The properness step now cites the existing separated-cancellation node and the existing proper/finitely-presented permanence node for 01T8, while the etale base-change step cites that permanence node for proper base change. After replacing the base by `S' = Spec B`, the review checks the explicit 02KH specialization for `U = Spec R'`, namely `H^0(X_U,O) = B ⊗_B R' = R'`; the normalized-fibre statement itself contains no proof sketch and carries its 03H2/02OD/0G7X source place. I checked that the fibre homeomorphism is the already existing general statement in `def-pc-scheme-fibre` (Tag 01K1), and that the Mathlib leaf names the exact Proper.lean:138 declaration. The five children have all three required search categories, are self-contained, and now carry the parent unit `sk-thm-p1`. The delivery is accepted as a repair of the returned split.
