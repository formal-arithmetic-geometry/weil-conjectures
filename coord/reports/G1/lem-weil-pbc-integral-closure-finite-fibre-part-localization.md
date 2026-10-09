# Stage 1 report: `lem-weil-pbc-integral-closure-finite-fibre-part-localization`

1. Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-closure-finite-fibre-part-localization.json` — existing statement node, now `status: split`; proof follows Stacks Tag 09XH in five steps.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-closure-finite-fibre-quasi-finite.json` — new statement node, `status: unsplit`; Mathlib verdict no match; cites `[pqf-def-quasifinite]` and Stacks Algebra Tags 00PL (definition), 00PK (isolated-fibre criterion), and 00PM (finite-fibre criterion).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-closure-zariski-main-away.json` — new statement node, `status: mathlib`; exact match `Algebra.ZariskisMainProperty.of_finiteType`, `Mathlib/RingTheory/ZariskisMainTheorem.lean:660-663`, with `[Algebra.FiniteType A B]`, prime `q`, `[q.IsPrime]`, and `[Algebra.QuasiFiniteAt A q]`; the property itself is at lines 75-78.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-closure-finite-fibre-image-clopen.json` — new statement node, `status: unsplit`; Mathlib verdict no match; cites affine spectra, integral-map closedness, and clopen/idempotent interfaces.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-closure-finite-fibre-choose-g.json` — new statement node, `status: unsplit`; Mathlib verdict no match; now repeats the full finite-type, fibre decomposition, integral-closure, product, and neighbourhood hypotheses rather than referring to another child.
- `coord/reports/G1/lem-weil-pbc-integral-closure-finite-fibre-part-localization.md` — this report.

2. Attachments

None.

3. Source

The proof source is `literature/stacks-project/more-algebra.tex` on `sheaf-dag`: Lemma Tag 09XH is lines 2502-2510 and its proof is lines 2512-2550. The nodes cite those local line ranges. The proof's external Algebra references are Tags 00PL/00PK/00PM (quasi-finite), 00Q9 (Zariski Main), 00HZ/00GU (closedness via going-up), 00EE (clopen product), and 00E9 (local criterion). The source file is not present in this sparse worker checkout, so the line references were checked against the matching sheaf-dag literature checkout and the public Tag pages.

4. Corrections and findings

- The imported statement is correct against Stacks Tag 09XH (local source lines 2502-2550).
- The imported node had no proof. Its hidden arguments are now explicit: quasi-finiteness on the finite fibre component; the Zariski Main localization; the clopen image/product decomposition; and the prescribed idempotent lift yielding the localization isomorphism.
- The Zariski Main step is a Mathlib leaf via `Algebra.ZariskisMainProperty.of_finiteType` at `Mathlib/RingTheory/ZariskisMainTheorem.lean:660-663`; its `Algebra.QuasiFiniteAt` typeclass and prime `q.IsPrime` hypotheses are explicit. The other three interfaces have no exact Mathlib theorem and remain unsplit.
- `python3 tools/review_split.py lem-weil-pbc-integral-closure-finite-fibre-part-localization` passes with four new nodes. `python3 tools/check_dag.py` reports 0 cycles and six pre-existing reachability warnings for unrelated nodes.

5. Could not finish

- The three unsplit child statements need their own later Stage 1 splits. No Lean was written or compiled, as required.

## Repair review by G1

I checked the five steps against the local line ranges of Stacks 09XH and its cited 00Q9 route. The repair makes choose-g self-contained, adds the quasi-finite definition and exact Tags 00PL/00PK/00PM, adds affine-spectrum/integral-map/clopen node citations to image-clopen, and records the exact Mathlib declaration lines and all of its map hypotheses. Each new node retains its statement, source, chapter/unit metadata, and four required Mathlib search modes. No target or unrelated node was changed.
## Review by G1

I independently checked the repaired statements against `more-algebra.tex` lines 2512-2550 and the cited Algebra Tags. The choose-g node now carries every hypothesis it uses; the quasi-finite node names its definition and 00PK/00PM criteria; the image-clopen node cites the affine-spectrum, integral-map, and clopen decomposition interfaces. The Zariski Main leaf records declaration lines 660-663, property lines 75-78, and the exact `FiniteType`, prime, and `QuasiFiniteAt` hypotheses. The branch passes `review_split.py` and `check_dag.py --cycles`, with only pre-existing reachability notices. I accept this repair.
