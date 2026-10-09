# Stage 1 report: `lem-weil-pbc-z-g-ring`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-z-g-ring.json` — existing statement node, now `status: split`, with four proof steps and exact source tags.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-z-localizations-dvr.json` — new public unsplit statement node for the prime localizations of `Z` (Stacks Tags 034X and 00PD).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-dvr-completion-regular.json` — new public unsplit statement node for regularity of the completion map of a characteristic-zero Noetherian local DVR (Stacks Tags 07PX, 0AP1, 00MB, and 07BZ).
- `coord/reports/C1/lem-weil-pbc-z-g-ring.md` — this report.

The assigned node follows More on Algebra Proposition 07PX, item (3). Its proof dependencies are exactly the union of the four step `uses` lists. Both new reusable statements are statement-only, `status: unsplit`, carry their own complete statements, exact source places, and LeanSearch, Loogle, and Mathlib-source-grep records. No Lean declaration or module exists on either source branch, so no module attachment applies.

## Attachments

None. The assigned statement and both reusable support statements have `lean_audit` state `none` on `master` and `slopmaster2`.

## WANTED

None. The cited Stacks sources are available in the fetched literature checkout.

## What was checked or corrected

The imported statement was retained exactly: `Z` is a G-ring in the sense of `def-weil-pbc-g-ring`. The imported empty proof was expanded along the source. The first step records the arithmetic localization fact as the public node `lem-weil-pbc-z-localizations-dvr`; the second handles the zero prime, where `Z_(0) = Q` and the completion is the identity; the third applies the corrected characteristic-zero DVR-completion node at every nonzero prime, explicitly recording that the fraction field of `Z_(p)` is `Q`, and names the source's completion-DVR, completion-flatness, generic-fibre and closed-fibre ingredients; the fourth closes the cases against the definition of a G-ring. The proof stays in unit `sk-thm-p1` and introduces no route departure.

The exact Stacks citations checked are More on Algebra Proposition 07PX (tag 07PX), item (3), Algebra Lemma 034X (tag 034X) for Dedekind localizations, Algebra Lemma 00PD (tag 00PD) for the DVR characterization, More on Algebra Lemma 0AP1 (tag 0AP1) for completion preserving the DVR property, Algebra Lemma 00MB (tag 00MB) for completion flatness, and More on Algebra Definition 07BZ (tag 07BZ) for regular ring maps. Before retaining the inline DVR description, I searched the current DAG for duplicate notions and cited the existing public criterion node [lem-sc-normal-dim1-dvr] (which itself records Tag 00PD) in both new statements; no existing Dedekind statement node covers the Z arithmetic assertion, so the Dedekind description remains inline with Tags 034W/034X. The returned arbitrary-DVR completion claim was corrected: the reusable completion statement now assumes characteristic zero for `Frac(A)`, identifies the generic fibre as `Frac(A^)=A^ tensor_A Frac(A)` and the closed fibre as `A^/mA^=A/m`, and the parent applies it only after recording `Frac(Z_(p))=Q` of characteristic zero. The two new nodes are reusable proof facts, not private claims, and are cited by the assigned node.

No statement, blueprint route, or existing node outside this item was changed. No Lean was written or compiled, as required for Stage 1.

## What could not be finished

Nothing remains for this one-level split. The two support nodes intentionally remain unsplit Stage 1 items because Mathlib has no matching G-ring, geometrically-regular-fibre, or regular-ring-map theorem.

## Review by C1

I independently read More on Algebra Proposition 07PX (tag 07PX, item (3), around lines 12652–12671), Algebra Lemma 034X (Dedekind localizations), Algebra Lemma 00PD (DVR characterization), More on Algebra Lemmas 0AP1 and 00MB, and Definition 07BZ. I checked the returned points against the source and against the cited DAG nodes as follows.

1. The `lem-weil-pbc-z-localizations-dvr` statement now explicitly cites `[def-weil-pbc-noetherian-ring]` and `[def-weil-pbc-localization-at-prime]`. It introduces the two notions that had previously been left implicit: a Dedekind domain is stated as a Noetherian integrally closed domain of dimension one (034W/034X), and a discrete valuation ring is stated as a Noetherian local domain of dimension one with principal maximal ideal (00PD), with the existing reusable criterion `[lem-sc-normal-dim1-dvr]` cited rather than creating a duplicate definition node. Its `stmt_deps` name all three cited nodes, and the source supports the zero-prime field and nonzero-prime localization cases.
2. The `lem-weil-pbc-dvr-completion-regular` statement gives the same inline DVR definition, cites `[lem-sc-normal-dim1-dvr]`, and now assumes `char(Frac(A))=0`. It explicitly identifies the generic fibre `Frac(A^)=A^ tensor_A Frac(A)` as geometrically regular by characteristic zero and the closed fibre `A^/mA^=A/m` as a field, while retaining the Noetherian and prime-localization definitions in both the statement and `stmt_deps`, alongside the existing completion, flat-map, and G-ring definitions. The source route remains 07PX with 0AP1, 00MB, and 07BZ.
3. In the parent item, the zero-prime step now cites `lem-weil-pbc-field-regular-ring`; its `uses` list and `proof_deps` include that existing Mathlib-leaf node, and the step is correctly marked `elementary: false`. The argument therefore uses the reviewed field-regularity result instead of calling the regularity assertion elementary.
4. The parent nonzero-prime step now records that `Frac(Z_(p))=Q` has characteristic zero before applying the corrected support node, and names the generic and closed fibres. The remaining steps and sources still follow 07PX: the first uses the localization support node, and the fourth assembles all primes into the G-ring definition. The two support nodes remain public reusable nodes with their three required Mathlib searches and `created.item` equal to this item.

The repaired branch was rebased onto the current `origin/sheaf-dag` before review. Its final diff is restricted to the assigned node, its two support nodes, and this report, and the final history has one squashed item commit on that base. `python3 tools/preflight_delivery.py C1 lem-weil-pbc-z-g-ring` and `python3 tools/review_split.py lem-weil-pbc-z-g-ring` pass. `python3 tools/check_dag.py` reports the repository's eight pre-existing reachability diagnostics, but zero cycles or self-loops; the repaired nodes add no diagnostic. All JSON files parse successfully; no Lean compilation was run.
