# Stage-1 repair report: lem-trf-log-regular-monomial-tor

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-log-regular-monomial-tor.json`: repaired four-step split, with the chart-comparison, coefficient-localization, and long-exact-Tor citations made explicit.
- `dag/nodes/sec-trace-formula/lem-trf-log-chart-face-tor-comparison.json`: new statement-only supporting node; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-tor-localization-on-spec.json`: new statement-only supporting node; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-tor-flat-base-change.json`: repaired source and blueprint ancestry; Mathlib searches found no match.
- `citations.json`: verbatim quotations for every node used by Steps 1–3.
- `searches.jsonl`: retained searches plus the repair searches; every repair-node query was run with `msearch.py` and its result was read.

## Attachments

None. I rechecked `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag and its mathematical names; there is no sorry-free declaration stating this item or either new supporting statement.

## WANTED:

None.

## What was wrong and what changed

The returned Step 1 identified a genuine proof gap. The old sentence identified a Tor map over the sharp monoid algebra without identifying it with the given chart over `Z[P]`. I added `lem-trf-log-chart-face-tor-comparison`, whose statement explicitly includes (i) localization at the face of chart elements that become units, (ii) a section and the splitting `P_F ≅ P_x ⊕ F^gp`, (iii) the unit homomorphism relating the supplied chart to the sharp chart, and (iv) the resulting change-of-rings Tor isomorphism. Step 1 now cites that statement and separately cites the sharp-chart, face-sharpening, and Kato Tor statements, so each cited node says exactly what the step takes from it.

The returned Step 2 used “vanishing is local on Spec A” without a node. I added `lem-trf-tor-localization-on-spec` and use it after the strict-henselian faithfully-flat descent. The returned Step 3 cited only the Tor definition; it now cites `lem-weil-pbc-tor-long-exact-first-variable` for the exact sequence and the Tor definition only for the resolution convention. The flat-base-change node now describes Tag 00M8 accurately as the free-resolution proof applied to a fixed base ring with a flat coefficient extension; its `blueprint.from.via` starts with the delivered item followed by the item’s via list. `split_report.tool_uses` is now a list of `{node, why}` objects and contains only the three generic off-unit tools actually used.

## Not duplicates

- `lem-trf-log-chart-face-tor-comparison` vs `lem-trf-kato-tor-independence-chart`: the new node is a comparison isomorphism from a supplied nonsharp chart to its sharp face localization; the existing node is the Tor-vanishing theorem after a sharp strict-henselian chart.
- `lem-trf-log-chart-face-tor-comparison` vs `lem-trf-fs-face-sharpening`: the new node concerns chart algebras, unit twists, and Tor; the existing node is only the fine-saturated monoid localization and sharpening statement.
- `lem-trf-tor-localization-on-spec` vs `lem-trf-tor-flat-base-change`: localization at a prime is the former’s coefficient-localization conclusion; the latter is the general flat coefficient-base-change isomorphism.
- `lem-trf-tor-localization-on-spec` vs `lem-sc-faithfully-flat-tensor-zero`: the former identifies localized Tor groups; the latter only reflects zero after faithful-flat tensoring.

## Review by Q64

I reread the item against ILO Exposé VIII, the proof of Lemma 3.4.3 (printed p. 110), and the surrounding §3.4–§3.5 discussion, and checked the edge cases `H=empty`, `H=P`, `P=0`, and `P=N^2`. The item statement and image clause are unchanged. For the new chart-comparison statement I read Exposé VI 3.7(a), p. 75, and Exposé VIII p. 110; its hypotheses introduce the local ring, face, quotient, section, sharp chart, unit twist, and monoid ideal, and its conclusion is only the Tor comparison, so it does not restate the item. For the new localization statement I checked the free-resolution argument underlying Stacks Tag 00M8 and tested it at a field localization and at a localization where the Tor module is already zero. The flat-base-change node is the same generic statement as before, but its source now says exactly how the Tag 00M8 free-resolution argument is being specialized.

Step 1 uses the existing face-sharpening statement for `P_F`, `F^gp`, the sharp quotient and its splitting data; the existing sharp-chart statement for the etale-local chart inducing the chosen characteristic; the new chart-comparison statement for all four previously omitted identifications; and the Kato node for vanishing of the resulting sharp-chart Tor. I verified each quoted statement literally in the cited node file and copied those statements into `citations.json`. Step 2 uses the strict-henselization faithful-flat statement, the repaired flat coefficient-base-change statement, faithful-flat tensor-zero reflection, and the new coefficient-localization statement; these supply respectively the map, the comparison isomorphism, descent of zero, and the local-to-global implication. Step 3 uses the Tor projective-resolution definition and the existing first-variable long-exact-Tor statement; the latter supplies the kernel identification for `0 -> I -> R -> R/I -> 0`. Step 4 is the two-line basis calculation and is marked elementary.

I searched the whole DAG and the main-20261015 blueprint before adding each supporting node; no node with the same statement or a more general statement was found. I reran the required LeanFinder, Loogle, grep, and LeanSearch queries for the repair statements. The search log records Loogle failures as `unavailable`, while the other searches record their actual generic localization, Tor, and flatness hits and explain why none is an exact match. No Lean source, compiler, Lake, build, live repository, or launcher file was modified.

## What remains

Nothing remains from the numbered return: all four Step 1 identifications, Step 2 locality, Step 3’s long-exact citation, the Tag 00M8 source wording, blueprint ancestry, search logging, and tool-use metadata were repaired in the sandbox.
