# Worker report: lem-trf-log-chart-strict-local-tor

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-log-chart-strict-local-tor.json`: item, statement, split into six steps; no Mathlib match. Statement and statement dependencies unchanged.
- `citations.json`: one verified verbatim statement excerpt for each of the eleven step/node citations.
- `report.md`: this report. No new nodes and no Mathlib leaves.

## Attachments

None. Searched the read-only `lean/WeilConjectures/` by the exact blueprint id and by logRegular/log_regular/log regular and monomial Tor terminology. No project declaration states the item. The given node has no Lean attachment record; its old sorry-free proof was not assumed to exist.

## WANTED

None for this assembly. The existing Kato node's source points to Kato 1994, 6.1(ii), which I did not independently obtain; the available ILO Expose VIII p.110 explicitly quotes its Tor vanishing. This delivery uses that existing statement as an unsplit dependency, rather than claiming to have proved Kato's theorem.

## What was wrong or missing

The imported item had an empty proof. Its statement is consistent with the available source and required no correction. The comparison with a sharp chart is not an equality of ring actions: the unit-character twist in the existing Tor comparison is essential. The arbitrary chart may have a torsion unit group, so splitting its entire group completion as a free group would be unjustified. Step 3 only requires freeness of the sharp quotient group, exactly as its cited splitting lemma says.

The current blueprint is `literature/blueprint/latest`, snapshot 7284bb09daf97437d544c51882b325f9c52cd345. Read its locality statement/proof and the trace chapter/unit records. The ancestry field retains the existing nearby-duality/log-resolution chain below the locality node; this delivery changes no unit or chapter route. There is no new blueprint equivalent: whole-blueprint searches for monomial and log regular found no node stating this arbitrary-chart strict-local conclusion. All algebraic ingredients were found already in the DAG.

## What remains unfinished

Nothing in this item's stage-1 assembly. Existing dependencies, including the sharp-chart Kato Tor theorem, retain their current separate proof obligations. No Lean was written or compiled.

## Mathlib searches

Read the results of all six current searches recorded in searches.jsonl: LeanFinder for the item and for the arbitrary-to-sharp reduction, Loogle for MonoidAlgebra and Tor, LeanSearch for the local log-regular monomial quotient, and two grep phrasings. The semantic hits concern formal smoothness/cotangent modules or localization of linear independence. The Loogle hits concern monoid-algebra ring maps and torsion-free modules. The broad grep had substring hits in polynomial files; the word-boundary refinement had no hits. None states log-regular monomial Tor independence or specializes to it in one line. The item's older search records are retained verbatim; the current query/result records are appended. No unavailable service is represented as no match.

## Not duplicates

No new nodes were created. Existing `lem-trf-kato-tor-independence-chart` is restricted to a chart identifying the characteristic monoid; the item permits any fs chart. Existing `lem-trf-log-chart-face-tor-comparison` compares two Tor groups without asserting their vanishing. Both are used, not duplicated. The existing monoidal-ideal tensor theorem above the item is not cited, which avoids a dependency cycle.

## Review by Q78

I read ILO Expose VI 1.1--1.2 and 1.6, printed pp.69--70, for the strict-local definition and sharp chart; VI 3.7(a), printed p.75, for the free sharp-group splitting and unit comparison; VIII proof of Lemma 3.4.3, printed p.110, for the explicit Kato monomial Tor input. I also read Stacks Tag 04HX (`etale-cohomology.tex`, `lemma-describe-etale-local-ring`) for the geometric structure-sheaf stalk identification. No SGA route is used. There are no new nodes whose source requires a separate check.

Step 1 cites the geometric-stalk definition and affine-neighbourhood cofinality, both opened and read, to identify the exact coordinate-ring colimit in the strict-henselization definition. The strict-henselization local-structure statement supplies strictly henselian local, not an unasserted residue-field identification. The fs log definition states the pushout chart isomorphism at that same stalk, so the ring map is the original chart composite. These two off-unit statements are declared generic tools in split_report.tool_uses; they only supply the necessary site/local-ring infrastructure.

Step 2 uses chart-face-localization-logification for the face and the specified identification with the characteristic, and fs-face-sharpening for integral fs localization, its unit group, and the finite free sharp group. I read each entire statement, not its proof. All hypotheses hold for the original fs chart, with no sharpness assumption on P.

Step 3 uses integral-monoid-free-sharpening-splitting. It assumes only integrality of the localized monoid and finite freeness of its sharp group's completion, both furnished by Step 2. It supplies an actual monoid section. In particular no claim that the unit group is torsion-free is needed.

Step 4 applies log-regular-sharp-chart to the original locally Noetherian log regular X, so no unproved preservation of log regularity under strict localization is used. Its statement supplies a pointed etale chart with the chosen characteristic identification, not merely an abstract monoid isomorphism. Relabelling by Step 2 identifies its germ b with a map into the same B.

Step 5 uses log-chart-face-tor-comparison, whose entire statement I checked. B is strictly henselian local, the original chart has the pushout description of Step 1, s is the monoid section of Step 3, and b is the sharp characteristic chart of Step 4. I wrote out surjectivity P to Q and ideality of H_x. The comparison's right ring action is b; its unit twist is included rather than suppressed. This is exactly the Tor isomorphism quoted in citations.json.

Step 6 applies kato-tor-independence-chart to the original X and the sharp chart on its pointed etale neighbourhood. Its strict local ring is B, and H_x is an arbitrary monoid ideal. Its statement explicitly permits the empty ideal. I wrote out why the generated monomial ideal equals the direct-sum ideal, then use the isomorphism of Step 5 to obtain zero.

Small cases checked: H empty gives the zero ideal, H=P gives a zero quotient, and H meeting the inverted face gives H_x=Q and hence a zero right quotient. P a group gives Q=0; nonempty monomial ideals are total and the same conclusion holds, including torsion groups. For P sharp and already characteristic the construction reduces to Kato with a possible unit twist. For the standard chart N on a regular trait the parameter remains a nonzerodivisor, agreeing with Tor one vanishing. In mixed characteristic no flatness over Z is assumed: only monomial quotients enter.

Against delivery-errors B--E: no new node, hollow definition, unsupported Mathlib leaf, or clause restatement is introduced. The split has genuine reductions and an assembly, not a renamed copy of its conclusion. Every cited node exists and its statement gives the fact used. Definitions are used only for their definitions. All hypotheses and coefficient actions were checked as above. The proof-dependency list is exactly the union of uses; the statement is unchanged. Every non-elementary step is under 2000 characters; the hidden comparison and splitting arguments already have separate existing nodes. All eleven citation excerpts were checked as literal substrings of the live statements.

The first dry run required fuller citation excerpts for the stalk definition and Kato vanishing. I replaced those short formulas with the complete cited statements, then repeated the dry run.
