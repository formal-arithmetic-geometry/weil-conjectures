# Stage-1 report: lem-trf-functorial-log-blowup-etale-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-functorial-log-blowup-etale-descent.json`: statement node, now split into ten steps. No Mathlib match for the logarithmic assertion.
- `citations.json`: verbatim statement excerpts for every dependency cited by every proof step.
- `searches.jsonl`: actual NK Mathlib searches; retained in the sandbox.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script, not a DAG delivery file.

There are **0 new nodes and 0 new Mathlib leaves**. The split reuses the existing chart-cover, saturated log-ideal construction, sheaf-descent and geometric permanence nodes. All non-elementary proof steps have fewer than 2,000 characters.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint tag and logarithmic blowup/descent terminology. The matches were ordinary scheme blowup files and incidental occurrences of “topological” or “tautologically”; none states the logarithmic assertion. The item has no recorded Lean audit/declaration to attach. No Lean was written or compiled, and no upstream master sorry declaration was treated as a proof.

## WANTED

None. I read ILO, Expose VIII, printed pp.108--110 (PDF pp.114--116), especially 3.3.8--3.3.13 and the proof of 3.3.15. I also read Stacks `sites.tex`, `lemma-glue-maps` (04TQ) and `lemma-glue-sheaves` (04TR), `properties.tex`, `lemma-locally-Noetherian-quasi-separated` (01OY), `morphisms.tex`, `lemma-finite-type-noetherian` (01T6) and `lemma-base-change-etale` (02GO), and `topologies.tex`, `definition-etale-covering` and `lemma-etale`. No SGA source is used.

## Problems found and changes

The imported statement was retained exactly. Its hypotheses are sufficient; the empty case and proper principal ideals need explicit care. The source's phrase “By descent” is not an effective proof of the tower-with-centers assertion by itself. I supplied the descent argument rather than creating another node that restates that assertion.

The main possible gap is synchronization: equality of separately contracted restrictions need not identify their original indices. The proof first forms one finite disjoint-union chart cover U of X. The two projections U x_X U -> U are surjective, so a proper center on any stage cannot become the whole log monoid sheaf on either full pullback. Their assigned comparisons therefore compare the full ordered towers. This supplies genuine stagewise descent data for the ideals. Once an ideal has descended, the existing global log-blowup construction supplies the next scheme, without appealing to ineffective descent for arbitrary schemes.

The historical blueprint ancestry is retained. The item was created beneath the monoidal-resolution branch of `lem-trf-local-term-locality`; the current main-20261015 text for that ancestor instead gives the contracting-correspondence argument. I read the current text and the chapter/unit records. This delivery expands the existing auxiliary log-descent lemma and does not modify a unit, chapter, target, or maintainer-owned ancestry field.

Mathlib searches used the required search command: LeanFinder for strict-etale logarithmic tower descent, LeanSearch for monoidal-ideal blowup sequences, Loogle for LogStructure and Blowup, and two source grep queries. The semantic hits concern ordinary etale morphisms, scheme morphism-property descent and ordinary ring-ideal functoriality, not construction of towers with log-ideal centers. Loogle returned no hits. The only logarithmic grep hit was logarithmic height in the elliptic-curve addition file; I read those lines and excluded it. The second grep for KatoFan/MonoidalSpace/FineSaturated/log blowups returned no hits. Exact queries and results are appended to the item's existing search record and logged in `searches.jsonl`.

## Unfinished work

None in the one-level split. The existing unsplit sheaf-localization node remains an existing dependency, not a newly created obligation. Stage 2 and Lean proofs are outside this task.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches for log blowups and coherent log ideals found no blueprint node stating this item. The existing `lem-trf-coherent-log-ideal-chart-construction` constructs one blowup once its global ideal is given; it does not descend a contracted functorial tower. The existing `lem-pe-set-sheaf-cover-descent` supplies the needed generic sheaf gluing. Reusing both removes any need for a new log-ideal-descent node.

## Review by NK

I checked this split against delivery-errors B--E with the cited node statements open. All proof references take statements, not arguments hidden in a cited proof. Every substantial external input is an existing cited node. No new statement is hidden behind a renamed clause of the item. There is no changed statement or STATEMENT-DISPUTED claim.

Step 1 uses the universal property explicitly stated in `def-trf-fs-log-blowup`, together with the identity-comparison assumption in the item. A tower with n ordered centers cannot be isomorphic as an ordered tower with centers to a shorter one. Whole ideals give universal identity blowups. I checked the empty scheme and also a proper principal ideal: the latter gives an identity blowup but must not be deleted under the stated contraction convention.

Step 2 uses `lem-trf-log-fan-chart-blowup` (i), which explicitly gives a finite quasi-compact strict-etale chart cover under precisely the item's fs, locally-Noetherian, quasi-compact and characteristic-torsion-free hypotheses. The coproduct-family node gives disjoint open components, and the finite-coproduct node gives quasi-compactness. The fine-fan definition is local, so the finite disjoint union of the chart fans is a fan; the characteristic isomorphisms assemble componentwise. The etale definition includes the affine-local characterization, which proves etaleness of the disjoint-union map without an extra theorem. The finite-union assumption on the rule applies here.

Step 3 uses `lem-weil-pbc-locally-noetherian-quasi-separated` for X, the three exact clauses of `lem-weil-pbc-qcqs-morphism-permanence` for quasi-compact maps and fiber products, `lem-weil-pbc-etale-covering-base-change` for the overlap covers, and `pqf-lem-locnoeth-lft` for local Noetherianity. The etale definition supplies local finite presentation and hence local finite type. Strictness pulls the characteristic sheaf back, so composing the chart with a strict-etale projection is a chart; this is also the strict-base-change setting of the fan-chart node. The full overlaps, not arbitrary possibly non-quasi-compact neighborhoods, are inputs for the rule. I checked the same hypotheses for common refinements and Y x_X U.

Step 4 takes strict-etale restriction compatibility from the explicit final clause of `lem-trf-coherent-log-ideal-chart-construction`. It yields actual scheme base changes of the blowups. `lem-weil-pbc-etale-covering-base-change` then supplies the surjective covers at every level. The equalizer sheaf condition in `def-weil-pbc-etale-sheaf-of-sets` proves that an ideal is whole if it is whole after a cover: local ideal representatives of a given section agree because the ideal is a subsheaf. I do not assume that a log blowup itself is surjective, which would be a different and unnecessary assertion.

Step 5 uses exactly the comparison hypotheses of the item and Step 4. Both overlap projections are surjective; there are therefore no omitted indices in either comparison. Center preservation gives equality of subideals on the identified stages. Composition on triple overlaps and identities on diagonals are precisely the assumed composition and identity laws. This step is elementary once the cover check is available, and cites no external lemma silently.

Step 6 uses `lem-pe-set-sheaf-cover-descent` for both objects and maps: unlike a representable full-faithfulness statement, this node explicitly states effective gluing of sheaves and gluing of homomorphisms as maps of sets. I checked its small-site/universe hypothesis and added `def-weil-size-convention` explicitly. `lem-weil-pbc-etale-site-localization-open` states the equivalence between the slice small-etale site and the covering scheme's small-etale site, which is the restriction used here. The descended map to M_i is injective by the sheaf condition, not by an unquoted descent-of-monomorphisms theorem. The sectionwise formula proves uniqueness. Ideal stability is local, and coherence/nonemptiness are the etale-local finite-nonempty-generator conditions actually stated in the log-ideal definition. This is the only gluing argument needed for centers, so no separate elementary node was created.

Step 7 applies the existing construction to a global ideal only after the inductive step has produced it. Its hypotheses fs, locally Noetherian and nonempty coherent ideal are all present. Its fs output is a log scheme in the locally-Noetherian convention of the definition. The node explicitly gives saturated universal blowups and strict-etale restriction compatibility, so it gives U_(i+1) = U x_X X_(i+1) and the corresponding overlap equality. Cover-base-change proves the next stage is still covered. This is a finite induction, with X_0=X as the base and one construction per index; there is no unproved termination assertion.

Step 8 checks independence by the common cover U x_X V. Its projections are surjective, so both towers retain every index and have the same length. Equality of the first center is detected on that cover using the explicit formula of Step 6; the universal property in the log-blowup definition then gives the unique first-stage comparison. Repeating gives all stages, and uniqueness gives the cocycle. Chart independence is an assumption of the item, not a theorem taken from an unrelated chart node.

Step 9 checks a potentially nonsurjective strict-etale Y -> X. The surjective cover is W -> Y, not W -> U. Thus stages may disappear on Y, but Step 4 detects exactly the same whole-ideal indices on W. A deleted stage is the identity by Step 1, so deleting consecutive stages does not shift the surviving centers incorrectly. The assumed comparison on W -> U identifies the contracted tower with T(W), and the center formula and universal property identify its descent with the extension on Y. The cited log construction and cover-base-change statements give precisely the restriction and cover facts used. Compatibility with identities and composites follows from the assumed comparisons after a cover and the established uniqueness.

Step 10 checks agreement with the old rule using the identity cover for a charted X, then arbitrary chart neighborhoods using Step 9. For uniqueness, first contract any extension. Its pullback to the surjective finite chart cover has no additional deletions, so its length and all its centers are forced successively by T(U). The subsheaf formula forces each ideal, and the universal property forces each transition. This proves uniqueness with centers and the stated functorial comparisons, not merely uniqueness of the final scheme.

The only off-unit non-Mathlib tool inputs are the finite-coproduct quasi-compactness lemma, general set-sheaf descent, and the small-etale localization equivalence. They are declared in `split_report.tool_uses`; each is a generic input for the auxiliary descent argument, not a replacement for a unit step. Other geometry inputs are already Mathlib leaves. I reviewed every non-elementary step for a hidden independent lemma; their content is application of these cited statements to the specified covers/ideals. No non-elementary step exceeds 2,000 characters.

## Validation

The server `review_split` check passed on the initial draft. The final required dry run and push are recorded below after completion.

Required dry run completed successfully: `deliver.py NK lem-trf-functorial-log-blowup-etale-descent --no-push` printed `OK (not pushed)` at `1e0716d292`, with server preflight passed. This includes the DAG and split checks. The next invocation is the authorized direct push; it repeats the delivery checks.
