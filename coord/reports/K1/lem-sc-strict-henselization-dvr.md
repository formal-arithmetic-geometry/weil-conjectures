# Stage-1 split: lem-sc-strict-henselization-dvr

## Files written

- dag/nodes/sec-curve-estimates/lem-sc-strict-henselization-dvr.json: item, split in four steps.
- dag/nodes/sec-curve-estimates/lem-sc-strict-henselization-noetherian.json: statement only, unsplit, Stacks 06LJ.
- dag/nodes/sec-curve-estimates/lem-sc-strict-henselization-dimension.json: statement only, unsplit, Stacks 06LK.
- dag/nodes/sec-curve-estimates/lem-sc-strict-henselization-regular.json: statement only, unsplit, Stacks 06LN.
- dag/nodes/sec-curve-estimates/lem-sc-dvr-dimension-one.json: Mathlib leaf, `IsDiscreteValuationRing.ringKrullDim_eq_one`, Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean:244-249.
- citations.json: verbatim statement quotes for each citation in the four item steps.

## Attachments

None. A search of WeilConjectures/ for the item tag, strict henselization, and DVR declarations found no declaration stating the item.

## Sources and route

Read the online Stacks tag pages 04HX, 07QM, 0AP3, 06LJ, 06LK, 06LN, and 00PD. The local `literature/stacks-project/` tree is absent on this machine; the node source paths name its normal regenerated location. The chapter and unit records were read. This is an auxiliary for a boundary stalk calculation below the curve estimate chapter; it is not the unit's key statement, so the unit's `realized` fields are not edited.

The item's Step 1 implements 04HX's affine chart and triples calculation using the two existing proper-base-change nodes. Step 2 spells out 07QM's flatness argument with etale flatness and filtered-colimit flatness, then obtains faithful flatness and injection from existing Mathlib leaves. Steps 3 and 4 implement both implications of 0AP3 through 06LJ, 06LK, 06LN, and the dimension-one regular local DVR criterion. The three permanence facts are prerequisites of 0AP3, not clauses of the item. The DVR dimension fact is a Mathlib leaf.

## Not duplicates

- lem-sc-strict-henselization-noetherian vs lem-weil-pbc-henselization-noetherian-completion: the existing node concerns an ideal-adic completion of a henselization pair, not Noetherianity of a strict henselization of a local ring.
- lem-sc-strict-henselization-dimension vs lem-weil-pbc-regular-local-dim-one-iff-normal: the existing node characterizes normality in dimension one, not preservation of dimension by strict henselization.
- lem-sc-strict-henselization-regular vs lem-weil-pbc-regular-local-dim-one-iff-normal: the existing node characterizes regularity of one ring, not its preservation by strict henselization.
- lem-sc-dvr-dimension-one vs lem-sc-regular-dim1-dvr: the existing node gives regular local dimension one to DVR; this leaf supplies DVR to dimension one.
- lem-sc-dvr-dimension-one vs lem-sc-dvr-saturation-line-smith-normal-form: that node diagonalizes submodules over a DVR; it states no Krull dimension.
- lem-sc-dvr-dimension-one vs lem-weil-pbc-z-localizations-dvr: that node concerns localizations of Z at specific primes; it does not state the dimension of every DVR.
- lem-sc-dvr-dimension-one vs def-weil-pbc-cohen-ring: that node defines complete mixed-characteristic DVRs; it states no dimension theorem.
- lem-sc-dvr-dimension-one vs lem-weil-pbc-completion-of-dvr-is-dvr: that node proves completion preserves the DVR property; it states no dimension theorem.
- lem-sc-dvr-dimension-one vs lem-weil-pbc-serre-criterion-normal: that node is Serre's normality criterion for Noetherian rings; it states no dimension of DVRs.
- lem-sc-dvr-dimension-one vs lem-weil-pbc-dvr-unit-times-uniformizer-power: that node gives the unit-times-uniformizer normal form; it states no Krull dimension.
- lem-sc-dvr-dimension-one vs lem-weil-pbc-pid-noetherian-normal: that node gives Noetherianity and normality for PIDs; it states no one-dimensionality.
- lem-sc-dvr-dimension-one vs lem-weil-pbc-regular-local-dim-one-iff-normal: that node assumes dimension one and characterizes normality; this leaf concludes dimension one from a DVR.
- lem-sc-dvr-dimension-one vs lem-weil-pbc-principal-maximal-dim-one-regular: that node assumes dimension one and proves regularity; this leaf derives dimension one.
- lem-sc-dvr-dimension-one vs lem-weil-pbc-dvr-completion-regular: that node gives a regular completion map in characteristic zero; this leaf is a characteristic-free dimension theorem.
- lem-sc-dvr-dimension-one vs lem-exc-punctured-curve-branches: that node describes branches of a special curve singularity; this leaf concerns every DVR.
- lem-sc-dvr-dimension-one vs def-sc-discrete-valuation-ring: that node defines a DVR by local PID and nonfield conditions; it does not state the dimension-one consequence.

Searches of all `dag/nodes/` for 06LJ, 06LK, 06LN, 00PD and the relevant phrases found no statement covering the three permanence results or the DVR dimension statement. `tools/blueprint_refs.py search` found no blueprint duplicate for any of the four. No new node copies a clause of the scheme-level item. All four nodes are self-contained statements with no proof or proof dependencies. The source labels and hypotheses were checked against the tag pages.

## Review by K1

I compared the scheme statement to Stacks 04HX: a geometric point over y gives an affine chart A with O_{Y,y}=A_p, and the etale-neighbourhood colimit is the ring strict henselization for the separable closure inside Omega. The Noetherian assumption is exactly what 0AP3 and 06LN require; 07QM and 06LK apply even without it. I read the statements of every cited node and made citations.json quote those statements verbatim.

Step 1 uses the etale-local-ring-triples statement for the cofinal affine chart and equivalence with triples, the strict-henselization-limit definition for the item's actual colimit, and strict-henselization-triples for its identification with (A_p)^sh and its local maximal ideal. Step 2 uses the triples statement's filtered etale colimit, etale-algebra-flat for every stage, and filtered-colimit-flat-modules for the underlying module. Its local-map claim uses the triples statement's maximal-ideal formula, and the two faithful-flat leaves provide faithful flatness and the I=0 injection. Each of these is a stated clause, not a construction hidden in a proof.

Step 3 uses the DVR dimension leaf and the 06LJ and 06LK statements to give Noetherianity and dimension one of R^sh. The definition of DVR gives a principal nonzero maximal ideal; the regular-local definition then makes R regular local in dimension one. The 06LN statement transfers regularity, and the existing regular-dim1-dvr node gives the conclusion. Step 4 reverses this: the DVR dimension leaf and 06LK give dimension one of R; the DVR and regular-local definitions make R^sh regular; 06LN reflects regularity and the regular-dim1-dvr node concludes. The assumed Noetherianity of R is in force for 06LN in both directions.

I checked the field edge case: both R and its strict henselization have dimension zero and are not DVRs under the project's definition, so the equivalence does not mistakenly count a field. For a one-dimensional DVR, the principal maximal ideal and dimension-one facts give exactly the regular-local criterion used. The new 06LJ and 06LN statements retain their Noetherian hypotheses, while 06LK does not introduce one. Mathlib searches were run under the item's search log for every new id, with second LeanFinder phrasings; LeanSearch returned HTTP 500 and is recorded as unavailable. The item was already searched in the repository and was searched again here. I corrected the initial temptation to use 0AP3 itself as a new node: the item steps now contain its argument and cite its distinct prerequisites.

## Second reading by K1

- Step 1 checked against Stacks 04HX and the statements of the affine triples, strict-henselization limit, and strict-henselization triples nodes; the affine chart, colimit identification, and local map are stated by the cited nodes. Verdict: valid.
- Step 2 checked against Stacks 07QM and every cited flatness, filtered-colimit, local-faithful-flatness, and ideal-contraction statement; the filtered diagram and locality hypotheses are present. Verdict: valid.
- Step 3 checked against Stacks 0AP3, 06LJ, 06LK, 06LN, 00PD and the cited definitions/criterion; Noetherianity, dimension one, regularity, and the DVR conclusion follow in the stated order. Verdict: valid.
- Step 4 checked against the reverse implication in Stacks 0AP3 and the same dimension, regularity, and DVR statements; the Noetherian hypothesis on the original local ring is in force. Verdict: valid.
- Node `lem-sc-strict-henselization-noetherian` checked against 06LJ (conditions (1) and (3)); self-contained statement-only node with its definition dependency and recorded searches. Verdict: valid.
- Node `lem-sc-strict-henselization-dimension` checked against 06LK; self-contained statement-only node with the Krull-dimension definition dependency and recorded searches. Verdict: valid.
- Node `lem-sc-strict-henselization-regular` checked against 06LN; self-contained statement-only node retains the Noetherian and regular-local hypotheses and recorded searches. Verdict: valid.
- Node `lem-sc-dvr-dimension-one` checked against 00PD and Mathlib `IsDiscreteValuationRing.ringKrullDim_eq_one` at `TFAE.lean:244`; the project DVR definition records the equivalent Mathlib typeclass assumptions. Verdict: valid Mathlib leaf.
- Small cases checked: a field has dimension zero and is excluded by the DVR nonfield clause; a one-dimensional DVR has a nonzero principal maximal ideal, yielding the regular-local criterion used in both directions; the geometric-point construction is vacuous for an empty scheme.
- Changes: none to the split files; this second-reading section records the source, dependency, duplicate, edge-case, and Mathlib-leaf checks. The dry run passed preflight, citation, search, and duplicate checks.
