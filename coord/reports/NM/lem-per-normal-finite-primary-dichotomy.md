# Stage-1 report: lem-per-normal-finite-primary-dichotomy

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-normal-finite-primary-dichotomy.json: statement, split; whole-statement Mathlib searches found no match. Six proof steps, no new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quotation for every step/node citation.
- report.md: this report. searches.jsonl retains the actual search-command log; prepare.py is sandbox-local preparation material.

## Attachments

None. Searched WeilConjectures for the exact blueprint id, primary ideals, symbolic powers, height-one normal localizations and finite normal algebra terminology. The project declarations about primary torsion representations and the isolated primary-square assertion in Kaehler/TraceDuality do not state this item. No sorry declaration is counted as a proof.

## WANTED

None. The ILO source and all Stacks sources used here are present locally.

## Corrections and route

The statement is correct and unchanged, including nonzero/proper/primary, injectivity and normality. The source's dimension-based wording in ILO V 2.2.3 and V 3.2.3 is realized by explicit contractions. I read printed pp.65 and 67 (PDF pages 71 and 73). The mixed-characteristic source cites Serre for the symbolic-power assertion; the present proof supplies that argument using existing DVR nodes. No SGA source is used.

Read the chapter and unit records and the latest blueprint ancestor proof lem-per-artin-gabber-affine-curve. This inherited algebraization subproblem belongs to its finiteness input through the recorded chain. The proof stays on the ILO algebraization route. The item is not the unit's key node; no unit file is changed.

The one generic tool use outside the unit is lem-trf-normal-domain-principal-divisor-kernel. Its statement explicitly supplies the height-one DVR localization needed for ILO V 3.2.3(i). We use none of its divisor/length/kernel conclusions. It is declared in split_report.tool_uses. The other substantive algebra inputs are existing Mathlib leaves. No new mathematical lemma is manufactured by copying a clause of the item.

## Unfinished work

None at stage 1. Existing cited nodes retain their own statuses; this delivery does not claim to finish their formal proofs.

## Not duplicates

No new nodes. Whole-DAG title/statement searches and blueprint_refs.py searches for primary, primary ideal and principal ideal theorem found the reusable nodes cited here. In particular the existing primary fibre-recovery lemma has a more specialized flat Noetherian interface, and the existing symbolic graded-embedding lemma asserts a different consequence; neither was duplicated or cited for something it does not state.

## Review by NM

I read ILO V 2.2.3 and V 3.2.3 in the local PDF, not an older blueprint snapshot, and read Stacks algebra.tex at tags 00GK (lemma-finite-is-integral), 00GT (lemma-integral-no-inclusion), 0306 (lemma-Noetherian-power-series), 00KV (lemma-minimal-over-1), 031S (lemma-criterion-normal), and 00PD (lemma-characterize-dvr). I also read the Noetherian-localization proof at 00FN. There are no new nodes needing independent sources. Every cited DAG statement was opened and read; citations.json quotes its actual statement.

Step 1 uses the finite-algebra node to obtain integrality and the strict-contraction form of lem-weil-pbc-integral-incomparability to show Q meets R nontrivially. I checked Mathlib/RingTheory/Ideal/GoingUp.lean at its IsIntegral.comap_lt_comap declaration: the lower ideal is prime, while the upper ideal need not be. This matters because Q is primary, not necessarily prime. Thus there is no unsupported nonzero-contraction theorem hidden in the proof.

Step 2 uses the precise DVR definition (principal ideals and a nonzero maximal ideal), the coefficient-family definition of multivariate series, the series-domain node over the residue field, the series-Noetherian node over the DVR, and the principal-ideal height bound. Coefficientwise division by pi proves the reduction kernel equals pi R directly. Surjectivity of reduction is not needed: primality follows from the target being a domain. A principal-ideal ring is Noetherian directly because all its ideals have one generator. The height bound applies to pi R itself, which is prime, hence minimal over that principal ideal. The nonzero constant coefficient supplies the lower bound on height.

Step 3 is elementary and contains the actual radical calculation, including the binomial argument for additive closure, the proof that the radical of a proper primary ideal is prime, and the contraction comparison. There is no invocation of an uncited primary localization theorem. The nonzero contraction from Step 1 rules out the zero prime below pi R. If the contraction instead contains an element outside pi R, the same reduction-kernel computation proves the first alternative immediately.

Step 4 uses exactly integral incomparability and the principal-ideal height bound. Every prime between pi A and P contracts to pi R, so there is no such strictly smaller prime. This establishes minimality over pi A before invoking the height bound. Normality is not used prematurely, and the image of pi is nonzero by injectivity. Going down, lying over, regularity of the entire series ring, and a dimension equality are unnecessary.

Step 5 takes the DVR conclusion from the explicit first assertion of lem-trf-normal-domain-principal-divisor-kernel, under precisely Noetherian normal domain and height-one hypotheses. It takes Noetherianity from the localization-Noetherian node and the fraction/equality/maximal-ideal description from the prime-localization definition. I wrote out a finite-sum common-denominator argument and then used primaryness to prove Q = A intersect Q A_P. Thus citing a definition does not stand in for a missing saturation theorem. The argument also verifies extension is proper and nonzero. In particular P and Q are not silently identified, and localization is A_P, not a localization at a contracted prime of R.

Step 6 uses principal generation from the DVR definition and unit-times-uniformizer factorization from the existing lemma, after Noetherianity and the nonzero uniformizer have been established. The generator is nonzero since the localized ideal is nonzero, and its exponent is positive since that ideal is proper. The equality (P A_P)^n = P^n A_P is the elementary expansion of products of finite sums; inverse image is exactly the symbolic power defined in the item. This supplies the argument of the item's second clause rather than moving that clause into a new node.

I checked delivery-errors B1-B10: no new-node schema, source, search or Mathlib-leaf issues arise; the item preserves all inherited fields, uses single TeX backslashes, and keeps all fresh searches identical to the actual logged queries. Existing source searches were preserved, not invented or relabelled. I read the hits of all five fresh searches, including the second semantic phrasing: their DVR ideal and Dedekind statements are separate ingredients, not the whole dichotomy. I checked C1-C8 with each cited statement open, including off-unit tool declaration and no reliance on another node's proof. D1-D5 are addressed by the six actual arguments and zero new nodes. E1-E7 are addressed by the explicit hypothesis checks above. No step is over 2000 characters, and none hides a separately named standard comparison.

Small cases checked: A = R over a field, Q = (t_1), gives the scalar alternative; over a DVR Q = (pi^n) gives its vertical symbolic power; Q = (t_1) has nonzero reduction and gives the scalar alternative; in Lambda[[t]] the primary ideal (pi,t)^2 gives the scalar alternative because t^2 lies in it. When A is ramified, pi need not generate the maximal ideal of A_P: the proof deliberately chooses a new local uniformizer varpi. The excluded zero ideal would invalidate the field conclusion, while the excluded unit ideal would invalidate positive n; both exclusions are used explicitly. The reasoning also works for r = 0, although the statement retains r >= 1. No statement dispute was found.
