# Q05 stage-1 report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-one-dimensional-subrings-common-dvr-criterion.json: statement, split; the statement is unchanged and the proof follows Stacks 09N0.
- dag/nodes/sec-trace-formula/lem-trf-noetherian-valuation-ring-dvr.json: statement, Mathlib leaf; `IsDiscreteValuationRing.TFAE`, Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean:210, specialized from entry 1 to entry 0.
- citations.json: one verbatim statement quote for each of the ten step/node citations.
- searches.jsonl: actual msearch.py results, retained as emitted.
- report.md: this report and the author's source review.

## Attachments

None. Searches in lean/WeilConjectures for the item id and for common DVRs, fraction-field subrings, and Noetherian valuation rings found no declaration stating this item's equivalence. The existing `krullAkizukiNoetherian` in WeilConjectures/RingTheory/KrullAkizukiNoetherian.lean supplies only the already recorded intermediate-ring Noetherianity node; it does not assert the item. Project statements about dominating DVRs likewise impose other hypotheses and do not state this two-subring criterion. The new generic criterion is in Mathlib, rather than an attachment to a project theorem.

## Wanted literature

None. Read varieties.tex, Situation 09MY (situation-glue), Lemma 09N0 (lemma-glue-separated), and the first paragraph of the 09NJ affine-neighbourhood proof; also algebra.tex, Lemma 00IA (lemma-dominate), Lemma 00PG (lemma-krull-akizuki), and Lemma 00II (lemma-valuation-ring-Noetherian-discrete), with tags checked in tags/tags. Read the latest blueprint's ancestor lem-trf-local-term-locality statement/proof and the chapter and unit records. This is an algebra tool on the inherited finite-pinching/affine-neighbourhood dependency branch; no SGA source is used.

## Corrections and scope

There was no previous sandbox split or report to resume. The imported statement agrees with Stacks 09N0 and needs no correction. The original statement dependencies remain exactly the five notions it names. The imported empty proof is replaced by five steps. The argument explicitly proves that the image contains A and B, explains why a proper image cannot be a field, chooses a nonzero maximal ideal by citing the existing maximal-ideal-existence node, embeds its localization in K, and preserves a nonzero nonunit under domination. In particular one must exclude the field alternative in 00II; merely saying the dominating valuation ring is Noetherian would not suffice.

Krull–Akizuki is a declared generic tool use from the curve-estimates unit, specialized with L=K, extension degree 1. No finiteness or Noetherian assumption on B or on the image C is introduced. The ordinary localization's local-ring and maximal-ideal descriptions come from the existing definition node, whose statement includes those properties. Its embedding in K and the nonunit check are written out. The proof never invokes an unrecorded existence theorem or takes a construction from another node's proof.

## Not duplicates

lem-trf-noetherian-valuation-ring-dvr vs def-sc-discrete-valuation-ring: the existing node defines a DVR as a nonfield local PID; the new node proves that Noetherian valuation rings which are not fields satisfy that definition, without assuming principal ideals.

lem-trf-noetherian-valuation-ring-dvr vs lem-sc-principal-ideal-dvr: the existing node assumes a principal nonzero maximal ideal; the new node assumes the valuation-ring property and Noetherianity, and gives the criterion directly by Mathlib TFAE.

lem-trf-noetherian-valuation-ring-dvr vs lem-sc-krull-akizuki-noetherian: Krull–Akizuki gives only Noetherianity for arbitrary intermediate rings; the new node starts with Noetherianity and the valuation property and concludes the DVR property.

lem-trf-noetherian-valuation-ring-dvr vs lem-trf-one-dimensional-subrings-common-dvr-criterion: the item compares the image of a joint tensor map with existence of a common overring; the new node concerns a single valuation ring already given. Neither an overring nor the tensor-map equivalence appears in its statement.

Whole-DAG title, statement, source-tag and declaration searches, plus blueprint_refs.py searches for discrete valuation, Noetherian valuation, valuation ring is Noetherian, and 00II, found no existing node stating the new implication. In particular there is no existing source carrying Tag 00II. Nodes referring to TFAE for normal dimension-one rings or particular traits have additional, different input statements. The new leaf is not a clause of the item.

## Review by Q05

I compared the complete statement with Situation 09MY and 09N0: both subrings are unital with fraction field K; only A is assumed Noetherian of dimension exactly one; the tensor map multiplies elements, with base ring Z. Stacks' unqualified tensor here is precisely the tensor of rings over Z. The existence conclusion uses a proper DVR, not the field K. The two directions and all hypotheses are retained.

Step 1 uses the sentence of def-weil-pbc-module-tensor-product that the tensor is generated by pure tensors. The finite-sum description follows immediately from its quotient construction, and the displayed distributive calculation makes that image a subring. The fractions a/b from A prove the nonfield assertion; def-weil-field supplies exactly inversion of nonzero elements. These are elementary operations with the stated definitions, not a separate subring-generation lemma.

Step 2 uses lem-weil-pbc-proper-ideal-contained-in-maximal, whose statement applies to every commutative ring and every proper ideal. The ideal (c) is proved proper before applying it, and c is nonzero, so the resulting maximal ideal is nonzero. This step is not marked elementary, since maximal-ideal existence is its genuine theorem input.

Step 3 uses the full statement of def-weil-pbc-localization-at-prime: R_p is local, with maximal ideal pR_p. Maximal m is prime, and C is a domain since it is a unital subring of K. The fractions r/s identify this localization with a subring of K: equality in K is cross multiplication, and equality in the localization follows with multiplier 1; conversely any equality after a nonzero multiplier is cancellable in K. Its maximal ideal is given by numerators in m because m is prime. Then lemma-nagata-local-domain-valuation-dominates applies to this local subring of the very field K and asserts containment and contraction of the maximal ideal, exactly what the step takes from it. The nonzero element c/1 is in that maximal ideal and remains nonzero in K, so contraction proves that V is not a field. No assumption that C is Noetherian was used.

Step 4 uses lem-sc-krull-akizuki-noetherian exactly as stated: R=A is a Noetherian dimension-one domain with fraction field K; L=K is a finite extension of itself; and A is contained in the intermediate ring V contained in L. This supplies Noetherianity of V without any normality or finite-type hypothesis. The second citation is the new leaf; its hypotheses are valuation, Noetherian, and nonfield, all now in force. Read algebra.tex 00II and Mathlib TFAE.lean:210–225: entries 1 and 0 give precisely that implication. Mathlib's local-ring hypothesis is inferred by ValuationRing.isLocalRing (ValuationRing.lean:267), and the DVR class at Basic.lean:58–60 agrees with def-sc-discrete-valuation-ring. Finally the fraction field equality is the explicit elementary fraction argument using A contained in V. No unproved dimension claim for V is inserted.

Step 5 uses the finite-sum tensor description again and the nonfield clause of def-sc-discrete-valuation-ring; def-weil-field says K is a field. Closure of O under sums and products contains the image, and O cannot equal K. Thus the map fails surjectivity. These are elementary deductions, rather than a new converse node.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against these files and the sources. The new node is a self-contained statement-only Mathlib leaf, with its valuation/Noetherian/DVR notions cited, a verified tag and label, exact declaration/file/line and actual searches. Searches used leanfinder, loogle, leansearch and grep, including a second semantic phrasing; candidates were read in their source. All step citations quote the node statements verbatim in citations.json. There are no transported identifications without an argument, no hidden black-box invocation inside an elementary step, and no step longer than 2000 characters. New dependencies point only downward to existing definitions, and the inherited ancestor link is provenance, not a mathematical dependency.

Small cases checked: A=B=Z, K=Q gives a proper tensor image and a common DVR Z_(p); B=K makes the tensor map surjective via 1 tensor b and rules out any proper common DVR; A=B=k[t] has the common DVR k[t]_(t). For the new node, a field is deliberately excluded, and a nondiscrete non-Noetherian valuation domain is deliberately outside its hypotheses. These tests confirm why both Noetherianity and nonfieldness are present and do not suggest a statement dispute.

## Unfinished work

No mathematical split work remains. The one new node is a verified Mathlib leaf; no statement-only unsplit lemmas were created. Delivery validation follows this report.
