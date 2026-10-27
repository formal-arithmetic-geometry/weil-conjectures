# Q88 stage-1 report: lem-trf-normal-boundary-fraction-clearing

## Files written

- dag/nodes/sec-trace-formula/lem-trf-normal-boundary-fraction-clearing.json: item statement, now split; statement and stmt_deps unchanged; no exact Mathlib match.
- citations.json: verbatim statement excerpts for all four step/node pairs.
- searches.jsonl: five searches actually run by msearch.py for this item, with their returned hits read.
- report.md: this report.

No new nodes; no Mathlib leaves created. The sandbox contained no earlier split or report. The inherited item's five 2026-10-22 search records were retained, and five searches from this session were appended.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, fraction-clearing names, normal-boundary names, and boundary/fraction/height-one/intersection terminology; no project declaration gives this full statement. The existing related DAG statements are dependencies, not attachments of the item.

## WANTED

None for this delivery: all mathematical input used here is in the local Stacks algebra.tex. The existing Mori–Nagata node mentions an unavailable local Swanson–Huneke PDF; that theorem is not used by this delivery.

## Corrections and source comparison

The imported statement is correct, including its empty-boundary case; no STATEMENT-DISPUTED. The formerly empty proof is replaced by four steps. Source: local Stacks algebra.tex, Tag 00PD (lemma-characterize-dvr), Tag 031T (lemma-normal-domain-intersection-localizations-height-1), and Tag 0311 (lemma-zero-at-ass-zero), with tag mappings checked in tags/tags. The exponents and simultaneous application are the agent's explicit elementary argument, so proof_origin.by is agent. The denominator argument is exactly the proof of 031T (2), relying on (1) and 0311; it does not silently assume a missing intersection theorem.

Read the chapter sec-trace-formula and unit sk-i-curve-zero records and the latest blueprint locality statement and proof under literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/. This item supplies original boundary-class-injectivity steps 7--8 along its recorded local-term/nearby-duality/log-regular ancestry. It does not replace the chapter or unit route and does not use any SGA source. Its existing blueprint.from.place is specific and retained, and same_as remains []. Whole-blueprint searches for height-one and normal domain gave no statement equal to the item. No unit realization update is appropriate for this auxiliary.

## Mathlib searches and candidates

Actually ran leanfinder twice with different conceptual phrasings, leansearch, loogle, and grep via msearch.py. Read every returned result. The plausible hits are IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one, IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot, IsIntegrallyClosed.of_localization, and IsLocalization.Away.sec_spec. Read the local source: DedekindDomain/Ideal/Lemmas.lean:564 and its surrounding dimension-one context, DedekindDomain/AdicValuation.lean:419 and its Dedekind hypotheses, and LocalProperties/IntegrallyClosed.lean:58. Dedekind results require dimension at most one, which the item does not assume. The local-properties theorem assumes the needed intersection equality rather than deriving it. Away.sec_spec requires membership in the localization away from tau, which is precisely what must be established here. Other returned S-integer, valuation-ring, rational-number, and finite-extension statements do not have this result's hypotheses or conclusion. Hence no Mathlib match.

## Not duplicates

No new nodes were created. The nearby existing lem-trf-normal-domain-principal-divisor-kernel supplies local DVR membership, but its global conclusion covers only zero divisor (units), not fractions with negative boundary orders. The existing lem-trf-normalization-integral-closure-krull supplies a stronger normal-intersection tool via normalization; this split instead uses the already-existing principal-quotient associated-height and module-detection nodes to follow Stacks 031T directly. The S2 total-fraction membership node is another possible general tool, but would require citing a Serre-criterion interface as well. None needs to be duplicated.

## Review by Q88

I read the local statements and proofs of 00PD and 031T, and the statement and proof of 0311. For the four existing cited nodes I opened their JSON files and read their full statements, rather than relying on titles or tags. No new-node source review is needed because this delivery creates none.

Step 1 uses no non-elementary theorem: finite maxima with an inserted zero exist even for empty I, and each positive integral boundary order is at least one. The displayed inequalities prove that the explicitly chosen N_0,H_0 work, with no need for an Archimedean or approximation lemma.

Step 2 uses the statement of lem-trf-normal-domain-principal-divisor-kernel for the DVR assertion and nonnegative-valuation membership criterion. Its ring hypotheses exactly match this item's Noetherian normal domain. Multiplication, inversion, and nonnegative powers are defining identities of the given additive valuations, with the latter two obtained by cancellation and induction. This step checks listed and unlisted height-one primes separately and applies the membership criterion only to the nonzero elements h and h', since f and tau are nonzero.

Step 3 cites lem-weil-pbc-normal-domain-principal-quotient-associated-height only for its actual assertion about associated primes of R/bR, with b nonzero. It cites def-weil-pbc-localization-at-prime for the actual c/s representatives with s outside the prime; no theorem about exactness of localization is smuggled in. Equality in the fraction field and injectivity of R into that field give sa=bc directly. The explicit equivalence in lem-weil-pbc-module-injects-localizations-associated-primes then applies to the class of a: for each associated prime the displayed s annihilates it, so it is zero. This proves a is in bR and g is in R for each of the two fractions. These are generic tools from another unit, declared in split_report.tool_uses with their purposes. The separate inputs 031T (1) and 0311 are strictly smaller facts and the proof carries the fraction-membership argument itself. No new node merely restates a clause of this item.

Step 4 uses only commutative field cancellation and injectivity of R into its fraction field, after all three ring elements have been obtained. It proves the identity for every admissible N,H, not just the maxima. There are no steps over 2000 characters and no hidden comparison or standard lemma.

I checked the B--E error lists against this split: all notions remain defined inline or by statement dependencies; every non-elementary input is an existing cited statement; all citation excerpts are literal substrings; no source tag substitutes for a dependency; no new unsplit node or illicit proof sketch is introduced; all exponents are nonnegative integers; every localization argument uses a nonzero denominator; the ring is normal and Noetherian wherever required. The proof dependency union equals the step uses. I checked that the chosen dependencies do not reach the item, avoiding a cycle.

Small cases: for R a field and I empty the proof gives f,f^{-1} in R and N=H=0. For arbitrary normal R and I empty, the associated-prime argument forces both fractions to be in R, so f is a unit. For R=k[x], tau=x, f=x^{-3}, the formulas give N_0=3,H_0=0 and h=1,h'=x^3. For tau=x^2,f=x, they give N_0=0,H_0=1, which is admissible even though it need not minimize the exponents. The denominator b a unit case has zero quotient and empty associated-prime set, explicitly covered by the cited module theorem. These checks find no missing hypothesis.

## Unfinished work

None within the stage-1 split; the existing dependencies keep their independent proof status. No Lean was written or compiled, and no shared-repository file or launcher script was modified.
