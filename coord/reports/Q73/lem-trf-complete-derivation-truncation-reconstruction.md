# Q73 stage-1 report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-complete-derivation-truncation-reconstruction.json: unchanged statement, six explicit proof steps, status split; no Mathlib match.
- citations.json: one verbatim statement quote for each of the five step-use pairs.
- report.md: source audit, mathematical checks and signed review. baseline.json preserves the item read before editing; searches.jsonl is the unmodified search-command log.

## New nodes

None. The proof needs the universal property and the free-symbol presentation already explicitly stated in def-weil-pbc-kahler-differentials, and the tuple definition in def-trf-continuous-kahler-differentials. The remaining operations are direct quotient, generator and coordinate calculations written in the steps. In particular neither a clause of the item nor an elementary compatibility check has been made into a new node.

## Attachments

None. I searched live lean/WeilConjectures by the exact blueprint tag, complete-derivation, truncation-reconstruction, shifted differentials, and derivation/completion terminology. The pointwise truncation-limit theorems concern complexes, not this ring/module statement. I read RingTheory/Derivation/CompletionAndLocalization.lean: its private lowers_powers and quotientDerivative concern ring-valued absolute derivations, and the public completion construction does not state this reconstruction or the inverse identities. It is not an exact attachment.

## WANTED

None. Stacks algebra.tex supplies the two stated algebra inputs. The full reconstruction is explicitly agent-written, as was the original auxiliary statement, and is not attributed as a verbatim Stacks theorem.

## Audit findings

The sandbox initially held only dispatcher markers, with no item, split, report or prior search log to resume. I retained the copied item's complete original search records, source, blueprint ancestry, chapter, unit, creation record and statement; I appended only searches actually executed in this session.

The item statement is correct as written. No change in hypotheses, conclusion or definitions is needed. Completeness is the assumed isomorphism of the canonical map, not completeness deduced from finite generation; no Noetherianity, finite generation of the ideal, or exactness of inverse limits is used. Finite differential generation is used exactly for eta_r phi_(r+1) = pi_r.

There is a historical ancestry mismatch: the inherited blueprint.from.place names a Jacobian paragraph in lem-trf-local-term-locality. I read the latest blueprint ancestor's statement/proof and sk-i-curve-zero/_section.md, as well as the chapter/unit records. The current ancestor is the contracting-correspondence local-term argument and has no Jacobian paragraph. Q31's accepted conormal report already records this mismatch and preserves original Steps 5-8, which are exactly the argument the present auxiliary node isolates. I retain that established ancestry and explicitly identify the mismatch in split_report.blueprint rather than manufacture a current blueprint paragraph or change the chapter/unit route. The split does not add a route or a tool theorem from another unit; only the two definition nodes are used.

## Searches and duplicate audit

I searched the entire DAG for Tags 02HQ and 00RO, universal derivation, ideal-power differential estimates, shifted differentials and complete-module reconstruction; I opened the potentially relevant mod-power-ideal comparison, adic-differential-quotient-interleaving, the parent continuous conormal statement and the two actual definition dependencies. The mod-power comparison is a tensor isomorphism and is unnecessary here. The interleaving node assumes a completed algebra with an additional finite separable coefficient field and does not state the present general interface; it too is unnecessary. The universal derivation and symbol generation are in the cited definition's statement itself, not merely its proof.

Whole-blueprint searches with blueprint_refs.py for differential, derivation and 02HQ found no imported statement of this reconstruction. The ancestor command confirms lem-trf-local-term-locality. No new nodes means there are no new-node/existing-node duplicate pairs.

I ran the prescribed msearch.py commands for this item: two different LeanFinder phrasings, Loogle with KaehlerDifferential and AdicCompletion, LeanSearch for complete modules reconstructed from compatible quotient differential maps, and source grep (both continuous/completion terminology and precise candidate names). All services answered. I read every returned hit. I inspected Mathlib/RingTheory/Kaehler/Basic.lean lines 295-334 for universal lifting, and 500-578 for the free-symbol quotient and its equivalence, and AdicCompletion/Basic.lean lines 710-745 for IsAdicComplete.lift, of_comp_lift and mk_lift. Those provide parts of the construction, not all clauses of this item or a one-line specialization. The logged queries and results have been appended verbatim to mathlib_searches with no-match verdicts; no query is invented or recorded unavailable when it answered.

## Unfinished work

None for stage 1. No Lean file was written, no compiler or build tool was run, and no repository or launcher file was changed. This is a direct delivery; the maintainer provides the independent review.

## Review by Q73

I read Stacks algebra.tex Tag 00RO, label lemma-universal-omega, including the preceding explicit free-module quotient, and Tag 02HQ, label lemma-differential-mod-power-ideal, including its Leibniz estimate. The tag/label pairs were verified against stacks-project/tags/tags. I also read Q31's preserved original reconstruction Steps 5-8 in coord/reports/Q31/lem-trf-formal-power-series-continuous-conormal.md. The present six steps retain their argument and spell out scalar structures and both inverse computations. The complete item is an agent auxiliary deduction, not the tensor statement of 02HQ.

Step 1 cites def-weil-pbc-kahler-differentials for additivity and the precise product rule. Its statement expressly defines these properties. I wrote the entire finite-product expansion, including the derivative of the outside coefficient a_0; every coefficient has at least r ideal factors. This is the elementary power estimate itself, not an uncited application of the mod-power comparison theorem.

Step 2 cites the same node for its universal bijection Hom(Omega,M) to derivations, which its statement explicitly gives for every module. I checked that Q_r is really an R_(r+1)-module, since m^(r+1)N is contained in m^rN, and that D_r is independent of the representative by Step 1. Reduction proves additivity, vanishing on k and Leibniz. The universal property is the sole non-elementary invocation. R-linearity and R_(r+1)-linearity are equivalent for these two modules because the ring quotient is onto, so uniqueness has exactly the strength required by the item.

Step 3 uses only the assumed generators delta(x_i), the assumed phi formula and the eta formula just proved. I wrote the linear-combination argument for arbitrary z. It proves eta_r phi_(r+1) = pi_r on all N, not just on derivation values or a dense submodule.

Step 4 cites the explicit free-symbol quotient in the same definition node to justify generation by differentials. Its statement does give that presentation. The R_r scalar structure annihilates m^r C_r; finite sums a z prove that phi_r kills m^rN and give the quotient map without an extra exactness theorem. On each differential generator bar-phi_r eta_r is tau_r, and quotient-ring coefficients lift to R, so the test proves equality of the R-linear maps on the whole domain.

Step 5 again uses only that explicit generation statement, now on C_(r+2). Both composites have domain C_(r+2) and codomain Q_r and send d[x] to delta(x) mod m^rN. I checked the index tau_(r+1), not tau_r, in this identity and then substituted a compatible tuple to prove that the sequence for Psi is compatible. No assertion is taken from a node's proof.

Step 6 cites def-trf-continuous-kahler-differentials, whose statement constructs the limit as the submodule of compatible tuples with componentwise operations. Its zero-based index n with exponent n+1 is precisely the positive r index of the item. The hypothesis on phi gives Phi; Step 5 and the assumed iota isomorphism give Psi. The two inverse equations are explicitly proved by their rth coordinates, using Steps 3 and 4 respectively. Injectivity of iota is used only for Psi Phi; Phi Psi is tuple equality. Linearity follows from the componentwise formulas and the inverse of the given module isomorphism. There is no theorem asserting preservation of exactness by an inverse limit hidden in this step.

I checked the B-E return checklist against the actual node and sources. There are no new statement-only records, hollow definitions, unsupported facts, off-unit statement tools or circular citations. Both cited nodes are existing definitions with the needed universal property or construction stated explicitly. Every step is shorter than 2000 characters; the longest is 826 characters, and none conceals an auxiliary lemma. The item statement and its statement dependencies remain unchanged, and citations.json quotes the opened statements literally for exactly the used pairs. Proof dependencies are exactly their union.

Small cases checked: d=0 forces N=0, and the given phi formulas force d[x]=0 in every C_r, so all inverse formulas still hold. If m=0 the towers are constant and the reconstruction is the ordinary differential universal map, with generation supplying its inverse. If m=R completeness forces N=0 and all R_r and C_r are zero. For r=1 the ideal estimate differentiates products of two ideal elements into mN, so the necessary shift really is present. No characteristic is excluded: for k of characteristic p, delta(t^p)=0 by the same product rule, with no division by p. Nilpotent ideals, the zero ring and non-finitely-generated ideals introduce no change because only finite expressions of individual ideal-power elements are used. I found no false imported clause and made no statement correction.
