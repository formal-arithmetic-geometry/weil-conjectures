## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-fd-l2-plancherel-shift.json`: statement, split; no Mathlib match. Three proof steps, no new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each step/node citation.
- `searches.jsonl`: search-command log, retained as generated.

## Attachments

None. The audit names `AlgebraicGeometry.WeilComplex.l2Weight_fourierTransform` in `WeilConjectures/DeligneLaumon/AffineLine/FourierWeight.lean:116–148`, but the current read-only checkout's file has only the different theorem `AlgebraicGeometry.le_add_one_of_isFourierPartner` (with `sorry`). A whole-tree search for the item tag, theorem name, Plancherel and l2Weight found no replacement declaration proving the item. The theorem `WeilSheaf.l2Weight_eq_sub_of_traceEnergy_eq` in TraceEnergy.lean:245 concerns two sheaves, not arbitrary Weil complexes or Fourier transform, so it is not an attachment.

## WANTED

None. The current blueprint statement and separate proof file are present locally. This is a proof expanded from the agent-written blueprint, recorded with `proof_origin.by = agent`, not a claim of following an unavailable human text.

## Corrections and source audit

Read the chapter `sec-deligne-laumon-a1`, the unit `sk-p-dl-a1-fourier-weight`, and the current main-20261015 statement and `.proof.md` for this item. The unit's upper-weight argument uses Plancherel; this item realizes only its intermediate growth shift, not the unit's key upper-bound proposition. The unit's binding records therefore were not edited. The old master proof agrees with the current separate proof file.

The imported argument compressed both the identity of normalized sequences and the supremum translation into one sentence. I made those arguments explicit, including extended-real cases; no analytic limit-interchange or finiteness-of-weight assertion is needed. The original statement assumes the chapter's fixed nondegenerate character and coefficient/embedding conventions. I made these conventions explicit: finite field, coefficient prime distinct from its characteristic, fixed complex embedding, nontrivial additive character, shift [1], and extended-real interpretation of the weight. This does not strengthen the source's intended hypotheses: `def-fd-additive-character` supplies precisely the fixed nontrivial character, and `def-fd-transform` supplies the shift. In particular this is not a new theorem for the trivial character. For a trivial character and the constant sheaf on the affine line, the input energy is q^m, whereas the transform has constant trace -q^m and energy q^{3m}; the weights are 0 and 2, contradicting a shift of one. That case is excluded by the existing chapter convention.

The historical `rests_on_sorry` audit is stale relative to the supplied source checkout. Its three LowerShriekOperations declarations are not found by whole-tree name searches, and their named file is absent. The affine direct-image finiteness declaration still exists at LowerStar.lean:411 and is sorried. It is a transitive input of the pre-existing Fourier package, not a fact used by the ratio/supremum argument of this item. The historical audit is preserved unchanged; it is not claimed closed. No unrelated replacement nodes are invented from absent Lean declarations. The proof's actual non-elementary input is already the existing `cor-fd-plancherel`, whose own audit contains these same frontier entries. Its own splitting task retains those dependencies.

## Mathlib and duplicate searches

All Mathlib queries in the item were run through the mandated `msearch.py` command and are recorded verbatim in searches.jsonl. Both semantic phrasings were read. Fourier-integral/Lp isometry hits refer to the analytic Fourier transform; the ExpGrowth hits define growth by a logarithmic limsup. Neither gives the present statement for Weil complexes by one-line specialization. The first Loogle query reported unknown identifier sSup and was replaced with OrderIso.map_sSup, which is only a general order result. Its needed special case is proved explicitly in the item's last step; it does not warrant a new node.

Whole-DAG name/keyword searches and `tools/blueprint_refs.py search 'Plancherel'` found the existing Plancherel node, this item and the distinct middle-extension corollary. That corollary has extra lisse/purity/middle-extension content and is not the same statement. The second blueprint regex query returned no matches. `blueprint.same_as` is therefore empty. No new nodes, duplicate pairs or Stacks-source claims are introduced.

## Review by Q109

I checked B–E against the actual node statements and the current main-20261015 sources, not just dependency names. The two cited nodes were opened in full: `cor-fd-plancherel` states the exact squared trace-sum identity on the affine line, and `def-wf-l2-norm` states the normalized positive-limsup supremum with empty supremum minus infinity. The current blueprint proof gives these same two inputs. I also read the current kernel/Artin–Schreier context and the additive-character and transform definition nodes to check the conventions. There are no new node sources to audit and no Stacks tag to resolve for this finite-sum/algebraic argument.

Step 1 uses only those two nodes: instantiate Plancherel with K = F and n = m, and identify its displayed sums with the energy definition using the same embedding. All hypotheses match: F is a Weil complex on the affine line, m is positive, and the nontrivial character and normalization are fixed. No purity, irreducibility, lissity or nonzero condition is imported from the unit's separate upper-bound theorem.

Step 2 cites the definition and uses the identity established in step 1. The three written equalities use positivity of q and the exponent identity m(beta+1)-m = m beta. Because the sequences are identical term by term, their limsups agree even if infinite. This is an elementary substitution, not an unstated analytic convergence theorem. The equivalence beta in S_G iff beta-1 in S_F proves both inclusions of the translated set.

Step 3 cites the definition and uses the translated set from step 2. In the finite nonempty bounded case I checked both parts of the least-upper-bound characterization: s+1 is an upper bound, and any upper bound u forces s+1 <= u. Empty and unbounded cases are handled separately. There is no hidden general supremum lemma left for another node. Each proof step is under 700 characters, so none triggers the long-step review threshold.

For small cases, identically zero trace sums give empty parameter sets on both sides and weight minus infinity; the equality therefore still holds. A skyscraper of weight zero at the origin has constant energy 1, admissible parameters beta <= -1 and weight -1; Plancherel gives energy q^m and weight 0, which checks the sign and the added one. For abstract energy q^{cm}, the threshold is c-1 before and c after multiplication by q^m, including a positive limsup at the endpoint. Translation preserves an unbounded parameter set as checked in step 3. These tests also rule out the common erroneous beta+1 change of variable.

The citation quotes in citations.json are literal substrings of the cited statements. The only non-elementary step takes exactly what Plancherel's statement says, rather than its proof or a definition purporting to assert an extra property (C1/C4). There are no new clauses moved into restatement nodes (D1/D2), no induction or circular reference, and no unexplained transport/comparison (D/E). All historical blueprint/import/audit fields remain available to the independent maintainer. The item now has exactly the union of proof uses as proof_deps; its statement also names the definitions of the Fourier transform and the character.

## Not duplicates

No new nodes; no new/existing pairs.

## Unfinished work

No part of this one-level natural-language split is left unfinished. The two cited nodes remain separate existing DAG work, and no Lean was written or compiled. Maintainer attention: refresh the stale source audit described above; it is not evidence of an attachment in the current checkout.
