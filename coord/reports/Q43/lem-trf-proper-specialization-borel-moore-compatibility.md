## Worker report

Files written:

- dag/nodes/sec-trace-formula/lem-trf-proper-specialization-borel-moore-compatibility.json — item split into eight steps; statement unchanged; zero new nodes and zero Mathlib leaves.
- citations.json — verbatim statement excerpts for every citation of every step.

Attachments: none. Searches of the read-only slopmaster2 WeilConjectures/ source for the exact blueprint tag, proper specialization and Borel–Moore terminology found the pushforward definitions in TraceFormula/Correspondence.lean and trace-class proper compatibility in ProperPushforward.lean. Neither states the specialization identity. Searching the TraceFormula directory for nearby or specialization found no implementation. Upstream master is not used as evidence of finished proofs.

WANTED: none. The Varshavsky PDF and Stacks source read below are present locally.

The input correctly uses the structure-morphism adjoint definition of Borel–Moore specialization, with bounded-below compact-support operations on intermediate nearby cycles. I retained its full statement, including total properness of the lifted morphism and the specified adjunction normalizations. There was no sandbox item, proof or search log from a prior attempt to preserve. The item's inherited Mathlib searches remain unchanged.

All argument steps of the item are complete. No Lean was written, no compiler was run, no git command was run in a shared checkout, and no live project or launcher file was modified.

## Sources read

I read Varshavsky, §§1.3.1–1.3.3, printed pp. 10–12: the explicit BC! formula in §1.3.2(b), its proper inverse relation with BC* in (c), and the Borel–Moore specialization of Example 1.3.3(b). I also read Theorem 2.1.3(b), printed pp. 17–18, and the current main-20261015 proof of lem-trf-local-term-locality, which makes the normal-cone reduction the route of the unit. The expanded adjoint and mate calculations are written here rather than quoted as a theorem of the paper, so proof_origin.by is agent.

For compact-support composition I read Stacks more-etale.tex, Tag 0F7J, label lemma-shriek-composition, its compatible compactification calculation and independence argument. The delivered proof uses the stronger existing DAG interface lem-amb-unbounded-compact-support-comparisons, which explicitly gives normalized composition, compact-support base change and their compatibility on general Noetherian schemes, including its bounded-below restriction. It does not merely infer coherence from existence of an unspecified isomorphism. No SGA source is cited or used.

## Searches and reuse

I searched the whole DAG for nearby/specialization composition, BC composition, §1.3.2 and Tag 0F7J. I read the statement files for the nearby-cycle finiteness/exchange, structural identities, cohomological comparison, compact-support tower formula, proper composition site transport, and general compact-support comparisons. Whole-blueprint searches using tools/blueprint_refs.py included 'specialization proper', 'nearby', 'compact support' and 'specialization'; ancestor gives lem-trf-local-term-locality, through lem-trf-specialization-zero-section. The item's blueprint metadata and its proof place are retained and explained in split_report.

I initially proposed a separate compact-support exchange coherence lemma and ran its searches. The five actual searches are retained in searches.jsonl: two LeanFinder formulations, Loogle, Mathlib grep, and LeanSearch. The signatures concern scheme structure-sheaf stalk specialization, ordinary sheaf whiskering and pushforward composition, normed-ring Units.ofNearby, compactly supported continuous functions, Zariski-module pseudofunctors, and homological cycles. None constructs this geometric nearby-cycle comparison. Grep had no hits. Those searches are not falsely recorded as a Mathlib match.

The first dry run identified the full set of existing nodes sharing Tag 0F7J. I opened every one. In particular, lem-amb-unbounded-compact-support-comparisons supplies the stronger coherence interface needed for a short mate calculation. I removed the proposed new node rather than keep an elementary consequence of that interface. The current delivery therefore creates no nodes and has no new-node search obligations. All inherited item searches are preserved.

## Not duplicates

No new node is delivered. The proposed lem-trf-specialization-compact-support-coherence was removed after reading the Tag 0F7J candidates. The item now cites the existing general compact-support comparison theorem and proves the required nearby-cycle identities directly in steps 4 and 6.

## Review by Q43

I read each cited statement with the item and sources open. Step 1 checks the hypotheses of the generic comparison interface instead of applying its Noetherian version to an unchecked base. In k[t]_(t), minimal t-order proves every nonzero ideal principal, hence the ring is Noetherian and a DVR. The precise strict-henselization lemma states the DVR equivalence for a Noetherian local ring. The definition of a DVR includes principal ideals, so the strict ring is again Noetherian. The finite-type-over-Noetherian theorem applies to the strict-trait lifts, their compactifications, and the finite-type geometric generic fibres over a field. The deformation definition supplies the bounded-below candidates, and the general comparison statement explicitly identifies their normalizations with its bounded-below restriction.

Step 2 expands the actual ordinary-unit/proper-comparison/exceptional-counit definition in def-trf-borel-moore-pushforward. The normalization in def-trf-admissibility says exceptional composition is the conjugate of compact-support composition. The explicit counit of def-weil-pbc-composite-adjunction and the dualizing identification of thm-trf-dualizing-complex-composition give e_U F_aU(p_h)=e_T. Substitution proves equation (1), including its special-fibre instance. This uses the specified constructible exceptional adjunctions, without an assertion about a right adjoint on an unrestricted pro-etale category.

Step 3 uses the final structure-adjoint formula in def-trf-deformation-specialization and its invertible can_s. Naturality of the specified compact-support exchange rewrites the formula into (2); this is elementary substitution. The only exceptional adjunction is between the stated constructible finite-Tor endpoints. The intermediate nearby-cycle terms are used only with bounded-below compact support.

Step 4 proves the proper inverse relation at the level of the actual maps. The identity-open compactification identifies proper compact support with ordinary direct image. Ordinary direct-image composition gives Q because tilde h j_T = j_U h_eta. The two exchange constructions in the deformation definition, expanded with the explicit mate-pasting and identity rules, become E_h=i_U^*Q C_i^{-1} and B_h=C_i i_U^*(Q^{-1}). The displayed j-adjoint explicitly checks which comparison Q is; cancellation proves the inverse relation. Thus this property is not attributed to a definition without its argument. The general compact-support comparison node supplies C_i and C_j with these proper normalizations.

Step 5 uses the sentence in lem-trf-nearby-cycle-finiteness-exchange that the ordinary exchanges respect the nearby-cycle unit. I wrote its actual ordinary-adjoint equation for constants; the input A_T on the geometric generic fibre is bounded constructible finite-Tor, so the existing theorem is used in its domain. Step 4 then gives equation (3). Total properness of tilde h is part of the item, not inferred from properness of h and h_0. The unit directions are A_U -> Rh_* A_T and A_U0 -> Rh_0* A_T0, as required by the pushforward definition.

Step 6 supplies the composition calculation rather than hiding it under the word 'compatibility'. I defined C_i, C_j and m_f from the deformation definition. The existing general comparison theorem states the two C composition equations; the j-adjoint of the proposed composite m_g m_f is written out, with the middle unit-counit cancellation justified by the mate-pasting statement. Naturality of C_g,i then gives E composition. This is specialized to f=h, g=a_U. The statement of lem-trf-proper-composition-site-transport applies because one factor h is proper and identifies the etale/pro-etale compositors used here. No properness of a_U or its total lift is introduced.

Step 7 writes every equality in (5). The first substitutes (4), the second uses (3), and the third is naturality at the actual ordinary unit tau_h. Step 8 substitutes (1), (2), and (5) into the adjoint of the special-fibre pushforward. The final hom correspondence is bijective by the stipulated exceptional adjunction, hence equality of adjoints proves equality of sections. These last steps are elementary functoriality calculations. Every step citation has a verbatim excerpt in citations.json, and proof_deps is the union of the uses lists.

I checked the delivery-errors B–E points against the resulting file: no new unsplit node to violate statement-only or self-containedness rules; no unrun search recorded; no definition used as a substitute for an unstated geometric theorem; no proof of a cited node mined for extra conclusions; no cycle through the ancestor or a cohomological-comparison node; no restatement child; and no silent weakening of the item. The general compact-support and categorical tools are declared in split_report.tool_uses without changing maintainer-owned tool_uses. The original normal-cone unit route and blueprint ancestry remain intact.

I checked the small cases: h=id makes both ordinary units, E_h and Q identities, so (5) is tautological. Empty T gives zero compact support and both sections vanish; alpha=0 is preserved by every displayed composition. The composition calculation works with g=id and with two proper factors. With g nonproper it uses only compact support and does not claim ordinary direct-image base change for g. No smoothness or properness over k is added, and S_T omega_T is never identified with omega_T0. The special fibre in every target is that of the lift. All eight proof steps are below 2000 characters. The genuine geometric/coherence inputs are cited; the remaining formulas are the explicit adjunction calculation itself.
