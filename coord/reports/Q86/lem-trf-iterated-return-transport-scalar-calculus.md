# Stage-1 delivery: lem-trf-iterated-return-transport-scalar-calculus

## Files written

- dag/nodes/sec-trace-formula/lem-trf-iterated-return-transport-scalar-calculus.json: statement, split into six steps; no Mathlib match for the whole statement.
- citations.json: one verbatim statement excerpt for each step/node citation.
- searches.jsonl: actual Q86 search results, retained alongside the item's inherited Q128 search records.

No new nodes; no Mathlib leaves. prepare.py is sandbox-only preparation material.

## Attachments

None. The blueprint tag and return-transport searches found no project declaration stating this item. The sectionsPointTransportIso and coefficient-compatibility declarations in WeilConjectures/SixFunctors/Etale/Derived/CoefficientChange.lean concern the small etale site and ordinary coefficient categories. They do not state the completed pro-etale return-square identities, their whole-diagram realization, and their scalar associators.

## WANTED

None. The available blueprint, Deligne and Stacks sources suffice for the underlying constructions; the explicit mixed calculation is agent-written.

## Corrections and scope

The statement is unchanged. The imported node had no proof. Its displayed identities are well-typed with composition read right to left. The key point in the split is to distinguish the common composite pullback H from its two iterated presentations, rather than infer coherence from existence of unrelated pullback isomorphisms. The existing normalized comparison node explicitly supplies equality on whole quotient diagrams, equality of scheme maps, iteration and the completion-normalized associator. There is no need to create a new lemma restating one of the item's clauses.

The blueprint search for return transport found no node; point transport found def-weil-local-frobenius-trace, def-weil-punctual-weights, prop-trf-karoubi-independence and thm-trf-finite-coefficient-map. These define local operators or state larger trace assertions, not this iteration/scalar calculus. The nearest blueprint ancestor remains prop-trf-karoubi-independence. The new snapshot's unit follows finite levels, reductions, integral realization and rationalization; this split provides the formal compatibility used on that route and changes no unit or chapter record.

## Not duplicates

No new nodes were created. The existing more general one-step point-automorphism compatibility is cited directly.

## Review by Q86

I read the current prop-trf-karoubi-independence proof's final sentence and the current trace-transport unit, together with the chapter/unit records and the parent local-normalization statement. The source asserts that Frobenius is transported but does not give these formulas; I have therefore marked the expanded calculation as agent-written. I read Deligne Weil II (1.1.3), printed p.150, for scalar localization and (1.1.7)-(1.1.8), pp.150-151, for geometric Frobenius and point transport. I also read Stacks sites-cohomology.tex, lemma-derived-pullback-composition (0D6D), and proetale.tex, lemma-pushforward-Noetherian-case (099N), especially clauses (2) and (5). They support the models, not the mixed coherence claim: that claim is taken from the explicit statement of lem-trf-integral-pullback-comparison-realization. No SGA source is used.

For Step 1 I read lem-weil-frobenius-point-transport-natural, clause (2), which asserts naturality for every point-category morphism at all required stages, and the explicit definition of iota. The induction has the identity base and applies that exact naturality equation to U^j(u), so rational morphisms are included. The recursion is an elementary composition calculation.

For Step 2 I read the finite composition node: its statement gives a canonical natural isomorphism of functors with a termwise model. I read the integral realization node, whose specified families are natural and admit arbitrary iterations. Thus both presentations r and s of H are natural. I read the raw rationalization definition: every rational morphism is a finite sum of tensors, so extending a linear naturality equality covers all such morphisms. Substitution into Step 1 proves naturality of t without assuming a Weil structure or inverting t.

For Step 3 I checked the exact mixed equation in the integral comparison node, its equality-of-scheme-maps clause, and its assertion before realization. Apply it to the two words in the GIVEN equality g^m z = z g_s^m. Both comparison paths start at T_s H_E and finish at the appropriate iterated pullback over M. The two resulting equations have the same b. Cancellation of r_M and T_s(r_E) has the displayed direction and yields precisely the requested first identity. This does not deduce equality of derived tower maps from equality of evaluations.

For Step 4 I read the full statement of lem-weil-point-automorphism-transport-scalar-extension, including its specified completion comparison, rational equation, and identity/tower compatibility. Its t is Gamma(kappa) sigma, exactly the definition of iota. The automorphism hypothesis holds for geometric Frobenius on Spec k, and ell is invertible because ell differs from p. I checked the normalization against the integral pullback realization node, which specifies the choices of the scalar comparisons in the integral-operations lemma. I read lem-weil-point-sections-scalar-extension: its inverse is exactly beta, not an unspecified isomorphism. Rearranging its inverse-direction equation gives the one-step identity used here.

For Step 5 the induction is explicit, including delta^0 and delta^(j+1). The coherence node justifies this iterative presentation. The only interchange is naturality of iota_M applied to the actual derived morphism delta^j, which has source T U_E^j N and target U_M^j T N. It is within the point constructible category. The resulting expression is precisely the induction hypothesis followed by the next iota. No unproved iteration lemma is hidden in this step.

For Step 6 I checked the identity and successive-extension sentences in the integral comparison statement and the displayed associator equation in the sections comparison statement. They identify every factor in the successive equations with the direct comparison under the SAME normalized associators. Composition and cancellation preserve those identifications. This is why no additional coherence lemma is needed. All inputs remain in the bounded constructible domains specified in the statement; the integral node expressly does not require finite Tor-amplitude of reductions. The rationalization has the same objects and formally adjoins no idempotents.

I checked small cases: j=0 in both inductions, m=1 giving the original one-step scalar equation, the identity coefficient extension, zero objects and zero morphisms, and X=s with z the identity (the two presentations coincide). None requires a nonzero object, an invertible Weil map, finite Tor-amplitude, or a perfect complex. I traced dependency paths from the four substantial comparison/naturality inputs and found no path back to this item. Every proof step is shorter than 2000 characters. The proof cites statements, not arguments hidden in their proofs. Off-unit general tools are declared in split_report.tool_uses; they do not replace any step of the unit route. No new-node self-containment, tag duplication or leaf-match obligations arise.

The Mathlib searches used the required command. Generic NatTrans.naturality is the defining naturality square (Mathlib/CategoryTheory/NatTrans.lean:57), and Scheme.Modules.pullbackComp/pseudofunctor_associativity (Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:241,273) concern Zariski structure-sheaf modules. I read these candidates; none specializes to the completed pro-etale comparisons in one line. LeanFinder's field-Frobenius hits concern field algebra maps. A second conceptual phrasing was tried. The inherited search records remain intact and the new command results are recorded as returned.

## Unfinished work

None in this one-level split. Its dependencies remain separate DAG work. Server dry run and direct delivery follow this review.
