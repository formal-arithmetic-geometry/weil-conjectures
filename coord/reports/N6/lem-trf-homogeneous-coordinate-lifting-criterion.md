1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-homogeneous-coordinate-lifting-criterion.json`: statement, now split into four elementary proof steps; no exact Mathlib match. The statement and statement dependency are unchanged.
- `citations.json`: the verbatim polynomial-coefficient definition used in Step 1.
- `report.md`: this report. No new nodes and no Mathlib leaves were created; `searches.jsonl` records the six actual N6 searches.

2. Attachments

None. Searched `lean/WeilConjectures/` by the exact item/tag, homogeneous submodule, coordinate lifting and telescoping. The returned project declarations concern other graded modules, formal lifting or chain telescopes; none states this criterion. No Lean was written or compiled.

3. Sources wanted

WANTED: Bierstone--Milman, *Canonical desingularization in characteristic zero by blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), printed p.275, Proof of Theorem 8.1 after Lemma 8.5, for lem-trf-homogeneous-coordinate-lifting-criterion. The paper is absent from the repository literature. I read the journal PDF online at https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf, PDF page 69 (zero-based page 68), including Lemma 8.5 and the final telescoping/induction paragraph. In accordance with the missing-local-literature rule, proof_origin is agent, and each step gives that exact online source instead of falsely attributing this argument to the locally present ILO PDF. No download was made.

4. Findings

No statement error or missing hypothesis. The crucial endpoint is positive degree: with degree zero, the lifting condition for polynomials divisible by a variable says nothing, and S=0 over a nonzero A would be a counterexample. The existing hypothesis ell>0 is therefore retained. The source's final correction is expanded with an explicit minus sign: P=Q-sum(D_j(Q)); this avoids confusing Q-rho_r(Q) with rho_r(Q)-Q.

I read the chapter and unit records, and the latest chapter, unit and ancestor proof. The current ancestor lem-trf-local-term-locality follows contracting correspondences, while this created item belongs to the recorded historical local-invariant algebra branch. I retain that provenance and do not change the chapter or unit route. The item is not its unit's key statement, so no unit realization file is changed.

5. Unfinished work

None in the split. This is stage 1 only; formal implementation is left to later stages.

## Review by N6

I checked the statement and four proof steps against BM p.275, the parent lem-trf-initial-diagram-stabilization (whose Step 1 needs exactly S=V in positive degree), and the complete statement of def-weil-pbc-mv-polynomial-ring. That definition explicitly supplies finite monomial expansions, coefficientwise addition, the monomial product law and evaluation. Step 1 takes only those facts, not any theorem hidden in its proof. The quote in citations.json is a verbatim excerpt of that statement. There are no other cited nodes: Steps 2–4 use the hypotheses and the calculation already proved in Step 1.

In Step 1, setting the first r variables to zero discards exactly the monomials having a positive exponent among those variables. Consecutive restrictions leave exactly the monomials with first nonzero exponent at j. Factoring Y_j is subtraction of one from that exponent; it needs neither a domain hypothesis nor division of coefficients. Every remaining monomial retains degree ell. Thus the claimed tail-variable membership and divisibility are proved from coefficients, rather than imported as uncited facts.

For Steps 2–3 I checked the strong induction carefully. H(r) quantifies over all homogeneous tail polynomials divisible by the next variable. At r=0 the assumed lift is P itself. In the successor argument Q is homogeneous because Q belongs to S and S is contained in V_ell. For every j<=r, H(j-1) is earlier and applies to D_j(Q) by Step 1. Their finite sum is Q-rho_r(Q), so subtracting it from Q gives exactly the desired P. No restriction-stability of S is assumed: membership of each restriction difference is what the induction proves. The argument uses just submodule closure, so this whole item needs no auxiliary node or off-unit tool use.

In Step 4 I checked that all n differences have the proved membership and that their telescoping endpoint is rho_n(T)=0. Positive degree eliminates the constant term. For n=0 there are no positive-degree monomials and the sum is empty; for the zero ring all coefficients vanish. Also tested n=1 (the r=0 lifting hypothesis immediately forces S=V), n=2 in degree one (the first-variable part is already in S and corrects a lift of the second variable), and rings with nilpotents or positive characteristic (no cancellation or nonzero coefficient is used). The statement is unchanged and there is no STATEMENT-DISPUTED.

I checked delivery-errors B–E with the files open: there are no new statement-only nodes to duplicate or to hide the item's clauses; all notions used beyond the inline homogeneous-component and submodule descriptions already have the polynomial definition dependency. Before choosing zero new nodes I searched the whole DAG for telescoping, triangular induction and coordinate restrictions and the whole imported blueprint with blueprint_refs.py for telescoping and homogeneous. The hits concern other telescopes, projective homogeneous coordinates or this item's own parent, and no other blueprint statement gives this criterion; same_as remains empty. All arguments are written in the item, the induction is noncircular, proof_deps is precisely the union of uses, and each step is under 2000 characters. There is no SGA citation.

I retained the imported Q19 search records and ran six actual N6 searches with msearch.py, reading the returned names/types and the local homogeneous-polynomial and evaluation definitions. LeanFinder and LeanSearch return homogeneousSubmodule and graded/localization constructions; Loogle returns eval₂Hom and its substitution laws; the second semantic phrasing returns finite-field evaluation and Rees filtration facts. Grep returns tactic telescopes and homogeneous-component/evaluation occurrences. These are ingredients or unrelated special settings, not the whole coordinate-face lifting criterion or a one-line specialization of it. The elementary coefficient calculation does not warrant creating nodes for these ingredients. The unavailable verdict was not used for any successful search.

## Not duplicates

No new nodes. The only changed node is the assigned item; its parent uses this criterion for a particular span and is not a second statement of it.
