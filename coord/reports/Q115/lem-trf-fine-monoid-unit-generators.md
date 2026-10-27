## Files written

- dag/nodes/sec-trace-formula/lem-trf-fine-monoid-unit-generators.json: statement, split, no Mathlib match; four elementary proof steps; statement unchanged.
- citations.json: verbatim statement excerpts for all three step/node citation pairs.
- report.md: this report. No new DAG nodes and no Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag, fine-monoid terminology, unit-generator terminology and unit finite-generation terminology. The hits concern other algebraic or sheaf constructions, not this statement. No project declaration states every clause.

## Wanted literature

None. The ILO PDF is available. This auxiliary argument was already identified as an agent algebraic refinement, rather than a verbatim assertion of ILO.

## What changed and what was wrong

The original unsplit item had no proof. The retained delivery added an explicit inverse formula for each generator occurring in a unit expression, then proved both containments of the monoid span, finite group generation and inheritance of torsion freeness. There is no statement dispute, hypothesis change, new dependency, or appeal to a structure theorem for finitely generated abelian groups. All arguments are elementary and remain in the item.

Retained all inherited searches. Ran five actual logged searches (LeanFinder twice with different formulations, LeanSearch, Loogle and grep) and appended their results without inventing searches. Read the returned types and relevant source in Mathlib/Algebra/Group/Submonoid/Units.lean, Algebra/AffineMonoid/Irreducible.lean, GroupTheory/MonoidLocalization/Finite.lean and Algebra/Group/Commute/Units.lean. The Galois correspondence between submonoids and subgroups of units does not identify the unit generators of an arbitrary generating list; Grothendieck-group finite generation concerns the larger completion; the irreducible-generation theorem assumes trivial units; the number-field theorem has extra ring hypotheses. AddUnits.ofNSMul only tests one multiple and does not prove the unit-sublist assertion. Consequently the full item remains a split, not a Mathlib leaf.

## Unfinished work

None in the one-level split. No Lean files were written or compilers invoked.

## Not duplicates

No new nodes. Whole-DAG key-word searches and blueprint_refs searches for "unit group" and "fine monoid" found no imported blueprint node stating the item. The existing fine-monoid-unit-splitting lemma uses this item and proves a different product decomposition; it cannot be used here without a cycle.

## Review by Q115

I read ILO Expose VIII 3.1.1--3.1.3 (printed p.98) and 3.1.11 (printed p.100), including the group-of-units and sharpening definitions and the integral-monoid localization convention. These supply the context, not a claimed verbatim proof of this auxiliary lemma. I also read the item's two definition dependencies in full, the chapter and unit records, the parent unit-splitting proof, and the current main-20261015 local-term-locality statement and proof. The latter's current contracting-correspondence route differs from this historical supporting branch; I preserve the item's ancestry and unit binding and make no claim that the current blueprint explicitly states this monoid lemma. The proof origin is honestly marked agent.

For step 1, def-trf-fine-fan-blowup explicitly defines fine as finite generation and injectivity into group completion; def-trf-fs-log-blowup explicitly defines the abelian group completion. Those are exactly the two cited inputs, quoted verbatim in citations.json. Restricting the ambient abelian-group operations to U requires no theorem: the step writes closure under addition and negation. I checked that no saturation or torsion-free hypothesis is used here.

For step 2, def-trf-fine-fan-blowup explicitly defines units by existence of an additive inverse. The step supplies that inverse, b-u, inside P. Positivity of n_i is used precisely so n_i-1 is a natural number. The expression b contains every remaining occurrence of the generators and lies in P. The equality a_i+(b-u)=0 is just substitution in the ambient group. Thus no uncited summand-of-a-unit lemma or finiteness theorem is hidden in this step.

Step 3 uses only the subgroup established in step 1, the coefficient test proved in step 2 and the chosen generating-list hypothesis. Both inclusions of the monoid span are written, and the group span lies between that monoid span and U; hence it equals U. It cites no external node. Step 4 uses the inclusion already established and the explicit torsion-free hypothesis, again with no external node. All four steps are elementary in the brief's two-or-three-line sense and each is shorter than 2000 characters; the total proof-text length is recorded in the latest repair section below. There are no new subclaims that need separate nodes and no non-elementary literature theorem used without a citation.

I tested P={0} with the empty generating list (both spans are {0}); P=N with generator 1 (I is empty and U={0}); P=Z with generators 1,-1 (both are units and generate as a monoid); P=N direct-sum Z with generators (1,0),(0,1),(0,-1) (only the last two contribute to units); a finite cyclic group (all generators are units, while the final torsion-free assertion is not applied); repeated and zero generators; and a zero coefficient at a nonunit generator. These confirm the positivity condition and the need for the final torsion-free assumption. No small-case correction was needed.

I checked delivery-errors B--E against the actual files: no redundant or statement-clause children, no new statements missing hypotheses, no proof in an unsplit child, no unsupported Stacks references, no off-route theorem, no citation of a dependency's proof, no cyclic use of the parent, and no doubled TeX escapes after JSON decoding. The statement and all maintainer-owned metadata are retained. Only the permitted sandbox is written.


## Returned landing repaired (2026-10-22)

The return at branch head bc26712d023 approved the mathematics but refused landing because the side completion had not been promoted to the live DAG. This is the single return point. I began with the required dry run of the retained delivery; it passed at 9c7f6b8f0cb. I compared the retained item with the current read-clone item field by field: current status is unsplit with no proof, while the statement, stmt_deps, source, chapter, unit and full blueprint ancestry agree exactly. The retained proof, search records and prior report have been preserved. The authorized delivery tool constructs the new commit on current main; I did not issue git commands or modify the shared repository.

I re-read the current statements of def-trf-fine-fan-blowup and def-trf-fs-log-blowup in full. All three retained citation excerpts are still verbatim, including fineness as injectivity and finite generation, the abelian group completion presentation, and the existential inverse definition of units. Their relevant hypotheses still fit: P is fine and commutative, no saturation is assumed, and ambient torsion freeness is used only in Step 4. I also re-read the current parent unit-splitting proof: its Step 3 uses exactly this lemma's finite-generation and conditional torsion-free clauses. No citation needs replacement and no new dependency is justified.

The repair also changes the proof, rather than merely rebasing an unchanged delivery: Step 1 now explicitly reconciles the cited definition $u+v=0$ with the item's subset $u\in P$, $-u\in P$ inside G, proving both implications and identifying v with -u. The Step 1 quote is expanded to include both the injectivity and unit definitions it uses. Step 3 explicitly treats an empty unit sublist, including d=0. Steps 2 and 4 retain respectively the displayed inverse b-u and the ambient torsion-free argument. The statement, route and dependency set are unchanged. These changes close the small definition-identification and empty-list details without introducing a lemma or strengthening a hypothesis.

I re-read ILO VIII 3.1.1--3.1.3 and 3.1.11 (PDF pp.104 and 106, printed pp.98 and 100). They still provide the unit/sharpening and integral-monoid context, while the explicit generating-sublist proof remains correctly marked agent. The current chapter and unit records preserve the historical ancestry already discussed above. Repeated the project-declaration tag/concept search and whole-blueprint checks: no attachment or duplicate was found. Existing logged Mathlib searches were read and retained; no query was repeated because neither the statement nor the search question changed.

For the renewed B--E review: there are no new nodes (B1--B10 and D1--D2 cannot introduce a child defect); all cited meanings are taken from the current statements, with three matching step/node pairs in citations.json (C1--C5); the parent is only inspected, never cited, so no cycle or route replacement is introduced (C6--C8). The inverse expression still uses n_i>0 precisely to ensure n_i-1 is natural, and b-u lies in P precisely because u is a unit. Empty P-generating and unit-generating lists, P=N, P=Z, N direct-sum Z, a finite cyclic group, repeated generators and zero coefficients were checked again against the actual formulas (E1--E7). Every step remains elementary, with each step shorter than 2000 characters. No source or statement dispute was found.


## Current returned landing repaired (2026-10-23)

The current return is the 2026-10-22 16:32 UTC entry at head 40c193c9c14, subsequent to the earlier bc26712d023 repair recorded above. I checked the retained prior execution log: the proof and report now in this sandbox were pushed at 40c193c9c14. The interrupted continuation had made no further delivery. With no active delivery for the item, the required initial dry run completed successfully at 7870eb00516. That receipt checks the retained overlay on the delivery tool's freshly fetched live base; it does not itself push.

Against the current read clone, the returned item differs only in proof, proof dependencies, proof origin, split report, status and the appended actual Mathlib search records. The statement, source, statement dependencies, chapter, unit, creation data and complete blueprint ancestry agree exactly. I retained all previous proof arguments, citation excerpts and logged searches. Re-read the full current statements of def-trf-fine-fan-blowup and def-trf-fs-log-blowup: the former still supplies finite generation, injectivity into the completion and the existential inverse definition; the latter still supplies the abelian group presentation. No citation changed its meaning or needs replacement. All three quotes remain verbatim.

The current repair makes the use of injectivity completely explicit in Steps 1 and 2: an inverse equation established in G is an equation in P by the injective canonical map. This also verifies that the inverse constructed in Step 2 satisfies the cited monoid definition, rather than only an ambient-group equality. Step 3 retains both containments, finite group generation and the empty-list case; Step 4 still uses torsion freeness only under its stated hypothesis. The proof route and hypotheses are unchanged.

For this renewed Review by Q115, I re-read ILO VIII 3.1.1--3.1.3 and 3.1.11 at PDF pages 104 and 106 (printed 98 and 100), both cited definitions, and the current parent unit-splitting statement and Step 3. The ILO text supplies the units/sharpening context; this elementary proof remains marked agent. Under B--E, no new nodes or hidden non-elementary lemmas are introduced; the three citation pairs cover exactly the two cited statements, and all four steps are elementary and shorter than 2000 characters. Rechecked the zero monoid and empty generating list, an empty unit sublist in N, Z, N direct-sum Z, finite cyclic groups, repeated generators and zero coefficients against the inverse formula and the conditional last clause. No statement correction, extra hypothesis, cycle or route change is required. Only the sandbox files are changed.


## Renewed repair after dispatcher continuation (2026-10-23)

The required initial dry run of the retained sandbox completed and exited successfully at c8124e19619. No push was left running. This repair addresses the sole landing return: the approved completion existed only on the side delivery and had not been promoted into the live DAG. The sandbox retains the returned proof and prior repair reports; against the current read-clone item, only the stage-1 completion fields and appended logged searches differ. The statement, statement dependencies, source, creation record, chapter, unit and blueprint ancestry agree. The delivery tool constructs the commit on its freshly fetched current main; no git command was run in the shared repository.

I re-read both current cited statements in full, not their proofs. Step 1 uses exactly the definition of fine (finite generation and injectivity) and the abelian group completion presentation. Step 2 uses the same injectivity and the existential inverse definition. All three citations.json excerpts remain verbatim in those statements. There is consequently no changed citation requiring replacement. The current parent unit-splitting Step 3 still uses this item's finite-generation and conditional torsion-free conclusions, with exactly the hypotheses supplied here.

This is a proof repair as well as a rebase: Step 2 now writes n_i=m+1 with m natural before defining b, rather than silently relying on truncated subtraction. It retains the original b-u inverse formula and its membership in P, exhibits the full equation a_i+(b-u)=a_i+b-u=0, and explicitly reflects that equation from G to P. It also states the contrapositive needed in Step 3: each coefficient outside I is zero, because a natural number that is not positive is zero. These details preserve every existing argument and make the handoff between the two steps explicit.

For the renewed Review by Q115, I read ILO VIII 3.1.1--3.1.3 and 3.1.11 directly from PDF pages 104--106, printed pages 98--100. They provide units, sharpening and integral-monoid context; the auxiliary proof remains correctly marked agent. The current chapter, unit and blueprint-local-term record were read; historical ancestry is preserved. Project searches by the exact blueprint tag and bounded fine-monoid/unit-sublist phrases found no complete project declaration. Whole-blueprint searches for unit group and fine monoid returned no matching imported node. I read and retained searches.jsonl: its five actual searches are unchanged because the mathematical statement and search questions are unchanged.

The B--E check finds no new node to be elementary, duplicate, a clause relabelling or an unsearched Mathlib leaf; no non-elementary result is used by any step. Steps 1 and 2 use only the quoted definitions, and Steps 3 and 4 use the preceding arguments and the explicit hypotheses. All are elementary and below 2000 characters. The monoid and unit spans in the zero-monoid/empty-list case are both {0}; in N only zero is a unit; in Z generated by 1,-1 all chosen generators are units; in N direct-sum Z the first coordinate forces every positive coefficient at (1,0) to be absent from a unit expression. Finite cyclic groups satisfy the unit-generation conclusion, and the last clause is applied only when G is torsion free. Repeated generators, a zero generator and zero coefficients do not affect the displayed inverse construction. No hidden hypothesis, source error, statement correction, route change or circular citation arises. Only this sandbox's item and report were changed.

Current proof-text lengths: 671, 633, 688, 251 characters; total 2243.
