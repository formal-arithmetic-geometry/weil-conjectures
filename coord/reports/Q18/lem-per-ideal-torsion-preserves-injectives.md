# Worker report

Item: lem-per-ideal-torsion-preserves-injectives. Group Q18. Stage 1, direct delivery. Date: 2026-10-19.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-ideal-torsion-preserves-injectives.json: existing statement node, now split into six proof steps; no exact Mathlib match. The statement and statement dependencies are unchanged.
- citations.json: eight exact statement excerpts, one for every step/node citation.
- report.md: this report and the signed review below.
- searches.jsonl: actual searches recorded by the required launcher search command.

New nodes: none. New Mathlib leaves: none. Existing Mathlib leaves reused: lem-sf-baer-criterion and lem-weil-pbc-artin-rees, plus the existing Noetherian and ideal-power-torsion definitions.

## Attachments

None. Searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag and for ideal torsion, torsion injectivity, primary components, Baer and Artin–Rees. The project torsion-quotient injectivity declaration is about injective functions on quotients, not injective modules. No project declaration states the item. No upstream master sorry declaration is treated as a finished proof.

## WANTED

None: all source material used is already in literature/. The item is exactly Stacks 08XW (2). The proof supplied here is an explicitly agent-written alternative using the existing Baer and Artin–Rees nodes; it is not attributed to the essential-extension proof of 08XW.

## Findings and changes

The item had no proof. Its statement is correct: commutative Noetherian ring, arbitrary ideal, arbitrary injective module, and injectivity as an A-module, without finite generation of that module. Stacks dualizing.tex, lemma-injective-module-divide (Tag 08XW), assertion (2), has precisely this conclusion. Its proof first treats principal torsion using essential extensions and then iterates over ideal generators. The present node-level argument uses the same theorem's full generality but gives an explicit Baer–Artin–Rees proof using two existing general-purpose Mathlib leaves. Its provenance is marked agent, and each step names its sources. Nothing above the node level is replaced: the item remains the injective-preservation input of lem-per-local-cohomology-sum-spectral in the existing ancestry below lem-per-artin-gabber-affine-curve. I read the chapter and unit records and the main-20261015 ancestor statement and proof; the item is not the unit key node, so no unit record is changed.

Proof: for f:J→Γ_K(E), choose a single m killing its image using finite generation of J. Artin–Rees on J⊆A gives n with J∩K^n⊆K^m J, hence f vanishes on the intersection. Therefore h(j+k)=f(j) defines an A-linear map J+K^n→E. Injectivity of E extends h to g:A→E. Since g is zero on K^n, its value at 1 is killed by K^n, and g takes values in Γ_K(E). This establishes Baer's extension test for that submodule.

The original Mathlib search records were retained. I ran LeanFinder, Loogle, source grep and LeanSearch for this item, and a second semantic phrasing before deciding no match. LeanSearch returned Module.Injective and unrelated torsion/noetherian embeddings; LeanFinder returned Artin–Rees, adic completion and Krull intersection results; Loogle with Module.Injective and Ideal.primaryComponent returned no hit. I read Module.Injective, Module.Baer and Module.Baer.iff_injective in Algebra/Module/Injective.lean and the primary-component source. The initial grep restricted to a file yielded heading-only results with incomplete path formatting; I recorded that limitation and ran the directory-restricted grep separately. All actual queries, including that initial attempt, are retained. No search was invented or repeated from an earlier sandbox attempt; the sandbox initially contained no node, report or search log.

## Not duplicates

No new nodes were created. The whole-DAG tag search for 08XW found this item and its parent spectral-sequence item only. Whole-blueprint searches for ideal-power torsion and 08XW found no matching blueprint node; the broader torsion search gave coefficient categories and unrelated torsion results. Searches for Baer and Artin–Rees led to the existing general leaves, which are cited rather than duplicated. In particular, no node for the uniform annihilator, the sum-ideal map or the final extension was created: those are short explicit steps of this proof.

## Unfinished work

None for this one-level split. This delivery writes no Lean, invokes no compiler or build tool, and modifies no shared repository or launcher file.

## Review by Q18

I opened the item, every cited node, the two Mathlib leaf source locations, Stacks dualizing.tex Tag 08XW (lemma-injective-module-divide), more-algebra.tex Tag 0AVF (lemma-characterize-injective-bis), and algebra.tex Tag 00IN (lemma-Artin-Rees). The item agrees with 08XW (2), including arbitrary E and arbitrary K. There are no new statements requiring a further source or hypothesis review. The alternative argument is deliberately marked as agent-written: 08XW is evidence for the statement, whereas 0AVF and 00IN provide the non-elementary ingredients of this particular proof.

Step 1 cites def-sbc-ideal-power-torsion-functor for the actual submodule Γ_K(E), not for an injectivity claim. It cites lem-sf-baer-criterion, whose statement gives exactly the equivalence between injectivity and extension of maps from arbitrary ideals. Thus the test used is genuinely a cited statement. A universe containing A and E and the finite constructions is chosen, satisfying the cited criterion's common-universe condition without restricting the mathematical statement.

Step 2 cites def-weil-pbc-noetherian-ring, whose full statement is that every ideal is finitely generated, and the torsion definition for the annihilating exponents of f(j_i). With these statements the uniform exponent is a finite-sum calculation, written out in the node. It does not assume E or Γ_K(E) is finitely generated. I used m=1+Σm_i rather than a maximum of a potentially empty set, so the ideal J=0 causes no exception. Commutativity justifies moving coefficients through the action.

Step 3 cites lem-weil-pbc-artin-rees. I read its exact statement: its containment is I^n M∩N⊆I^(n-c) N for n≥c with M finite over a Noetherian ring. Here M=A is generated by 1, N=J, I=K, and n=m+c≥c. Thus it says precisely J∩K^n⊆K^m J. The vanishing on that product is an explicit finite-sum calculation from Step 2, not another uncited algebra theorem. In particular the proof never applies Artin–Rees to E. The Mathlib source theorem Ideal.exists_pow_inf_eq_pow_smul in RingTheory/Filtration.lean:389 supplies the cited leaf; its lines 389–391 were read.

Step 4 has no external citation because well-definedness of h on the sum ideal is written out: two decompositions differ by an element of J∩K^n and f vanishes there. Its two linearity formulas and its two restrictions are elementary consequences of that formula. There is no quotient-descent or gluing assertion left implicit.

Step 5 uses the forward implication of lem-sf-baer-criterion for the already injective module E and the ideal J+K^n. Its statement really does give an extension on A. The remaining calculation is g(a)=a g(1)=0 for a∈K^n, so the torsion definition, cited explicitly, puts g(1) in Γ_K(E). Commutativity then puts every b g(1) there. No claim that a submodule of an injective is automatically injective is used. Step 6 uses the opposite implication of the same criterion for the now-verified ideal-extension property of T.

I checked delivery-errors B–E against the written files. There are no unsplit new nodes with hidden proofs, missing notions, duplicate statements, false Mathlib leaves or clause relabellings. The statement is unchanged, dependencies are the union of the uses, each quoted sentence or formula in citations.json is an actual substring of the cited statement, and the two off-unit theorem citations are Mathlib leaves, not replacements of a unit route. No SGA source is used. Every step is under 500 characters, so none reaches the long-step review threshold, and their subarguments are nevertheless explicit.

For edge cases, K=0 gives Γ_K(E)=E (take exponent 1); K=A gives Γ_K(E)=0 because every power is A; nilpotent K again gives E; E=0 and J=0 are included by the formulas. In the K=A case, the annihilation obtained in Step 2 forces f=0, making the sum-ideal map zero as required. These tests also show why a positive m and no properness hypothesis on K are appropriate. I found no statement dispute. The concrete repairs during writing were to avoid an empty maximum, state every Artin–Rees substitution, and show both well-definedness and torsion-valuedness of the extension instead of treating them as unnamed standard facts.
