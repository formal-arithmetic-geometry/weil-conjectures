# Q41: lem-zl-curve-restriction-filtration-spectrum

## Files written

- dag/nodes/sec-deligne-laumon-general/lem-zl-curve-restriction-filtration-spectrum.json — statement item, split into nine steps; Mathlib search finds no match for the complete geometric/classical/common-stage assertion.
- citations.json — one verbatim statement quotation for every cited node in every proof step.
- searches.jsonl — actual msearch.py searches; original Mathlib records in the item are retained.
- report.md and write_split.py — report and sandbox-only reproducible assembly helper.

New nodes: 0. New Mathlib leaves: 0. No unit record changes: this item is not the unit's key statement.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag, curve restriction/filtration terminology, and lisse/pullback concepts. Existing concrete WeilSheaf pullback, lissity, stalk and common-stage category declarations cover pieces, but none states this entire assertion with its classical realization and normalized iterated point-transport compatibility. No proof is accepted just because a declaration's body lacks a literal sorry.

## WANTED

None needed for this split. The blueprint's complete notes remain listed as missing in literature/LIST.md; this assembly instead uses the actual blueprint paragraph, the existing DAG statements, Deligne and Bhatt–Scholze available locally. No SGA source was used.

## Audit findings and changes

The live item was an unsplit statement with no proof, created in the split of lem-zl-two-point-curve-constituent-purity. Its statement is retained verbatim, as are provenance and inherited searches. No released repair note exists. The sandbox contained only dispatcher markers; there was no earlier split, report, search log or running delivery process to resume.

The statement uses the correct residue-degree exponent f, not the constant-extension degree m. A closed immersion first identifies the residue fields of z and its image y on X_{0,m}; only then does constant restriction introduce the power from y to x. No smoothness, dimension-one, connectedness or semisimplicity assumption is used or added. No statement dispute was found. The coefficients remain the prescribed classical lisse adic systems and the sf common-stage heart; the concrete native WeilSheaf category is not silently identified with either.

## Not duplicates

No new nodes. Whole-DAG keyword/statement searches and blueprint_refs.py searches for Frobenius power, lisse pullback, pullback Frobenius, classical realization, power spectrum, filtration spectrum and exact restriction found the existing inputs used here, rather than a need to introduce any replacement clause nodes. In particular the existing lem-zl-power-spectrum-conjugation supplies algebraic multiplicities, lem-zl-constant-extension-weil-heart-equivalence supplies the constant restriction, and lem-zl-immersion-weil-local-behavior supplies the immersion comparison. A traversal of all statement/proof dependencies of the principal cited inputs found no path back to this item.

## Mathlib searches

Ran msearch.py with LeanFinder twice using different formulations, LeanSearch, Loogle and grep. Read every result. The first semantic search returned ordinary structure-sheaf modules, local cohomology and ideal sheaf functoriality. The second returned local cohomology, condensed modules, a period ring and ordinary structure-sheaf stalk restriction. LeanSearch likewise returned ordinary open-immersion restriction and unrelated objects. Loogle's sole Frobenius/pullback hit is a regular-category subobject lemma, not geometric Frobenius of an adic Weil sheaf. The source grep for WeilSheaf/localFrobenius/IsAdicLisseSheaf returned zero hits. All services answered; no failed service is recorded as mathematical absence. The exact queries and returned log records are in mathlib_searches, with the original records preserved.

## Review by Q41

I read the current main-20261015 proof of thm-zl-real-mixed-by-curves, especially paragraph 2 (exact restriction to the slicing curve) together with paragraph 1's reality statement. I read the chapter and unit records and the three-level route rules. The present item realizes that subargument and leaves the unit's curve and purity route intact. I also read Deligne, Weil II (1.1.1), pp.146–147, and (1.1.7)–(1.1.10), pp.150–152, and Bhatt–Scholze 6.8.3–6.8.5 and 6.8.14–6.8.15, pp.59–62. Deligne's finite-residue-point discussion explicitly gives the residue-degree power. Bhatt–Scholze supplies the integral systems/rationalization and ordinary pullback comparison, not a ready-made theorem with all project-specific normalized point transports. I therefore mark this assembly as agent-origin and cite the existing precise comparison statements for those transports.

Step 1 uses precisely the statements of lem-pod-separated-finite-type-base-change, lem-weil-pbc-closed-immersion-integral-separated-uc(c), and lem-weil-pbc-finite-over-separated-finite-type. I checked their full statements, including that the last takes a finite morphism and a separated finite-type structure map. Those are furnished by the first two; no separatedness of C_m is assumed without justification. I read Stacks schemes.tex lemma-separated-permanence (01KU), morphisms.tex lemma-base-change-finite-type (01T4) and lemma-closed-immersion-finite (035C), with the finite-type composition route in the existing node.

Step 2 uses lem-zl-classical-weil-filtration-heart-transport for exactly its asserted short exact heart sequences and common finite coefficient stage. Its statement permits finite constant extensions, empty filtrations and the specified top identification. Exactness of a chosen integral-lattice sequence is not inferred from rational exactness.

Step 3 uses part (a), not the proof, of lem-zl-constant-extension-weil-heart-equivalence for exactness and its unchanged carrier with the iterated Weil isomorphism. It uses part 1 of lem-zl-immersion-weil-local-behavior over k_m for exact pullback in the actual Weil heart. A closed immersion is an allowed locally closed immersion. The cokernel universal property supplies the canonical quotient comparison in the step; no new node merely repeats this clause.

Step 4 uses lem-zl-classical-finite-weil-diagram-realization to obtain finite locally free normalized integral systems and to match their realizations to the given ones. I corrected the draft to cite this existence statement, rather than simply presuming arbitrary classical integral models to be finite free. The item supplies a finite diagram, including inverse Weil maps, so the lemma applies. I read lem-per-lisse-completed-system-comparison for its integral-system equivalence and its pullback/scalar/composition clauses, and lem-tw-lisse-rational-realization for the fully faithful rational realization and ordinary inverse image on lisse objects. Pulling the finite-level trivializing covers and free modules back proves lissity. These schemes are separated finite type, as checked in step 1. No claim that a Weil map preserves a lattice is made.

Step 5 takes naturality, identity and composition from those same two comparison statements. It writes explicitly why their composition law applies to g_X^m h = h g_C and to the Weil map and its inverse. For the potentially delicate point transports it cites lem-zl-classical-local-frobenius-iterate-comparison: I checked that its statement gives each of the three factors, all iterates, coefficient extension and the grouping of m successive factors after constant extension. A merely fully faithful functor or equality of traces would not suffice, and neither is used as that assertion here.

Step 6 opens both cited geometric statements again. The immersion statement gives a closed image y, the residue isomorphism and the intertwining b. Constant restriction gives a closed x, positive residue degree e, the q_y equation and the intertwining a with F_x^e. Equality of residue fields identifies e=f, and multiplying the equations gives the displayed c=ab conjugacy. The operator is the normalized geometric Frobenius and not arithmetic Frobenius. This is checked for each term and quotient, not just G.

Step 7 uses the exact characteristic-polynomial identity of the existing lem-zl-power-spectrum-conjugation with K=Qbar_l and n=f>=1. Conjugacy means the same matrix in transported bases, so its polynomial is unchanged. The power lemma explicitly allows nonsemisimple operators and records algebraic multiplicities. Step 8 uses the equivalence in def-wf-iota-real between real local polynomials and conjugation-invariant eigenvalue multisets, then the final assertion of that same power lemma. Its statement explicitly sums multiplicities when distinct eigenvalues collide after powering. I did not assume the quotients of a real sheaf are themselves real; reality is concluded only for R_m G.

Step 9 is elementary: r=0 forces G=0; exactness preserves zero; zero local factors are 1; the empty scheme has no closed-point assertions. I tested m=1, zero rank, empty C_m, disconnected C_m and nontrivial Jordan blocks. For a concrete exponent check, q=2, m=2 and x of degree d=2 give f=m/gcd(d,m)=1, so using m would be wrong. For a collision check, a conjugate pair i,-i powered by 2 gives -1 with multiplicity two; a nontrivial Jordan block needs no diagonalization.

I checked delivery-errors B–E against the written item: there are no new-node statement/source/duplicate obligations; every non-elementary input is a cited existing statement with an exact quotation in citations.json; no definition is cited for an existence or exactness theorem; no clause is moved to a fresh node; all stages use the same coefficient categories; no hidden finite Tor or lattice-invariance hypothesis is introduced. Every proof step is below 2000 characters. I declared the off-unit permanence, immersion and realization citations as generic tool uses in split_report, with reasons; these do not replace any unit argument.

## Remaining work

No mathematical subargument is left unaccounted for in this one-level split. Existing unsplit dependencies remain their own DAG items. The required server dry run and direct push are the delivery checks; no Lean source is written and no compiler/Lake/build command is run.
