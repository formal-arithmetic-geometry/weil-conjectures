# Worker report: lem-trf-normalization-finite-prime-fibres

## Files written

- dag/nodes/sec-trace-formula/lem-trf-normalization-finite-prime-fibres.json: statement, split; Mathlib verdict no match. The statement is unchanged. Six proof steps give the completed-branch bound, not just finiteness.
- citations.json: twelve step/node entries with verbatim statement quotations, covering every citation in the six steps.
- searches.jsonl: five fresh item searches recorded by msearch.py. The inherited searches in the item are retained.
- report.md: this report. No new nodes, Mathlib leaves, or unit-record changes.

## Attachments

None. I searched WeilConjectures in the read-only slopmaster2 source for the blueprint tag, the item id, integral closure, normalization and finite-prime-fibre terminology. There is no declaration stating this arbitrary-Noetherian-domain assertion together with its completed-branch bound. The finite-type curve and Dedekind declarations do not supply it. No compiler or Lean-writing tool was used.

## Sources wanted

WANTED: Swanson–Huneke, Integral Closure of Ideals, Rings, and Modules, Proposition 4.8.2 and Lemma 4.8.3, printed pp. 83–84 (author-hosted PDF pp. 97–98), for lem-trf-normalization-finite-prime-fibres. The local literature/swanson-huneke-integral-closure.pdf is absent. I read the author-hosted PDF online at https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf, without downloading it. As required for a missing local document, proof_origin.by is agent. Proposition 4.7.3 and Theorem 4.3.4 in that book were also read to check the completion-component comparison and the localness input. The proof uses existing Stacks-based henselian tools for localness, rather than the stronger finite-normalization theorem.

## Problems found and changes

The item arrived as an unsplit statement with no proof. Its statement agrees with Proposition 4.8.2, including the cardinality bound, so there is no statement dispute or added hypothesis. I retained its creation metadata, source ancestry, and inherited Mathlib searches. The historical blueprint ancestry is through lem-trf-local-term-locality and the normalization descendants of specialization to the normal cone; it is not a verbatim normalization assertion in the current blueprint. The detailed from.place records this rather than inventing a sentence. Whole-blueprint searches found no same-statement blueprint node, so same_as is empty. This is not a unit key node, hence no realized fields are changed.

The tempting stronger complete-local finite-normalization theorem is unnecessary. Existing complete-pair henselianity and integral-component permanence prove localness of each branch normalization. Existing completed-branch lifting supplies the lift of every fibre prime. I explicitly identify its algebra map with the fixed fraction-field map before counting, so a different choice of lift cannot silently give a different contraction for the same branch.

I searched the whole DAG by normalization, completion, finite fibres, henselian and source-place terminology, and searched the blueprint with blueprint_refs.py before considering additional nodes. This found all needed nodes already present. The general localization-prime correspondence is used, not a narrower node about a particular localization. The complete-local henselian tools replace the proposed new locality node. No new node restates a clause of the item, and no elementary counting or fraction calculation is made into a node.

The fresh msearch.py searches used LeanFinder, Loogle, grep and LeanSearch, with a second natural-language formulation. The hits in Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean around primesOver_finite and RingTheory/QuasiFinite/Basic.lean around Algebra.QuasiFinite.finite_primesOver were read. They require a Dedekind extension ring or quasi-finiteness, hypotheses not available here. The field-degree bounds do not give this completed-branch bound. No Mathlib match is claimed.

## Unfinished work

None in this one-level split. The already-existing cited unsplit nodes remain their own future work; no proof or statement of another worker's node was edited.

## Review by NU

I read Proposition 4.8.2 and its proof in the author-hosted Swanson–Huneke PDF, and Lemma 4.8.3 immediately following it. The latter packages a lifting fact; our cited DAG node has an independent proof using flat tensor extension and lying over, and does not cite the present item. Thus using it does not import a circular proof from the order of the book. I also checked the source's completed-component setup in Proposition 4.7.3. Local Stacks algebra.tex Tags 0307 and 00E3 give the localization interfaces; Tags 05GG and 05GI support the completion setup. Local more-algebra.tex Tags 0ALJ and 092X give complete-to-henselian and integral-domain-over-henselian locality. No SGA source is used.

For Step 1 I opened the full statements of def-weil-pbc-localization-at-prime, lem-weil-pbc-localization-noetherian and lem-weil-pbc-integral-closure-commutes-localization. They give precisely localness, Noetherianity and the equality of the localized integral closure with the integral closure in K. The multiplicative set is R minus a prime, and its elements remain nonzero in K, so the displayed fraction argument verifies the domain and fraction-field hypotheses needed later.

For Step 2 I checked clause (1) of lem-weil-pbc-localization-prime-residue-field-iso. It is the full prime bijection for an arbitrary multiplicative localization. Applying it to N, not just to R, is permitted. The restriction to the fibre is justified explicitly by extension/contraction and the denominator calculation. No residue-field assertion or unproved fibre-identification theorem is used.

For Step 3 I read lem-weil-pbc-local-completion-local-ring and lem-trf-normalization-completed-product-comparison in full. The former supplies n=mH and the residue-field identification, hence contraction n to m. The latter explicitly supplies a finite exhaustive list of minimal primes, complete Noetherian local domain quotients, injectivity of A into each quotient, the induced K embeddings, and integrality of the images of B. These are actual clauses of its statement, not facts inferred from its title. The identification of the maximal ideal of a quotient of the local ring is written out. No analytic reducedness of H is assumed.

For Step 4 I opened lem-weil-pbc-complete-pair-henselian, def-weil-pbc-henselian-terminology, def-weil-pbc-integral-closure and lem-trf-integral-component-henselian-permanence. The hypotheses hold: C_i is complete at n_i, T_i is a nonzero subring of a field and integral over C_i, and its only idempotents are 0 and 1. Permanence explicitly supplies both localness of T_i and localness of the map. The additional prime-over-maximal-is-maximal argument is elementary and is included: a least-degree monic relation over a field gives an inverse for each nonzero element. It is not hidden behind the definition of integrality or a missing theorem citation.

For Step 5 I checked every clause of lem-trf-normalization-completed-branch-lift. It gives the minimal completed prime, the A-algebra map, the lifted prime and both contractions. Step 1 verified its Noetherian local domain and normalization hypotheses. The product-comparison statement supplies exactly the injective denominator map needed to identify the lifting map with j_i. Writing db=a and cancelling the nonzero image of d in the branch fraction field proves uniqueness directly. This fraction computation is a step, not an unnecessary new lemma.

Step 6 uses only the preceding constructions and finite-image counting. Every contraction is a prime over m, and every prime over m occurs among the r contractions. Coincidences between branch contractions are allowed, so the conclusion is a bound rather than an unjustified equality. The localization bijection transfers that bound to the original fibre.

I checked small and potentially misleading cases: R a field and p=0 give one branch and the single zero prime; the argument does not require p nonzero. A normal local R may have several completed branches, and distinct branch contractions may coincide; the proof still gives the required inequality. A nonnormal local domain with multiple completed branches is allowed. Nilpotents in the completion cause no assumption failure because the argument passes to its minimal-prime quotients. Neither excellence of R nor module-finiteness of its normalization is assumed.

Against delivery-errors B through E, I checked that all non-elementary inputs have existing-node citations, every cited statement actually contains the asserted clause, and the proof is more than an application of a renamed clause. All twelve quotations in citations.json were compared with the current repository statements and are literal substrings. proof_deps is exactly the union of uses. The four off-unit generic tools are declared in split_report.tool_uses; the definitions and Mathlib leaf are notions, and the remaining algebra nodes lie in this item's unit. No proof step exceeds 2000 characters (the longest is 960); I nevertheless inspected the locality, map identification and counting arguments for hidden lemmas. They are explicit short consequences of the cited statements. There are no new nodes to audit for duplicate sources, and no unsupported attachment or hollow construction.
