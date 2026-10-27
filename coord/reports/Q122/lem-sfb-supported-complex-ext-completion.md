# Q122: lem-sfb-supported-complex-ext-completion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-supported-complex-ext-completion.json — existing statement, now split; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-short-complex-adic-cohomology-limit.json — one new statement-only unsplit lemma; no Mathlib match after two semantic phrasings, Loogle and source grep.
- citations.json — ten citations with verbatim statements; searches.jsonl — actual search-command records; report.md — this report. write_split.py is a sandbox-only generation script.

## Attachments

None. Searched lean/WeilConjectures for the item tag, supported-complex terminology, and Ext/completion terminology. No project declaration supplies every clause. The generic projective and module facts used here already have DAG nodes, including Mathlib leaves.

## WANTED

None. All required sources are local.

## Findings and changes

The item was unsplit and had no earlier sandbox copy. Its statement is correct, including arbitrary integer a; no hypotheses or conclusions were changed. I read GOAL.md and followed the stage-1-only authorization. There is no Lean edit and no compiler invocation.

The inherited source mentions 0DYJ, 0A6A and 05EC. Reading these showed that directly creating a new 0DYJ node would merely move the first clause of this item into a new node. Instead I use the strictly more general finite three-term algebraic calculation in 0EGU(2). The item itself supplies the finite-free Hom realization, support-to-annihilation argument, completion calculation and identification of both maps. Exact completion of finite modules suffices for the second map, so no new derived base-change lemma is needed. The universal assumption for all finite coefficient modules is retained even though this proof only needs its instance for N in each degree.

The latest blueprint file read was literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3), and the current unit's _section.md. Its current paragraph cites the open-direct-image finiteness theorem. The item's inherited from.place records the deeper deformation/alteration prerequisite chain. The ancestor command returns None for that inherited chain; I preserved its from.node and extended the existing via list for the new node. No chapter or unit route is changed.

The inherited Mathlib searches are retained; current searches for the item and new lemma are also recorded. The new lemma's search hits include Artin–Rees and AdicCompletion.map_exact, which are ingredients rather than the asserted comparison with the limit of quotient cohomology. Loogle with AdicCompletion and homology/ShortComplex, and grep of AdicCompletion sources, gave no such declaration. The search for the prime-radical criterion led to Ideal.radical_eq_sInf; a subsequent whole-DAG search found the existing lem-weil-pbc-zero-locus-eq-iff-radical-eq Mathlib leaf, which I reused instead of making another leaf.

## Not duplicates

lem-sfb-finite-short-complex-adic-cohomology-limit vs lem-sfb-supported-complex-ext-completion: the new lemma concerns arbitrary finite three-term module complexes without support, pseudo-coherence, Ext or power-annihilation hypotheses; its source is 0EGU(2). The item proves both canonical supported Ext maps by applying that algebraic result and separately proving the completion map from exact completion.

lem-sfb-finite-short-complex-adic-cohomology-limit vs lem-sfb-adic-short-complex-cohomology-ml: the existing statement proves Mittag–Leffler, including for some nonfinite terms and exact section functors; it does not identify the limit with completed cohomology. ML alone does not give that identification.

lem-sfb-finite-short-complex-adic-cohomology-limit vs lem-weil-pbc-mittag-leffler-complex-limit-homology: the existing statement compares cohomology of a limit complex with the limit of cohomology under an essentially-constant preceding-cohomology hypothesis. It does not identify the latter with the adic completion of original cohomology, and that essential-constancy hypothesis is not given here in degree a-1.

lem-sfb-finite-short-complex-adic-cohomology-limit vs lem-weil-pbc-completion-exact-finite-modules: exact completion of short exact sequences identifies cohomology of the termwise completed complex with completed cohomology; it does not compare the inverse limit of quotient cohomology. The new Artin–Rees comparison addresses precisely that difference.

Whole-DAG searches for 0EGU and lemma-consequence-Artin-Rees found no existing source-tag node. Blueprint searches for Artin.Rees, short complex, quotient cohomology and cohomology completion found no equivalent blueprint statement. Lean source searches found no completed-project theorem giving the new lemma.

## Review by Q122

I read delivery-errors B–E in both copies in that file and checked the actual node statements rather than their proof sketches. The mathematical sources read for the item are more-algebra.tex Tag 0DYI (lemma-ext-induced-toplogy), especially its finite-free Hom computation; 0DYJ (lemma-ext-annihilated-into), especially the opening finiteness/power-annihilation argument; derived.tex Tag 064B (lemma-morphisms-from-projective-complex); and algebra.tex 00MA (lemma-completion-tensor) and 00MB (lemma-completion-flat). For the new node I read the full statement and the cycle-correction proof of 0EGU (lemma-consequence-Artin-Rees), including the maps H/I^n H to H_n, the delayed reverse maps, and assertion (2). Its source says exactly the limit identification, while naturality follows from its explicit canonical forward maps; no proof is embedded in the new statement.

Step 1 cites def-pc-ring-pseudo-coherent-complex for the bounded-above finite free representative, not merely finite cohomology. I opened lem-sc-bounded-above-projective-kprojective and lem-coef-kprojective-derived-hom-bijection: they respectively give K-projectivity and the bijection from homotopy classes to derived morphisms. Finite free projectivity is justified by lifting basis vectors. Cycles and boundaries of the signed Hom complex describe the maps and homotopies to M[i], so the cited statements provide the exact comparison required, for negative as well as positive i. This works also for the completed coefficient module, which need not be finite as an A-module.

Step 2 uses lem-weil-pbc-noetherian-submodule-finite to make the cycle module finite, and finite generation passes to its quotient by the explicit generator argument. I opened lem-weil-pbc-finite-module-support-annihilator: its statement supplies support = V(Ann), under exactly finite generation. I then opened lem-weil-pbc-zero-locus-eq-iff-radical-eq and used its intersection-of-primes clause; it really gives the needed inclusion in the radical. Finally lem-weil-pbc-fg-ideal-radical-power gives a power in the annihilator because I is finitely generated by the stated Noetherian definition. The final constant-tail inverse-limit argument is written out, with no appeal to completeness of A.

Step 3 applies the new 0EGU lemma only to the three finite modules C(N)^{i-1}, C(N)^i, C(N)^{i+1}; the complex relation is inherited from P. Finite bases identify their quotients with the Hom terms for N/I^nN. Reducing the same matrices checks differentials and transitions, so the canonical map, not just an unspecified isomorphism, is obtained.

Step 4 uses lem-weil-pbc-noetherian-submodule-finite for Z, B, D and the kernel in the preceding degree; the other finite modules are quotients. I opened lem-weil-pbc-completion-exact-finite-modules, whose statement gives exactness for every short exact sequence of finite modules with these very completion maps. The four short exact sequences in the proof identify completed cycles, boundaries and their quotient explicitly. Finite powers commute with the compatible-sequence limit coordinatewise; differential matrices and cycle classes show that the resulting map is induced by N to its completion. No flat base-change claim, no finite projective dimension and no finite A-module hypothesis on the completed module are used. This calculation is short and uses only the cited exactness statement; it is not a separate hidden comparison lemma.

Step 5 is elementary: the two squares commute already on cycles by the formulas for quotient and completion coordinates. The induced cohomology and limit maps are therefore A-linear and natural. citations.json copies each cited statement verbatim; in particular no definition node is being used as a substitute for an exactness theorem.

I checked I=0: all quotient modules and completions are the original modules and both maps are identities. For I=A, the support hypothesis forces each relevant finite Ext module to vanish, and both targets are zero. K=0 or N=0 gives zero groups and zero complexes throughout. A zero ring is harmless. Negative i are treated by the signed Hom model and do not require ordinary nonnegative module Ext. No nilpotence of I on N is assumed; only the relevant Ext module is annihilated by a power, and that exponent may depend on i,N. For the new lemma the zero short complex and I=0,A reduce to identity or zero limits. Finite generation and Noetherianity are necessary for its Artin–Rees argument and are both stated.

All proof steps are below 2000 characters. The new lemma is statement-only, carries complete object introductions, precise tag and label, its own recorded searches and blueprint provenance. I checked the DAG and blueprint for more general existing statements before creating it. The proof uses existing Mathlib leaves wherever available. There is no new clause-restatement, no cyclic appeal to this item, no SGA citation and no alteration of target statements.

## Unfinished work

None for this stage-1 split. The new unsplit general algebraic lemma is intentionally left for its own future stage-1 item.

## Validation

Server review_split passed before this report was written. Full delivery dry-run and push are performed after the completed audit.
