# Stage-1 delivery: lem-sfb-relative-global-ci-koszul-regular

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-global-ci-koszul-regular.json: statement, split; no Mathlib match. Five steps reuse existing nodes; the statement and its three statement dependencies are unchanged.
- citations.json: a verbatim statement quotation for every cited node in every proof step.
- report.md: this report. searches.jsonl was written by the mandated search command.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, relative-global-complete-intersection terminology and Koszul regularity found the definitions and separate local-regularity / regular-to-Koszul results, but no declaration asserting the whole item. In particular Algebra.isRegular_localization_of_relativeGlobalCompleteIntersection is only the local regularity input, not an attachment for global Koszul-regularity. Upstream sorry declarations are not counted as finished proofs.

## WANTED

None. All source text needed is available locally.

## Problems and corrections

The imported item had no proof. Its statement agrees with Stacks 07D2 and is not disputed. The specified presentation hypothesis matters: the intrinsic existence of some complete-intersection presentation alone would not make an arbitrary redundant list of equations regular. I retained the specified-presentation wording, and did not add Noetherian or nonzero-quotient hypotheses.

The blueprint ancestor command prints from.node=None, as in the inherited node. The creation chain ends at a Lean module, rather than a blueprint id; this is already recorded on the ancestor lem-sfb-admissible-direct-image. I retained the inherited provenance and via list, named its direct-image proof (3) support in split_report, and searched the whole blueprint. No same-as match: the searches for 'relative global complete intersection', 'Koszul regular' and 'Koszul' found no blueprint statement of this item. The latest unit and direct-image proof were read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/. No chapter/unit change is needed for this local algebra input.

## Not duplicates

No new nodes were created. Existing local regularity (00SV), regular-to-Koszul (062F), Koszul scalar extension, exact localization, module localization and maximal-localization detection are cited instead of recreated. The ordered ring-sheaf Koszul torsion node concerns a different model and an ideal power, so I did not use it for exact annihilation of this exterior-algebra Koszul complex; the one-line contraction calculation is written in the proof itself.

## Review by Q108

I read Stacks more-algebra.tex, Tag 07D2 (lemma-relative-global-complete-intersection-koszul), including the reduction to primes containing the ideal, and its explicitly cited algebra.tex Tag 00SV (lemma-relative-global-complete-intersection-conormal), assertion (1). I also read the contraction statements 0626/0663 and their calculation, and 062F with its proof. The proof keeps precisely this local-regularity route. There are no new node sources to review.

For step 1 I opened def-weil-pbc-koszul-complex. Its statement gives the degree-minus-one derivation formula d(v wedge z)=phi(v)z-v wedge dz, which gives the displayed identity for each standard basis vector. For a cycle the second summand is zero; the first is a boundary. Linear combinations of these generators annihilate homology. This is a few-line calculation, so no separate annihilation node is created. It holds in all characteristics, including characteristic two.

For step 2 I read the complete statements of lem-weil-pbc-relative-global-complete-intersection-local-regular-sequence and lem-weil-pbc-regular-sequence-koszul-regular. The first assumes exactly the same specified polynomial presentation and an arbitrary commutative base. It asks for a prime of P/I, so the proof explicitly forms Q/I and verifies primality and the inverse-image equality. It returns regularity in P_Q, exactly what 062F requires. The latter states regular implies Koszul-regular without a Noetherian assumption. I checked the local-regularity Lean declaration as supporting source information, without compiling or treating it as a global result.

For step 3 I opened lem-weil-pbc-localization-module-exact, lem-sc-koszul-base-change-iso, and def-weil-pbc-module-localization. Exact localization applies to arbitrary modules and arbitrary multiplicative sets; there is no finiteness assumption on kernels or homology. Its kernel/image and quotient consequences give the homology comparison directly; the step spells out which exact sequence gives the quotient. The base-change node states an isomorphism of the entire Koszul chain complexes for any algebra, not just a per-degree coincidence and not just regular sequences. The wedge-coordinate description explains its application to the localization. Thus the local homology vanishing obtained in step 2 is the localization of the global homology module. This step assembles two existing generic results and hides no new comparison lemma.

For step 4 I reread the module-localization definition: each denominator acts bijectively, and multiplication is localized multiplication. Outside V(I) an actual generator f_j is a denominator, since if every generator were in Q then I would be contained in Q. It acts both as zero (step 1) and bijectively, forcing the localized homology module to vanish. This covers the zero quotient without falsely requiring primes over it.

For step 5 I opened lem-weil-pbc-linear-map-bijective-at-maximal-localizations and def-weil-pbc-koszul-regular-sequence, and checked the complex definition's zero negative terms. The detection node concerns arbitrary module homomorphisms, so it applies to 0 -> H_i; its localized source and target are zero. Bijectivity then forces H_i=0. The definition requires all nonzero homological degrees, and the negative degrees vanish directly, so every clause is proved.

I checked delivery-errors B through E: no statement-only auxiliary node contains a proof, no new duplicate or restatement of the item is made, all notions used have defining nodes, every non-elementary input is cited by its statement, no proof of a dependency is used as if it were its statement, and the argument is acyclic. Generic tools from other units are declared in split_report.tool_uses; Mathlib leaves and definitions require no extra route approval. All five steps are below 2000 characters (the longest is 727). citations.json quotes actual statement substrings (the full statements) for every occurrence.

Small cases: c=0 gives P concentrated in degree zero; n=0 with a nonempty fibre forces c=0 by the presentation condition; the zero base ring gives the zero complex; a unit among the equations contracts the complex, and a general unit ideal is covered by step 1 and step 4. A non-Noetherian base is allowed by 00SV as stated; no finite generation of Koszul homology is used. No correction of the source is necessary.

I ran the required Mathlib search command with LeanFinder, LeanSearch, Loogle and grep, and a second semantic phrasing. The hits were standard smooth presentations, ordinary regular sequences and generic homology criteria, not this relative fibre-dimension theorem. All newly recorded queries occur in searches.jsonl; inherited searches and their results are retained, and no unavailable service is reported as a no-match.

## Unfinished work

None in the split. The cited existing DAG inputs remain responsible for their own proof work. No Lean was written and no compiler, Lake or build command was run.
