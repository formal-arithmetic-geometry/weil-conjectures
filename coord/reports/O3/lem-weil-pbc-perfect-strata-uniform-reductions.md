# Stage-1 report: lem-weil-pbc-perfect-strata-uniform-reductions

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-perfect-strata-uniform-reductions.json`: statement, six proof steps, status split; no Mathlib match.
- No new nodes and no Mathlib leaves. `citations.json` contains the verbatim statement for all 16 step/node citation pairs. `searches.jsonl` records five actual searches in this session. `prepare.py` is sandbox-only preparation material, not part of the delivery.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for perfect/stratification combinations. The generic-perfectness and Verdier files do not state the item, including its completed coefficients, all quotient levels and original-cover models.

## Literature wanted

None.

## What changed and what was wrong

The item had no proof. Its statement is unchanged, including its general Noetherian adic datum and its limitation to intrinsic constructibility. The source's Proposition 6.6.11 uses complete local coefficients; the written finite-projective argument works for the item's more general coefficient datum without importing that additional hypothesis. The proof is accordingly marked agent-written, following the finite-model part of the source and spelling out the relevant tensor calculation.

There is no statement dispute. I did not use the unrelated claim about arbitrary etale schemes in Lemma 6.6.10(3). Only part (1), and the reverse finite-model argument of Proposition 6.6.11, are relevant. I did not assert completeness or choose an etale-origin witness.

The chapter and unit were read and are unchanged. The item serves the integral-lattice opening of the current `thm-weil-pbc-finite-extension` proof, through the inherited integral-stratified-perfect characterization. Generic K-flatness, derived scalar extension, and the existing finite-selection lemma are declared as tool uses. No chapter or unit route is replaced.

## Not duplicates

No new nodes were created. Whole-DAG searches for 6.6.10/6.6.11, exact constants, K-flatness, finite pro-etale refinements, coefficient restriction, and stratum detection located the nodes used below. The blueprint searches for perfect, stratified, constant exact, finite reduction, and uniform reduction did not locate a blueprint node stating the whole item. In particular `lem-sfb-stratified-local-cohomological-bounds` supplies finite selection from bounds already established locally; it does not assert the derived quotient model or finite-level constructibility. `lem-sfb-adic-perfect-model-complete-reduction` is a maximal-ideal/residue statement, so it cannot supply all powers of the arbitrary ideal in this item. I instead wrote that elementary calculation in the proof.

## Review by O3

I read Bhatt–Scholze Lemma 6.6.10(1), including its proof that locally closed subsets of a Noetherian space are constructible and Noetherian, and Proposition 6.6.11, especially its reverse implication and the definition of a perfect-valued local model immediately preceding its proof. I also read Stacks sites-cohomology.tex labels lemma-bounded-flat-K-flat (06YS), lemma-derived-tor-quasi-isomorphism-other-side (06YT), and definition-derived-tor (06YU), and sites-modules.tex lemma-constant-exact (093J). For the last step I checked properties.tex lemma-Noetherian-topology (01OZ), topology.tex lemma-constructible-Noetherian-space (005L), and proetale.tex definition-constructible (09AJ). These are available locally; no SGA source is used. There are no new-node sources to review.

Step 1 uses the exact perfect-complex definition and the projective-module lifting/splitting characterization. A surjection from a finite free module splits because the term is both finitely generated and projective; tensor and constants preserve the splitting identity. The flatness argument is written as a retract of a finite sum of the identity tensor functor. The cited ringed-site K-flat theorem has exactly the bounded-above flat hypothesis established here, and the derived-change-of-rings statement explicitly computes scalar extension with that K-flat representative. No flatness of the quotient module over A is assumed. Both the A-constant and B-extended complexes meet this hypothesis.

Step 2 cites the full statement of `lem-weil-pbc-stratum-completion-unit-restriction`. Its scope explicitly includes a composite of stratum restriction and pro-etale restriction, the canonical coefficient identifications, exact module pullback, and the displayed derived quotient comparison. All its hypotheses (Noetherian X and the same adic datum) are present. I use only those clauses, not its completion-unit conclusions. The kernel/image/quotient argument showing commutation with cohomology is explicit, so I have not substituted a definition of inverse image for an exactness theorem.

Step 3 invokes the K-flat computation already justified, and gives the balancing formula for the quotient comparison. For a finite free term it identifies the two sides with the same finite sum of the quotient sheaf; applying the splitting maps gives the finite-projective case. This is a computation from the tensor definition, rather than a new lemma with its own hypotheses. A-linear differentials commute with this formula. The conclusion is a constant *complex* with the same term support for every n, and does not claim that cohomology commutes with scalar reduction.

Step 4 uses `lem-weil-pbc-finite-type-constant-exact`, whose statement gives preservation of kernels and cokernels for an arbitrary commutative coefficient ring, on the already computed quotient complex. The coefficient datum explicitly assumes each A/I^n finite as a set. Each term of the quotient complex is a finite-free retract, hence a finite set; cycles and their quotient by boundaries are therefore finite. Thus the actual constant model is H^q(P tensor A/I^n), not an unjustified H^q(P) tensor A/I^n. This also proves the model assertion on all the originally chosen covering members, not just a later refinement.

Step 5 uses the full finite-selection clause of `lem-sfb-stratified-local-cohomological-bounds` on K with the actual local term intervals of step 1. I checked that it permits variable bounds per original covering member and returns quasi-compact open submembers still covering each stratum. I then use the identical selected family for every K_n; step 3 supplies bounds on each of its members. `lem-weil-pbc-noetherian-stratum-detection` applies to any abelian sheaf with zero inverse images on those stratum covers, and so applies to each H^q(K_n). The bounds are chosen before n; an arbitrary new family depending on n would not prove uniformity.

Step 6 uses the minimal-closed-subset statement of the existing Noetherian-scheme node to obtain the descending-chain condition, then the explicit Noetherian clause of `def-weil-constructible-subset`. The given finite locally closed partition is therefore constructible. The complete definition of `def-weil-proetale-constructible-sheaf` requires precisely this partition, locally constant modules, and finite fibers; step 4 supplies them with the original covers. Every cited node's statement was opened, and the corresponding complete verbatim statement is in citations.json. Nothing is taken from an uncited proof inside another node.

For B--E of delivery-errors I checked self-contained hypotheses, the exact strength of every citation, the distinction between ordinary and completed constants, the lack of a hidden non-elementary comparison, and that the proof has not moved the item's clauses into fresh nodes. Steps 3, 4 and 6 are computations from the stated results and definitions and are marked elementary; steps 1, 2 and 5 cite their substantive tools. No step exceeds 2000 characters. The inherited source, blueprint and creation metadata are retained, along with inherited search records; the five new logged searches are appended accurately. All returned hits were read: adic algebra, scheme-cover infrastructure and generic K-projective complexes do not supply the item.

Small cases checked: X empty (bounds [0,0], and a one-empty-stratum witness for the constructibility definition's N>=1); zero complexes and empty strata; A/I^n the zero ring; I=0 with A finite; shifted perfect complexes and different bounds on different covering members. Finite projective terms may have variable rank; only their finite-free retracts are used. Nontrivial differentials are retained in H^q(P tensor A/I^n), so no false flat-base-change assertion is hidden in the cohomology computation.

## Unfinished

No part of this one-level split remains unfinished. Existing cited unsplit nodes remain separate queue items, as prescribed. No Lean was written or compiled.
