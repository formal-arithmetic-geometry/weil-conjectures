# Worker report: lem-per-higher-graded-cokernel-perturbation

1. Files written: dag/nodes/sec-deligne-laumon-a1/lem-per-higher-graded-cokernel-perturbation.json (item, statement preserved verbatim, nine elementary proof steps, status split); report.md; citations.json (empty because no proof step cites any node). No new nodes and no Mathlib leaves.
2. Attachments: none. Searched lean/WeilConjectures for the blueprint tag, ArtinRees/artinRees, higher graded cokernel, approximate complexes and preimage perturbation. The AdicTower and filtered-complex declarations concern different objects. No matching project proof was found.
3. WANTED: none. ILO and Stacks sources are present and were read.
4. The item has no statement error. It already omits the source's unrestricted perturbed exactness clause, which would require an extra hypothesis. The Jacobson-restricted existing bound lemma cannot be cited for this unrestricted conclusion, and its proof is not a substitute for its statement. The finite argument is instead written in full in the item.
5. Unfinished: none within the one-level stage-1 split. No Lean files, compilers, Lake commands, repository writes or manual git commands were used.

## Sources and route

Read SETUP.md's three levels, GOAL.md, the worker and stage-1 instructions, and delivery-errors B through E in both copies. Read chapter sec-deligne-laumon-a1 and unit sk-p-dl-a1-perverse. Read the current latest blueprint's lem-per-artin-gabber-affine-curve statement and proof, especially Step 3, and the live parent lem-per-gabber-graded-model-approximation. This is the already chosen supporting commutative algebra branch for uniformization and duality, without changing the chapter or unit route. No SGA source is used.

Read ILO, Expose III, section 4, Definition 4.4 and Proposition 4.5 with its proof, printed pp.39-41 (PDF pages 45-47), and Theorem 5.1 proof on pp.41-42 for the caller. The low/high degree argument and quotient-kernel description are 4.5(iii), with q in place of m and a=n+1-c. The algebra clause is 4.5(iv).

Read Stacks Tag 07VE, more-algebra.tex, lemma-approximate-complex, first proof paragraph and the following displayed preimage inclusion. That finite induction does not use finiteness, Noetherianity, or the Jacobson condition. Only the subsequent infinite-intersection step needs the latter condition. Read Tag 07VF, lemma-approximate-complex-graded, as a width-one comparison; it is not used as a theorem giving the higher-width or Jacobson-free statement.

## Searches

Searched the whole dag/nodes for 07VE/07VF, lemma-approximate-complex, finite adjustment, perturbed preimages, transferred bounds and graded cokernels; read the statements of all relevant hits listed below. Ran tools/blueprint_refs.py ancestor for the item, and search for Artin-Rees, perturb, approximate, preimage and cokernel. No blueprint node states this unrestricted comparison. The inherited blueprint ancestor and full via chain are preserved, with same_as empty. There is no released repair note for this item and no earlier split/report in the sandbox.

All Mathlib searches were made using msearch.py. The actual results are in searches.jsonl, and the item records its two semantic phrasings, LeanSearch, Loogle and grep. The log also retains actual searches concerning a potential finite preimage supporting lemma, ultimately not created. Read the promising hits in Mathlib/RingTheory/AdicCompletion/Functoriality.lean, lines 381-390, Exactness.lean around 184, and Filtration.lean around 227 and 389. The lifting lemmas assume surjectivity of a fixed map modulo I and improve its approximate solutions; map_exact concerns completed maps; bounded_difference compares already stable filtrations with an existential bound; exists_pow_inf_eq_pow_smul supplies a bound for one fixed submodule. None gives perturbation of both differentials with the prescribed bound, or the higher-width comparison. Loogle's LinearMap range/pow hits are Fitting decomposition for powers of an endomorphism. The grep hit in Prime/Homeomorph is unrelated. No service was unavailable in this run. Historical Q74 searches in the imported item are preserved as historical records, not claimed as searches performed by Q153.

## Not duplicates

There are no new nodes. I checked these existing statements before deciding what to cite:

- lem-sfb-perturbed-image-artin-rees-bound assumes I is in every maximal ideal and concludes a transferred image bound for finite modules. It cannot supply the Jacobson-free assertion here. Its six-step finite proof agrees with the direct induction used here, but this item does not cite that proof as a statement.
- lem-sfb-adic-relation-matrix-initial-ideals assumes a local Noetherian ring with maximal ideal and gives width-one initial-ideal equality after an existential closeness threshold; it is not this fixed-width, unrestricted assertion.
- lem-per-gabber-graded-model-approximation algebraizes finite type models and depends on the item. It cannot be used here without a cycle.
- lem-per-rig-smooth-presentation-perturbation concerns actual isomorphisms of completed algebras under conormal power-splitting, not image-filtration bounds.
- lem-sfb-artin-object-graded-approximation algebraizes objects of a fibred category and gives ordinary graded ring comparison, not this module statement.

## Review by Q153

I checked the item against ILO III 4.5 with the source open. Its statement remains byte-for-byte unchanged. It says precisely the higher-width cokernel assertion with integer degrees and a=n+1-c, and makes no exactness claim for the perturbed pair. The single statement dependency def-weil-pbc-noetherian-ring defines the Noetherian assumption correctly: every ideal is finitely generated. All other notions are defined inline or basic linear algebra. I opened every candidate citation's statement and found that the Jacobson-restricted candidates cannot be applied here; no proof step relies on them. Accordingly citations.json is empty, and proof_deps is exactly the union of uses, the empty set.

Steps 1-5 spell out the finite preimage correction in 07VE. Step 1 states both invariants and the base: x_t lies in I^tM, p'(x_t) is the fixed y, and x-x_t lies in im r'. Step 2 expands finite sums to prove the coefficient order estimate. Step 3 applies the given p-bound at t+c+1, using j>=t+c+1. Step 4 applies the given r-bound only when t>=c, and treats t<c separately. It defines x_{t+1} explicitly and proves its order. Step 5 checks both invariants using p'r'=0, terminates at k=j-c, and obtains the transferred image bound. No step invokes a non-elementary theorem; these are finite induction, the hypotheses and linearity written out in separate elementary steps. No Jacobson assumption, completion, intersection theorem, or perturbed exactness is smuggled in.

Step 6 is the q<=c comparison: n+1=c+a>=q+a and a>=1 put the difference in both the shifted denominator and I^qF, and interchanging the two maps gives the reverse inclusion without needing any bound. Step 7 is q>c: lift through p using the given bound and through p' using step 5, then use step 2 to compute the error exponent n+1+q-c=q+a. The reverse inclusion uses the transferred bound, not an unproved symmetry of complexes. Both containments are explicit.

Step 8 proves directly that I^qF maps onto I^qQ/I^{q+a}Q for Q=F/im p and that its kernel is I^{q+a}F+(I^qF intersect im p): choose z in I^{q+a}F with the same image as x, and write x=z+(x-z). The converse follows by applying the quotient map. Thus its bijection on representatives requires no hidden isomorphism theorem. Apply the identical computation for p' and use the equal kernels from steps 6-7.

Step 9 checks direct sums by finite support, the scalar action on a representative bx, and for F=B multiplication on representatives xy and the unit 1. The max-exponent inequality checks product containment for negative degrees and independence of denominator representatives. These are direct verifications of the operations, not additional non-elementary lemmas. Every proof step is below 2000 characters; the induction and both comparisons are fully written out.

I checked I=0 (the maps coincide), I=B (all graded quotient pieces vanish), j=c (the induction has no correction steps), c=0, n=c (width one), zero modules/free ranks, q<=-a (zero pieces), -a<q<0, q=c, and q=c+1. In B=k[t] with I=(t), r=0 and p=t^c, replacing p by t^c(1+t^a) tests the exact exponent a and the higher-degree comparison. Dropping p'r'=0 can fail: r=id, p=0, r'=id, p'=t^{n+1} satisfies congruences but gives different graded cokernels at high degrees. The written proof uses that zero-product exactly to preserve y during correction.

As a check that the source's unrestricted perturbed exactness clause cannot be used, take B=k x k, I=k x 0, L=M=B, F=0, r=id, r' multiplication by (0,1), p=p'=0, c=n=0. All bounds and congruences hold, but ker p'=B and im r'=0 x k. The finite correction and graded comparison are valid. This is not a new statement dispute: the live item already excludes this conclusion. No item hypothesis was changed.

## Dry-run repair

The first dry run rejected an extracted finite-preimage lemma because the new node shared the item's Stacks tags and was cited by the only non-elementary step. I followed its instruction to write the argument directly in the item. The undelivered helper was removed; its entire finite induction is now steps 1-5. The two graded image inclusions and quotient/action/multiplication checks remain steps 6-9. This removes the unnecessary node and leaves no unproved black box. The report and citations.json were updated to match the final files.
