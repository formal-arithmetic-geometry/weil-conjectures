# Stage 1 worker report: `lem-exc-field-sections-stalk-invariants`

## Files written

- `dag/nodes/sec-curve-estimates/lem-exc-field-sections-stalk-invariants.json`: repaired into four proof steps, deleting the unused representable/G-set step and expanding the descent argument.
- `dag/nodes/sec-curve-estimates/lem-exc-finite-galois-sections-descent.json`: repaired statement-only descent node; Mathlib searches found no match.
- `citations.json`: verbatim citation fragments for every node used by every step.

## Attachments

None. No sorry-free declaration for this item was found in `/home/ubuntu/weil-conjectures-slopmaster2/WeilConjectures` by searching the item id, the stalk/invariant terms, and the relevant declaration names.

## WANTED

WANTED: `literature/stacks-project/etale-cohomology.tex`, Tags 04JM and 03QW, for `lem-exc-field-sections-stalk-invariants`; the checkout used for this worker contains the citation index but not the fetched Stacks TeX files.

## What was changed

The returned node had an unused representable/G-set step and omitted the details required for finite-separable representatives and finite Galois descent. I removed that step, added the site restriction via etale-covering composition, and wrote the cofiltered germ injectivity and finite quotient invariance arguments. I also corrected the embedding argument from equality of subgroups to the required inclusion when `j(L) != L'`, and made the finite-descent node state its Galois hypotheses and pullback action.

## Review by M1

I read the item source citation (Stacks Tags 04JM and 03QW) and the direct proof in the available Stacks checkout, and compared the statement with the parent blueprint paragraph. I also read the source statements of `lem-weil-pbc-etale-fibre-discrete-separable-points`, `lem-weil-pbc-finite-galois-receiving-separable-extensions`, `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`, `def-weil-pbc-etale-sheaf-of-sets`, and `lem-weil-pbc-etale-covering-composition`.

Step 1 uses etale composition and the repaired finite-Galois descent statement; both say exactly that the restricted functor is a sheaf and that sections descend as Q-invariants. Step 2 uses the geometric-stalk colimit, the finite-separable fibre decomposition, the finite-Galois receiving-extension lemma, cofilteredness, and the sheaf equalizer definition. I verified that these supply each hidden hypothesis: the connected component is `Spec` of a finite separable extension, it embeds in `K^sep`, it can be enlarged to finite Galois `E`, and the germ map is injective because the relevant morphism is a covering. The finite-descent node explicitly supplies the Q-action by pullback. Step 3 uses Yoneda naturality and the stalk action; I corrected the false conjugation equality to `sigma(L)=j(L) subseteq L'`, yielding `sigma^{-1} H_{L'} sigma subseteq H_L`. Step 4 checks independence of sigma and sheaf naturality. I checked every citation against the exact statement and recorded verbatim fragments in `citations.json`.

I checked the edge cases `L = K`, where the formula is `F(Spec K) = M^G`, and `K` separably closed, where `G` is trivial. I also checked that every cited node says the fact used, that no definition node is being used as a theorem, and that `proof_deps` is exactly the union of the step uses. The off-unit generic tools are `lem-weil-pbc-etale-covering-composition`, `lem-weil-pbc-etale-fibre-discrete-separable-points`, `lem-weil-pbc-finite-galois-receiving-separable-extensions`, `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`, and `def-weil-pbc-etale-sheaf-of-sets`; they are declared below because this unit has no replacement nodes for site theory or stalk indexing.

## Review by M1

The returned points were repaired as follows: the unused cyclic G-set step was deleted; step 1 now states the small-site restriction and cites etale composition plus finite descent; step 2 contains the finite-separable representative, finite-Galois enlargement, cofiltered germ injectivity, and Q-invariance details with all six source nodes cited; step 3 uses the corrected subgroup inclusion; and the finite-descent statement now defines the finite Galois hypotheses and Q pullback action. I ran the DAG and split checks, verified all citation quotes verbatim, and tested the two edge cases above.
