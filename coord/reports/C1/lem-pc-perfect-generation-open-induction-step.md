# Delivery report

Files written:

- `dag/nodes/sec-picard-framework/lem-pc-perfect-generation-open-induction-step.json` — split item, no Mathlib leaf.
- `dag/nodes/sec-picard-framework/lem-pc-perfect-generation-koszul-orthogonal.json` — statement-only child, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-supported-open-pushforward.json` — statement-only child, no Mathlib match.
- `citations.json` — verbatim citations for every non-elementary node used by each proof step.

Attachments: none. No sorry-free declaration with the item tag or exact statement exists in either Lean source checkout.

WANTED: none.

The imported item was checked against Stacks Project `perfect.tex`, Theorem `theorem-bondal-van-den-Bergh` (Tag 09IS), including its induction paragraph and the cited Lemmas `lemma-direct-summand-of-a-restriction` (09IQ) and `lemma-orthogonal-koszul-complex` (09IR). The existing node `lem-sc-perfect-support-map-lift` already states the direct-summand extension needed for Q, so I did not duplicate it. The two new nodes record the independent Koszul orthogonality and supported open-immersion pushforward/restriction results (Tags 09IR, 08DP, 08DF). The item statement and hypotheses were retained.

## Review by C1

I read the complete Tag 09IS theorem proof in `/home/ubuntu/c1-stacks-review/perfect.tex`, the definitions of the Koszul situation and the two cited lemmas, and the source of every existing node cited. Step 1 uses exactly the statement of `lem-sc-perfect-support-map-lift`: with closed support T=X, zero target E, and zero map, its hypotheses are satisfied and it gives a perfect Q whose restriction contains P as a direct summand. Step 2 checks that Z=V minus U is closed in the affine V and has a finite set of generators because U intersection V is quasi-compact; the new supported-pushforward node states both that the Koszul pushforward is perfect and that it is extension by zero. Step 3 uses the extension-by-zero clause to identify the Hom groups by adjunction, then uses the exact equivalence in `lem-pc-perfect-generation-koszul-orthogonal`; the cited statements explicitly provide these implications. Step 4 uses the direct-summand clause again and the generator definition `def-pc-generators` to conclude that E restricted to U and then E vanish.

For the new Koszul node I checked Tag 09IR's affine setup, the quasi-compact overlap hypothesis, and both directions of its equivalence. For the supported-open node I checked Tags 08DP and 08DF in `/home/ubuntu/c1-stacks-review/cohomology.tex`; its three clauses are copied as a single self-contained statement and no proof is hidden in it. I searched the whole DAG for the 09IR, 08DP, and 08DF tags and for direct-summand/Koszul/pushforward keywords before creating either node; no existing node stated these results. I also ran LeanFinder, Loogle, grep, and LeanSearch searches for the item and each new node; LeanSearch was unavailable and is recorded as unavailable, while the other searches found no scheme-level Mathlib theorem. Small cases checked were r=0 (K=O_V), r=1 (the two-term Koszul complex), U=V (Z empty), and U empty (the support criterion reduces to the zero object).

## Not duplicates

`lem-pc-perfect-generation-koszul-orthogonal` vs `lem-pc-perfect-generation-open-induction-step`: the new node is the independent equivalence for a Koszul complex on an affine open, while the item combines this criterion with extension of P, pushforward perfectness, and the final generator argument on X.

## Second reading by C1

- Item statement: checked hypothesis by hypothesis against Stacks `perfect.tex`, Tag 09IS, Theorem `theorem-bondal-van-den-Bergh` induction paragraph; verdict: the qcqs, quasi-compact-open, affine-open-cover, perfect-generator, Koszul-support, and generator clauses agree.
- Step 1: checked against Tag 09IQ and the statement of `lem-sc-perfect-support-map-lift`; verdict: applying it with `T=X`, `E=0`, and the zero map is valid.
- Step 2: checked against Tag 09IS and Tags 08DP/08DF; verdict: quasi-compactness of `U intersection V` gives finitely many generators, and the pushforward/perfectness and extension-by-zero conclusions match.
- Step 3: checked against Tag 09IS lines 3935--3945, the Koszul node, supported pushforward node, and `lem-sc-derived-open-gluing`; verdict: repaired the omitted open-cover argument by constructing `F=R(U to X)_*(E|_U)` and checking its restrictions on both opens.
- Step 4: checked against Tag 09IS lines 3947--3951 and `def-pc-generators`; verdict: adjunction and the direct-summand argument now explicitly precede the generator conclusion.
- `lem-pc-perfect-generation-koszul-orthogonal`: checked against Tag 09IR, including the affine overlap, finite sequence, and both equivalence directions; verdict: retained as an independent statement and defined the Koszul complex explicitly; tested `r=0` and `r=1`.
- `lem-pc-supported-open-pushforward`: checked against Tags 08DP and 08DF; verdict: retained all three clauses, added the ringed-space derived-direct-image definition and an explicit meaning of supported cohomology; tested `U=X` and `U` empty where applicable.

Changes made: Step 3 now cites the existing derived-open-gluing node and spells out the local-isomorphism argument; Step 4 states the adjunction calculation after the equality from Step 3; the item uses TeX for the direct sum; both new statements were made more self-contained and their dependencies updated; the corresponding verbatim citation was added to `citations.json`.

