# Stage 1 report

1. Files written: the repaired item node; new Mathlib leaf `lem-sc-etale-at-prime-formally-etale-cotangent-criterion`; `citations.json`.
2. Attachments: none.
3. WANTED: none.
4. Repair: the prior split was returned for D1 and C1 because it quoted the item-sized criterion and left openness, cotangent detection, localization, flatness, and unramifiedness uncited. I added the strict smaller Mathlib cotangent-support leaf and rewrote the proof as four implications. The item itself is not present as a sorry-free project declaration.
5. Searches: the new leaf records the required LeanFinder, Loogle, grep, and unavailable LeanSearch queries, with the exact Mathlib declaration and line.

## Review by K1

I read the item's source references (Stacks Algebra Tags 00U1, 00U6, 00UW, and 08WD), the blueprint ancestor `lem-sc-mult-n-etale-kernel`, and every cited DAG statement. The new leaf is the primewise specialization of Mathlib `Algebra.etaleLocus_eq_compl_support` (Mathlib/RingTheory/Etale/Locus.lean:58), so it states formal etaleness exactly as vanishing of the localized `H_1` and Kähler differential modules; its searches and match are recorded in the node.

Step 1 uses that leaf and `lem-weil-pbc-etale-near-prime-naive-cotangent-vanishing`; those statements supply localized cotangent detection and the etale basic open, respectively. Step 2 uses the affine etale ring-map criterion to obtain both global vanishings, then applies the leaf after localization at `qS_g`; the localization identity is elementary. Step 3 uses the etale-implies-flat node, flatness under localization, and the affine etale criterion; zero differential modules remain zero after localization, an elementary module calculation. Step 4 uses openness of flatness, flatness under localization, affine-sections flatness, the affine unramified criterion, and the etale definition. The finite generation of differentials follows from finite presentation, and choosing `g2` from vanishing at `q` is the standard finitely generated localization argument; these are the only elementary transitions. `citations.json` quotes the exact statements used in every step.

I checked hypotheses at each application: finite presentation of `S` is part of the item; the openness lemma is applied with `M=S`; localization primes are `qS_g` and `p`; and the final map is locally of finite presentation, flat, and unramified before invoking `def-weil-etale-morphism`. Small cases (a localization at a prime and a zero finitely generated module) confirm the two localization arguments. The return points D1 and C1 are repaired by removing the item-sized quotation, adding the Mathlib leaf, and citing every non-elementary input. Off-unit citations are declared as tool uses because the unit route has no replacement nodes for those generic algebra facts.

## Second reading by K1

- Item statement: checked against Algebra Tags 00U1, 00U6, 00UW, and 08WD; the finite-presentation, localization, flatness, and differential hypotheses and all three conclusions agree, including field and zero-ring cases.
- New Mathlib leaf: checked against `Algebra.etaleLocus_eq_compl_support` in `Mathlib/RingTheory/Etale/Locus.lean:58`; it is a self-contained primewise specialization with definition nodes and recorded searches.
- Step 1: the cotangent leaf and `lem-weil-pbc-etale-near-prime-naive-cotangent-vanishing` provide exactly the localized vanishing to an etale basic open.
- Step 2: the affine etale criterion and cotangent leaf provide both directions; zero-module localization and `(S_g)_{qS_g}=S_q` are elementary.
- Step 3: the etale-flat, localization-flatness, and affine etale statements apply; the flatness passage now explicitly applies localization first to `S_g` and then to `R\to R_p`.
- Step 4: openness of flatness, localization flatness, affine flatness, the affine unramified criterion, and the etale definition provide the claimed neighborhood; finite-presentation hypotheses are present.
- Changes: repaired the two-stage flatness localization in step 3 and added this audit; no nodes were removed.
