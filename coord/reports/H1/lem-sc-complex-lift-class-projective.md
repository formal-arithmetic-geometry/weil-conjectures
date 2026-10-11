1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-complex-lift-class-projective.json`, statement, split.
- `dag/nodes/sec-abelian-varieties/lem-sc-complex-lift-acyclic-projective.json`, statement-only child, no Mathlib match.

2. Attachments: none.

3. WANTED: none; the cited Stacks source was read from the local review checkout at `/home/ubuntu/c1-stacks-review/more-algebra.tex`.

4. I found no exact declaration tagged `lem-sc-complex-lift-class-projective` or matching the theorem in `WeilConjectures`. The item follows More on Algebra, Lemma 15.75.2, Tag 0BCA. Its proof uses the acyclic lifting lemma, the existing projective-complex derived morphism representative node (Tag 064B), and a derived morphism lifting lemma (Tag 0649). The cone step is elementary. The split-injectivity argument explicitly checks projectivity, quotient splitting, surjectivity modulo I, and class closure.

## Review by H1

I read the full statement and proof of Tag 0BCA and its preceding acyclic lifting lemma in the local Stacks source. Step 1 uses the existing projective-complex representative statement. Step 2 is the mapping-cone calculation. Step 3 uses the acyclic child with its bounded-above, acyclic, termwise quotient conclusion. Step 4 uses the same existing representative statement for the dotted chain map. Step 5 spells out the source’s split-injectivity proof and checks hypotheses (1)--(3) where used. Step 6 takes degreewise cokernels and uses acyclicity to identify the shifted cokernel with K. I checked edge cases I=0 and E^bullet=0 conceptually. The new child was searched in the DAG and blueprint before creation, and LeanFinder, Loogle, and Mathlib grep searches were run and recorded. Citations are verbatim excerpts from node statements.

## Not duplicates

lem-sc-complex-lift-acyclic-projective vs lem-pc-ring-derived-map-representative: the new node lifts bounded-above acyclic complexes termwise through an ideal, while the existing node represents derived morphisms from bounded-above projective complexes by homotopy-class maps.

## Second reading by H1

- Item statement: checked against More on Algebra, Lemma 15.75.2, Tag 0BCA, hypothesis by hypothesis; verdict: agrees, including the five assumptions and the derived reduction conclusion.
- Step 1: checked against the Tag 0BCA proof and the exact statement of `lem-pc-ring-derived-map-representative`; verdict: the bounded-above projective source is `E^\\bullet`, so the cited bijection supplies the quasi-isomorphism.
- Step 2: checked against the cone paragraph of Tag 0BCA and the direct-sum clause of assumption (2); verdict: cone terms and acyclicity are the stated elementary calculation.
- Step 3: checked against the repaired Tag 0BC9 child statement; verdict: all three class hypotheses and the termwise quotient hypothesis match.
- Step 4: checked against the displayed quotient triangle in Tag 0BCA and `lem-pc-ring-derived-map-representative`; verdict: the derived morphism and its chain representative are now stated explicitly, including reduction modulo $I$.
- Step 5: checked line by line against the split-injectivity paragraph of Tag 0BCA; verdict: projectivity gives the lift and splitting, assumption (2) gives class membership, and assumption (3) kills the summand with zero reduction.
- Step 6: checked against the final cokernel paragraph of Tag 0BCA; verdict: the short exact sequence, acyclicity, cone inclusion, and quotient identification are all written rather than hidden behind the cone description.
- New node `lem-sc-complex-lift-acyclic-projective`: checked against More on Algebra, Lemma 15.75.1, Tag 0BC9; verdict: self-contained statement, correct TeX, no unused derived-category object, and no proof content. Existing DAG and blueprint searches found no duplicate; the recorded LeanFinder, Loogle, and grep searches ran.

Changes made: corrected the child source tag from 0BCA to 0BC9, rewrote its statement self-contained in TeX, removed its unused derived-category dependency, and expanded main steps 4 and 6 to state the chain-map and cokernel arguments explicitly.

5. Nothing remains unfinished.
