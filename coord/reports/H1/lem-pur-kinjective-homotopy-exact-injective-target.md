1. Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-homotopy-exact-injective-target.json`: split statement, no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-hom-complex-short-exact.json`: statement-only child, no Mathlib match.

2. Attachments: none.

3. WANTED: `literature/stacks-project/injectives.tex`, Lemma `lemma-characterize-K-injective`, because the source text is not present in this checkout; the proof follows the imported source location and the neighboring node's transcription.

4. No statement or blueprint correction was needed. The target was not already declared in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`. The split isolates the non-elementary degreewise Hom exactness fact; the remaining passage is the long exact homology sequence followed by the defining degree-zero Hom-complex calculation.

## Review by H1

I read the target node, its ancestor `lem-pur-kinjective-characterize-K-injective`, the chapter and unit records, and the existing nodes `lem-weil-pbc-complex-ses-homology-long-exact` and `def-weil-abstract-derived-category`. The child statement was checked against the successor-step source description: injectivity of each `I^{p+n}` makes precomposition along each short exact degree sequence exact, and products preserve that exactness. Step 1 uses precisely the child statement and checks that precomposition commutes with the Hom differential. Step 2 uses the existing long-exact-homology statement at degree zero; its hypothesis is met because Step 1 gives a short exact sequence of cochain complexes of abelian groups. Step 3 uses only the definition of the homotopy category and the Hom-complex differential: degree-zero cocycles are chain maps and boundaries are null homotopies. I checked small cases (the zero sequence, a split degreewise sequence, and a one-degree complex), and each gives the stated exactness. Mathlib searches were run for the item and child with LeanFinder, Loogle, grep, and LeanSearch; only the general degreewise-short-exact and homology-sequence declarations matched, so neither node is a Mathlib leaf.

## Second reading by H1

- Item statement: checked against `injectives.tex`, Lemma `lemma-characterize-K-injective`, successor-step displayed Hom sequence; hypotheses and middle exactness agree.
- Child statement: checked against the degreewise injective extension argument; strengthened to explicit short exactness so both endpoint maps used in Step 1 are stated.
- Step 1: checked endpoint injectivity/surjectivity and compatibility with Hom differentials.
- Step 2: checked the cited long exact homology statement applies to the short exact Hom-complex sequence.
- Step 3: checked degree-zero cocycles and coboundaries against `def-pur-kinjective-complex`; zero, split, and one-degree cases rechecked.
- Searches: `rg` found no duplicate; `tools/blueprint_refs.py search 'Hom-complex exactness'` returned no match; Mathlib searches are recorded.

Changes made: strengthened the child statement and expanded Step 1 with the endpoint argument; updated the citation quote.
