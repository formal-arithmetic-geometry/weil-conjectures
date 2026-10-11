1. Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-functorial-injective.json`: statement split, no new nodes; Mathlib searches found no match.
- `citations.json`: citations for the existing functorial injective-embedding node.

2. Attachments: none.

3. WANTED: none; the source file is available at `/home/ubuntu/c1-stacks-review/injectives.tex`.

4. The item was unsplit and its Lean audit had no declaration. I checked the source lemma `lemma-functorial-injective` directly. Step 1 uses the existing node `lem-weil-pbc-grothendieck-functorial-injective-embedding`, whose statement supplies exactly the functor, natural monomorphism, and injective values required to define the auxiliary complex. Step 2 follows the source formulas `J^n=I(M^n)\\oplus I(M^{n+1})`, differential matrix, the map `u`, quotient `Q`, and shifted cone `C(v)[-1]`; the factorization is through the injective first summand. Step 3 uses the short exact sequence and its long exact cohomology sequence, as the source proof does, to establish the quasi-isomorphism. I checked that the conclusion includes functoriality, termwise monomorphism, quasi-isomorphism, and the injective-subobject factorization. No duplicate node was created.

## Review by K1

I read the target node, its blueprint ancestor, and the complete Stacks proof in `injectives.tex` lines 1742--1770. The only cited external statement is the existing generic functorial injective-embedding node; its wording was copied verbatim into `citations.json`. The hypotheses are exactly a Grothendieck abelian category, and each construction is functorial because the embedding is natural. I checked the small edge case `M=0`, where all constructions remain zero or injective zero objects, and checked that the cone shift has the stated degree formula. The original node had no proof; I repaired it by recording the source construction and setting `status` to `split`.

5. Nothing remains unfinished.

## Second reading by K1

- Statement checked against Stacks `injectives.tex`, Lemma `lemma-functorial-injective`: Grothendieck abelian hypothesis, functorial termwise monomorphic quasi-isomorphism, and injective subobjects agree; zero complex and field cases are valid.
- Step 1 checked against the source construction and `lem-weil-pbc-grothendieck-functorial-injective-embedding`: the functorial embedding, matrix differential, chain map, and degreewise short exact sequence are all supplied.
- Step 2 checked against the displayed cone differential in the source: the shifted cone terms, natural map, termwise monomorphism, and factorization through the injective direct summand are explicit; the summand claim is elementary.
- Step 3 checked against the source and `lem-weil-pbc-complex-ses-homology-long-exact`: the quotient is the contractible shifted identity cone, so the cited long exact sequence proves the quasi-isomorphism and naturality.
- No new nodes were created; the only external facts used are existing DAG nodes, and their statements were read verbatim for the citations.
- Changed the proof to include the cone differential and the quotient-contracting-homotopy argument, marked Step 3 non-elementary, added the long-exact node citation and dependency, and retained the recorded Mathlib searches.
