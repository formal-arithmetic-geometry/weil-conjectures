1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-koszul-regular-immersion-derived-hom.json` — statement, split proof, and blueprint metadata; status `split`.
- `dag/nodes/sec-picard-framework/lem-sc-koszul-regular-sequence-dual-complex.json` — statement-only child; Mathlib searches found no match.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.

2. Attachments: none.

3. WANTED: `literature/stacks-project/duality.tex`, Tag 0BQZ, for the local Koszul dual calculation (the repository contains the citation metadata but not the source tex file).

4. The imported item had no proof. I searched the whole DAG and blueprint for the Tag 0BQZ statement and for Koszul-dual/exterior-power variants; the only nearby result was the already existing perfectness node, which supplies the local Koszul resolution but not its dual. I therefore created one strictly smaller affine algebra statement. The item's three steps use the existing perfectness statement, the new affine dual calculation, and the existing restriction-of-derived-Hom statement. The affine child was tested on ranks zero and one: for r=0 the Koszul complex is A and both sides are B=A; for r=1 the dual two-term complex has sole cohomology B in degree 1, matching N[-1].

## Review by J1

I read the item source citation (Stacks Tag 0BQZ) and the surrounding imported nodes `lem-sc-koszul-regular-closed-immersion-perfect`, `lem-sc-derived-internal-hom-restrict-open`, and `lem-sc-smooth-proper-diagonal-koszul-dual`. Step 1 takes exactly the local bounded finite-free Koszul model stated by the perfectness node. Step 2 takes exactly the affine child's quasi-isomorphism and checks that the quotient module B and I/I^2 identify with the affine restrictions of the structure and conormal sheaves; the rank r hypothesis is the length of the local regular sequence. Step 3 uses the child's stated localization functoriality and the restriction node's canonical RHom isomorphism; these are the hypotheses needed to agree on overlaps and preserve the i_*O_Z-module action. I corrected the initial citation quote for the restriction node so it is verbatim from that node's statement. No existing node or Lean declaration states the affine Koszul dual formula, and all four required Mathlib search forms were run for both the item and the new child; LeanSearch was unavailable and recorded as such.

5. I could not read the upstream Stacks TeX because it is absent from this checkout; the report records the requested source under WANTED. The split is otherwise complete and ready for the dry run.

## Not duplicates

lem-sc-koszul-regular-sequence-dual-complex vs lem-sc-koszul-regular-immersion-derived-hom: the new node is an affine commutative-ring calculation for a chosen finite sequence and its Koszul complex, while the existing item is the global scheme-level derived sheaf Hom formula for a closed immersion and includes localization and gluing.

## Second reading by J1

- Item statement: checked against Stacks `duality.tex`, Tag 0BQZ (`lemma-regular-immersion-ext`), and the cited definition nodes; verdict: scheme-level specialization is coherent and the locally constant rank hypothesis matches the downstream use.
- Step 1: checked against `lem-sc-koszul-regular-closed-immersion-perfect`; verdict: the affine Koszul model and finite-free terms are exactly supplied.
- Step 2: checked against the repaired affine child and the affine identifications of `I/I^2`, `C_i`, and `N_i`; verdict: valid after expressing the quasi-isomorphism in `D(A)` and restricting scalars from `B`.
- Step 3: checked against the child's localization clause and `lem-sc-derived-internal-hom-restrict-open`; verdict: localization and module compatibility justify gluing.
- New node `lem-sc-koszul-regular-sequence-dual-complex`: checked on `r=0`, `r=1`, and `A=\\mathbb Z, I=(2)`; verdict: repaired a false strict `B`-module-complex claim to the correct `D(A)` formulation.

Changes: repaired the affine child's module-category formulation, updated Step 2 and the verbatim citations, and recorded the counterexample motivating the repair.
