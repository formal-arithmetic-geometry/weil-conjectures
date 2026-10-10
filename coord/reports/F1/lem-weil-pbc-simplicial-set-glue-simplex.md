# Stage 1: lem-weil-pbc-simplicial-set-glue-simplex

Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-simplicial-set-glue-simplex.json`: split the item into four steps proving the boundary inclusion and pushout universal property.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-simplicial-set-nondegenerate-decomposition.json`: one statement node, a Mathlib leaf. `SSet.exists_nonDegenerate` and the three `SSet.unique_nonDegenerate_*` declarations state existence and uniqueness of the nondegenerate decomposition.

Attachments: none. The search of `WeilConjectures/` and `Comparator/` in the slopmaster2 source checkout found no declaration matching the item or the new node.

WANTED: none. The Stacks source tree is absent from this clone but `simplicial.tex` and `tags/tags` were read from the local source copy at `/home/ubuntu/c1-stacks-review/`; `literature/LIST.md` already records the Stacks project as obtained and `tools/fetch_literature.sh` documents its regeneration.

The item statement agrees with Stacks 018R. The imported file had no proof. I kept its statement, source, chapter, unit and earlier Mathlib searches. The item is not the statement of `sk-prop-h2`, so I did not change that unit's `realized` fields. The proof uses Stacks 0166 for factorization through a missing face and 017R for the unique nondegenerate decomposition. LeanSearch returned HTTP 500 on two queries for the new leaf; Loogle, LeanFinder and the Mathlib source identified and verified its declarations. No proof is unfinished.

## Review by F1

I read Stacks `simplicial.tex` Lemma 018R (`lemma-glue-simplex`) and its proof, together with Lemma 017R (`lemma-splitting-simplicial-sets`), Lemma 0166 (`lemma-face-degeneracy`), Lemma 017S (`lemma-injective-map-simplicial-sets`) and Lemma 0177 (`lemma-simplex-map`). The source tags and labels were checked in `tags/tags`. The item's hypotheses (equal lower degrees, exactly one new simplex in degree `n`, and only degenerate new higher simplices) are precisely 018R's. Its explicit boundary as the non-surjective maps is the `(n-1)`-skeleton of `Delta[n]` used there: a non-surjective map misses a vertex and factors through its face. I checked separately that for `n=0` the boundary is empty.

Step 1 uses the definition node `def-weil-pbc-simplicial-set` for degeneracy and subcomplex stability, and `lem-weil-pbc-simplex-face-factorization` for the missing-vertex factorization of 0166. Its hypotheses are met because `n>0` in the only case that invokes the face lemma. If `x` were degenerate, its lower-degree source would be in `U`, contradicting `x` being new. Each proper face of `x` has degree `n-1` and is therefore in `U`.

Step 2 uses the new decomposition leaf, whose source is 017R and whose four Mathlib declarations I read in `Degenerate.lean` at lines 114, 217, 225 and 233. A nondegenerate ancestor of a simplex outside `U` cannot have degree below `n` by hypothesis (1), cannot have degree above `n` by (3), and must equal `x` by (2). The source's injectivity step cites 017S; the decomposition leaf gives the precise uniqueness that 017S obtains from 017R. I checked the converse carefully: a surjective degeneracy of `x` cannot fall into `U`, because an order-preserving section would then recover `x` inside `U`.

Step 3 defines the proposed extension on `U` and on each distinct new degeneracy. Its naturality check uses the boundary conclusion of step 1 and the unique representations of step 2. It covers both cases for the composite `sigma` followed by an arbitrary simplicial operator: if surjective it remains a new degeneracy; otherwise it is a boundary simplex and the compatibility of `g` and `h` supplies the required equality. Step 4 uses the same dichotomy to verify the restriction to `Delta[n]`; naturality forces any competing extension to agree on every new degeneracy. These are the degreewise bijectivity argument of 018R written as the universal property stated by the item. The cited definition node and the two leaf statements say exactly what these steps use; none of the steps relies on an uncited result in the proof of another node.

I searched all DAG nodes for 017R, 017S, 018R, their labels and the nondegenerate decomposition, and searched all blueprint nodes with `tools/blueprint_refs.py search` for simplex and splitting terms. No existing node states 017R. The face-factorization node already states 0166, so I reused it. The new node is self-contained, has only a statement, names its definition, and cites Stacks by tag and label. It has a Mathlib match with declaration names, file and verified lines. Its `blueprint.from` points to the nearest ancestor and the simplex-attachment clause; no blueprint node has the same statement.

For small cases I checked `n=0`, where a new vertex produces the coproduct; `n=1`, where the two faces of `x` may coincide but the degeneracies remain distinct by 017R; and `n=2`, where repeated faces still lie in `U` and the unique-decomposition argument does not require distinct faces. I corrected the initial JSON escaping of TeX commands before running the checks. I found no mathematical error in the item or in Stacks 018R.
