1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-derived-k-injective-restrict-open.json` — item, split; Mathlib searches found no match (LeanSearch unavailable).
- `dag/nodes/sec-picard-framework/lem-sc-derived-open-restriction-adjunction-exact.json` — statement-only child; Mathlib searches found no generic ringed-space match (LeanSearch unavailable).
- `citations.json` — verbatim statements used by both proof steps.

2. Attachments:

- `CategoryTheory.Adjunction.preservesKInjectiveComplexes` belongs to `lem-weil-pbc-right-adjoint-preserves-kinjective` (existing node; sorry-free declaration in `WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/Comp.lean:91-114`).

3. WANTED:

None.

## Not duplicates

lem-sc-derived-open-restriction-adjunction-exact vs lem-sc-derived-k-injective-restrict-open: the new node states only the exact adjunction and exactness of $j_!$, while the existing item concludes preservation of K-injective complexes.
lem-sc-derived-open-restriction-adjunction-exact vs def-weil-pbc-sets-extension-by-empty: the existing node concerns set-valued extension by the empty object, whereas the new node concerns modules over a ringed space.
lem-sc-derived-open-restriction-adjunction-exact vs lem-weil-pbc-module-extension-by-zero-adjunction: the existing node is for modules on open subschemes of schemes and includes an explicit presheaf and stalk construction; the new node is the generic ringed-space statement.
lem-sc-derived-open-restriction-adjunction-exact vs lem-weil-pbc-sheaf-directed-colimit-finite-coequalizers: the existing node is about directed colimits and finite coequalizers of sheaves, not open restriction or extension by zero.
lem-sc-derived-open-restriction-adjunction-exact vs lem-weil-pbc-sets-inverse-image-extension-by-empty-constant: the existing node concerns inverse image and extension by the empty set for set sheaves, not module sheaves or exactness.
lem-sc-derived-open-restriction-adjunction-exact vs lem-weil-pbc-sets-extension-by-empty-adjunction: the existing node states a set-sheaf adjunction with extension by the empty object, not the module extension-by-zero adjunction.
lem-sc-derived-open-restriction-adjunction-exact vs lem-weil-pbc-sheaf-basis-surjection: the existing node concerns surjectivity on a sheaf basis and does not state an open restriction adjunction.
lem-sc-derived-open-restriction-adjunction-exact vs lem-weil-pbc-module-open-restriction-injectives: the existing node is a scheme-specific result about restriction preserving injective objects and direct image preserving injectives, while the new node is the generic ringed-space exact $j_!\dashv j^{-1}$ input.
lem-sc-derived-open-restriction-adjunction-exact vs lem-sc-derived-internal-hom-restrict-open: the existing node concludes a derived internal-Hom restriction isomorphism and uses the present item; the new node is its smaller exact-adjunction prerequisite.

4. What was wrong or incomplete:

The item was unsplit and had no proof. Its imported Mathlib search list omitted the required unavailable LeanSearch record. I retained the statement and supplied the missing proof route from Stacks Tag 08BS. The proof needs the exact extension-by-zero adjunction as a separate, strictly smaller ringed-space module statement; no existing DAG node stated that generic fact, so I created `lem-sc-derived-open-restriction-adjunction-exact`. The generic K-injective preservation fact already exists as `lem-weil-pbc-right-adjoint-preserves-kinjective`, so I cited it instead of creating a duplicate.

## Review by F1

I read Stacks Cohomology Lemma 08BS and its cited 08BJ result. Tag 08BS has exactly the ringed-space and open-subspace hypotheses of the item and says restriction of a K-injective complex is K-injective because restriction has the exact left adjoint $j_!$. The new child records that adjunction and exactness for sheaves of modules, with the module category and ringed-space notions supplied by the cited definition nodes; it follows the construction and exactness references 009Z/00A7 and 01AK. Step 1 uses only the child statement, and that statement explicitly supplies both adjointness and exactness. Step 2 instantiates the existing 08BJ node with $u=j^{-1}$ and $v=j_!$; its statement explicitly concludes that applying $u$ termwise to a K-injective complex remains K-injective. I checked that both module categories are abelian through `def-weil-sheaf-of-modules-category`, and that the direction of the adjunction agrees with the generic lemma. I tested the construction on the identity open ($U=X$, where $j_!$ and restriction are identities), the empty open (both restriction and extension by zero are zero), and the zero complex. Mathlib searches were run for the item and child with LeanFinder, Loogle, grep, and unavailable LeanSearch, and their recorded results are included verbatim in the node files. A whole-DAG search found the existing generic 08BJ node and no generic ringed-space exact-adjunction node; the blueprint search found no duplicate.

5. What I could not finish:

Nothing; the dry run remains to be executed.

## Second reading by F1

- Item statement: checked against Sites Cohomology Tag 08BS (`cohomology-lemma-restrict-K-injective-to-open`), including all ringed-space, open-subspace, and K-injective hypotheses; verdict: correct.
- Step 1: checked against the child statement and Tags 00A7/01AK; the exact restriction and exact extension-by-zero adjunction are exactly the inputs used; verdict: correct after source-label repair.
- Step 2: checked against `lem-weil-pbc-right-adjoint-preserves-kinjective`; its right-adjoint orientation and exact-left-adjoint hypothesis give precisely the conclusion; verdict: correct.
- New node `lem-sc-derived-open-restriction-adjunction-exact`: checked against Sheaves Tag 00A7 and Modules Tag 01AK, including the restricted structure sheaf and exactness claims; verdict: correct after making $\mathcal O_U=\mathcal O_X|_U$ and the open immersion explicit.
- Existing-node search: `lem-weil-pbc-ringed-space-open-restriction-adjunction` is the distinct restriction $\dashv j_*$ result, so the child is not a duplicate.
- Edge cases: checked $U=X$, $U=\varnothing$, and the zero complex; all assertions reduce to identity or zero functors as expected.
- Mathlib records: verified the semantic searches are present in `searches.jsonl`, including unavailable LeanSearch results; no Mathlib leaf applies.

Changes made:

- Corrected the item source document and proof-step locations to `sites-cohomology.tex` and Tag 08BS.
- Corrected the child source to exact Tags 00A7 and 01AK and made the restricted structure sheaf explicit in its self-contained statement.
