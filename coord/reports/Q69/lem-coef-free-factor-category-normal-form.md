# Stage 1 report: lem-coef-free-factor-category-normal-form

Files written:

- `dag/nodes/sec-six-functors/lem-coef-free-factor-category-normal-form.json` — statement, split proof; no new nodes; Mathlib searches found no match.
- `citations.json` — verbatim citations for every node used by every proof step.

Attachments: none. No finished declaration with this blueprint tag or exact statement was found in `WeilConjectures/` of either read-only source checkout.

WANTED: Dwyer--Kan, *Calculating simplicial localizations*, Proposition 3.2, printed pp. 20--21 (the PDF is cited by URL in the node and was read online; it is not archived in `literature/`).

No new node was created. The existing `def-nagata-category` Mathlib leaf supplies the category axioms used in the construction, and `lem-coef-fixed-object-simplicial-free-calculus` supplies the fixed-object coproduct convention. The item's imported statement is retained unchanged.

## Review by Q69

I read the complete item node, the chapter record, the fixed-object unit context, and the Dwyer--Kan source location cited by the item and its proof. I searched the whole DAG and blueprint for reduced-word, alternating-factor, and category-coproduct statements; the only nearby results were the already existing fixed-object simplicial coproduct calculus, the hammock pushout/comparison nodes that cite this item, and unrelated nerve or monoid-word results. The source checkout contains no declaration tagged with this item, and no sorry-free exact declaration exists to attach.

Step 1 uses only the category axioms in `def-nagata-category`: identities and composition make tagged composable lists and the elementary reductions meaningful. I checked that each reduction preserves endpoints and strictly lowers list length, including identity composites. Step 2 uses the same category axioms for associativity and units inside each factor; the recursively defined normalizer is unchanged by each elementary reduction, so termination gives a unique reduced word. I explicitly checked the edge cases of an empty list, a one-letter list, adjacent letters whose composite is an identity, loops, and invertible nonidentity arrows; invertibility alone never triggers deletion.

Step 3 uses the existing fixed-object coproduct convention exactly where it is cited: the coproduct is taken on the common object set and amalgamates the identity category. The reduced-word category has associative composition because normalizing a concatenation is invariant under prior normalization; its factor maps are faithful, and evaluation of reduced words proves the universal property. Step 4 uses the same two statements to verify functoriality: apply the factor functors letterwise and normalize, allowing image letters to become identities or adjacent tags to merge. I checked empty object sets and maps that identify objects. The `citations.json` quotes are copied verbatim from the two cited node statements, and `proof_deps` is exactly their union.

I corrected the imported node's missing proof by expanding the normal-form and universal-property arguments into four complete steps. No statement, hypothesis, dependency, or blueprint ancestry was changed, and no extra node was introduced because every auxiliary fact is a direct construction from the two existing statements and category definitions.

## Second reading by Q69

- Statement: checked the fixed-object category coproduct, alternating reduced-word, termination, uniqueness, functoriality, empty-object, loop, identity-composite, and invertible-arrow clauses against Dwyer--Kan, *Calculating simplicial localizations*, Proposition 3.2, printed pp.20--21 (and its use in §5.8(i), p.25); the source's free-factor instance is the motivating case, while the arbitrary-factor formulation is required by the consuming hammock-pushout node and follows by the same category relations; verdict: correct.
- Step 1: checked tagged composable lists, endpoint preservation, identity deletion, same-factor composition, and strict length decrease against the category axioms in `def-nagata-category`; verdict: complete and correctly scoped.
- Step 2: checked the recursive normalizer, associativity/unit invariance, confluence, uniqueness, and the explicit treatment of invertible nonidentity arrows against the factor category laws; verdict: complete, with no hidden cancellation assumption.
- Step 3: checked the reduced-word category's associativity, units, faithful factor maps, evaluation, uniqueness, and identification with the fixed-object coproduct against `def-nagata-category` and the coproduct convention in `lem-coef-fixed-object-simplicial-free-calculus`; verdict: cited statements provide the required universal-property input.
- Step 4: checked image-letter identities, merged tags, preservation of one-step reductions and composition, empty object sets, loops, and identity composites against the same two cited statements; verdict: complete and functorial.
- New nodes: none; the only auxiliary notions are the category axioms and fixed-object coproduct convention already carried by the two cited nodes, so no B1--B7 node audit applies.
- Citations: verified every `citations.json` quote is verbatim in its cited statement and that `proof_deps` is exactly the union of step uses; verdict: correct.
- Mathlib/Lean search: ran independent LeanFinder (`Coproduct of categories sharing objects morphisms alternating reduced composites`), Loogle (`CategoryTheory.FreeProduct`), and Mathlib grep (`free product|alternating word|coproduct.*category` in `CategoryTheory`); all returned no exact multi-object normal-form declaration, so the item remains unsplit.
- Repair: corrected the copied `created.item` metadata to `lem-coef-free-factor-category-normal-form`; no mathematical statement or proof step required alteration.
