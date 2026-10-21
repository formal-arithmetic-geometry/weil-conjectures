## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-additive-localization-descent.json`: split the statement into six steps. The statement and its statement dependencies are unchanged. No exact Mathlib match: the searched localization criterion requires a calculus of fractions, and the searched precomposition criterion requires fullness. Neither is assumed here.
- No new nodes and no new Mathlib leaves. The existing `lem-sfb-products-zero-additive` is the final criterion.
- `citations.json`: one verbatim statement quotation for each cited node at each proof step.
- `searches.jsonl`: actual search-command log. The item's inherited searches are retained; five new searches (two LeanFinder phrasings, Loogle, grep, LeanSearch) are appended in `mathlib_searches`.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, localization/additivity terminology, and relevant declaration names. The derived-functor applications found are special cases with stronger hypotheses, rather than declarations stating this item.

## WANTED

None. All sources used were available locally.

## Findings and corrections

No statement dispute. No hypotheses or conclusions have changed. The imported item had no proof. Its source field mentions Stacks 04VG, which treats a left multiplicative system and is not itself an unrestricted additivity theorem. That maintainer-owned source field is retained, but the actual proof source and every step now identify `homology.tex`: 00ZY (`definition-preadditive`), 0103 (`remark-direct-sum`), 0104 (`definition-additive-category`), 0105 (`lemma-additive-additive`), and 0DLP (`lemma-additive-functor`). The proof is marked agent-written: the essential-surjectivity argument is supplied here rather than attributed verbatim to Stacks. It needs only the explicit essential surjectivity and the additivity of q and Gq. The localization universal property remains a statement dependency, defining a hypothesis, but is not a proof dependency.

The current blueprint's `def-weil-rationalization-karoubi` final paragraph defines integral scalar extension by completed derived tensor product, then rationalization. This item serves additivity of its descended integral functor as recorded by its two intervening created nodes. It is not the unit's key node, so no unit record is changed. The proof does not change the unit or chapter route, and uses no SGA source.

## Unfinished work

None in this stage-1 split. No Lean was written and no compiler, Lake, or build was run. Remote preflight and push results are recorded below when available.

## Not duplicates

No nodes are created. Whole-DAG searches by additive terminology, essential surjectivity, and biproducts, and whole-blueprint searches for `additive`, `biproduct`, and `additivity descends`, identified the existing `lem-sfb-products-zero-additive`, which is cited instead of recreated. The coproduct-preservation leaf is unnecessary because the specific binary-product calculation is written out. The blueprint's abelian-category left-exact definition is not used as a theorem about the general additive categories of this item.

## Review by O2

I read the current item and all five nodes cited by its steps, as well as its localization-universal-property statement dependency. I read Stacks `homology.tex` at the additive-functor definition, the direct-sum relations and their product/coproduct proof, and the product criterion. I read 04VG in `categories.tex` to check its narrower scope, and read the current main-20261015 rationalization blueprint paragraph that is this item's ancestor. There are no new-node sources to check.

For step 1, `def-weil-pbc-additive-functor` states exactly additivity on each morphism group, and `def-weil-preadditive-category` supplies bilinearity of composition. Naturality gives H(f)=e_Y^{-1} U(f) e_X. Expanding this formula proves H(f+g)=H(f)+H(g), and cancellation at 0 proves zero preservation without invoking a separate theorem on natural isomorphisms. The direction of e and the source/target of each component agree with the formula.

For step 2, `def-weil-additive-category` states all five biproduct identities, including the sum-of-projections identity. The additive-functor definition permits applying q and H to that sum. The step writes out the diagonal, off-diagonal, and sum identities separately; it never assumes G is additive when applying G to arbitrary sums. The sum in E is justified by H's additivity from step 1, not by the desired conclusion.

For step 3, the cited preadditive definition gives precisely the two bilinear distributivity identities. Substitution of the relations from step 2 proves the displayed product lift and its uniqueness in both D and E. This is a calculation with the biproduct equations, not an uncited product-preservation theorem. The cone in E is literally the G-image of the chosen cone in D, since H=Gq.

For step 4, the item explicitly supplies isomorphisms qX to A_1 and qY to A_2; no fullness or morphism lifting is assumed. Composing a proposed pair with their inverses gives the required product lift. A functor maps an inverse pair to an inverse pair by functoriality. To cover every product cone, rather than just one chosen cone, the step constructs the two leg-preserving comparison maps by the product universal properties; uniqueness makes their composites identities, and applying G transfers this cone isomorphism. These are elementary universal-property arguments written out in the step, so no new lemma is hidden behind the word "transport".

For step 5, the preadditive definition gives composition with zero equal to zero, by bilinearity and additive cancellation. Since q sends zero to zero, G(0) on q-images equals H(0), already proved zero. Writing the general zero as b composed with zero composed with a^{-1} checks all objects of D. This does not require an objectwise identification of D with C or a special choice of zero object.

For step 6, I opened `lem-sfb-products-zero-additive`: it states exactly that a functor between preadditive categories with binary products in the source, preserving binary products and zero morphisms, is additive. The additive-category definition supplies the binary products; steps 4 and 5 supply the two preservation hypotheses. I also read its Mathlib declaration `CategoryTheory.Functor.additive_of_preserves_binary_products`, `Mathlib/CategoryTheory/Preadditive/AdditiveFunctor.lean:234–239`. Thus the node gives the exact conclusion under the hypotheses established here. This Mathlib leaf is an allowed generic tool across units, so it needs no replacement of a unit's proof route.

I checked B1–B10: no new statements, notions, or duplicates; the unchanged item introduces every object; all recorded additional searches really ran; exact Mathlib lines were inspected; blueprint references and existing metadata are retained. I checked C1–C8: the only non-elementary fact used is the cited existing product criterion; every quote in citations.json is taken directly from the corresponding statement; all other steps are the explicit short calculations described above. I checked D1–D5: no clause has been moved into a new node, there is no self-citation or deferred circular identification, and the argument itself is supplied. I checked E1–E7: no left/right fraction hypotheses, fullness, abelianness, or smallness assumption enters the proof; natural-isomorphism and object-isomorphism directions were checked.

For edge cases I checked X=Y=0, either summand zero, and zero categories: the same equations give product lifts and zero images. The argument also covers q being the identity and W consisting of identities, and it covers localizations that identify nonzero maps with zero. No cancellation of q on Hom sets, faithfulness, or fullness is used. Every proof step is shorter than 2000 characters; there is no long inline comparison lemma to extract.
