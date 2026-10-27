# Q36 — lem-sfb-hypercover-derived-unit-chain-squares

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-hypercover-derived-unit-chain-squares.json`: statement, split into ten explicit steps; no Mathlib match for the whole statement.
- `citations.json`: verbatim statement quotations for all 33 step/dependency pairs.
- No new DAG nodes and no new Mathlib leaves. `searches.jsonl` retains the searches executed by the required search command; the inherited item's earlier searches remain unchanged.

## Attachments

None. Searching the live `lean/WeilConjectures/` by blueprint tag and by hypercover/unit/chain terminology found no declaration of the complete item. The project has truncated hypercover and derived-functor infrastructure, not this combined statement. No Lean was written or compiled.

## WANTED

None.

## Problems and corrections

The statement is retained without weakening or added hypotheses. The original node had no proof; its source includes a hypercover descent lemma, but this item's chain identities do not require descent or acyclicity of section rows. Those hypotheses are deliberately not used. The split does not cite the parent `lem-sfb-acyclic-hypercover-pullback-normalization`, which already depends on this item.

The ordinary coefficient action is transported along the specified ring isomorphism, and all total complexes are compared as complexes of abelian groups after restriction of scalars. The derived adjunction unit is distinguished from the right-derived-functor comparison transformation (called gamma in step 4).

The inherited blueprint has null `from.node`; the ancestor command also returns null. I retained its place and via list rather than inserting an unrelated imported node. Whole-blueprint searches for derived adjunction, K-injectivity and chain squares found generic tools but no blueprint statement of this item. There is no change to the chapter or unit route, or to any maintained field.

## Not duplicates

No new nodes. In particular, the generic precomposition bijection is already `lem-sp-kinjective-comparison-principle`, bounded-below injectivity is already `lem-weil-pbc-bounded-below-injectives-kinjective`, the normalized transpose formula is already `lem-sfb-resolving-derived-adjunction-normalization`, and identity-resolution composition normalization is already `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`. The new split cites them instead of introducing hypercover-flavoured special cases.

## Review by Q36

I read the current item and its inherited provenance, its chapter and unit records, the worker and stage-1 rules, the three route levels in SETUP, GOAL, and delivery-errors B–E. I read Stacks `proetale.tex`, label `lemma-compute-cohomology` (Tag 09A2), including both resolution/total arguments; `derived.tex`, labels `lemma-K-injective`, `lemma-bounded-below-injectives-K-injective`, `lemma-adjoint-preserve-K-injectives`, `lemma-pre-derived-adjoint-functors-general`, `lemma-pre-derived-adjoint-functors`, and `lemma-derived-adjoint-functors`; and `sites-cohomology.tex`, label `lemma-derived-pushforward-composition` (Tag 0D6E). The extra chain squares are agent calculations from those constructions, and proof_origin therefore says agent. There are no new-node sources to review. No SGA source is used.

For step 1 I opened the bounded-below injectivity criterion, exact-functor factorization, precomposition principle, and homotopy definition. The comparison principle explicitly gives a bijection on homotopy classes into any K-injective target; thus it applies with source map h* i even though h* I need not have injective terms. The bounded-below hypothesis is supplied for both I and J, and exactness is an assumption of the item. This supplies existence as well as uniqueness of b. Step 2 uses the actual Hom adjunction on the homotopy category, whose statement was read in full, to give the short acyclic-source proof of K-injectivity of h_* J. This is a two-line application, not a new lemma. Step 3 uses that same node's assertion that the termwise unit is a chain map and additive functors preserve homotopies; the homotopy h_* s composed with eta_E is written explicitly.

For step 4 I checked the statement of the normalized resolving-class adjunction node: it explicitly fixes the transpose by the ordinary transpose followed by the right-derived comparison, not merely existence of an adjoint. The class of all complexes is allowed because exact h* preserves quasi-isomorphisms; the universal right-derived pair and comparison on K-injectives are precisely those of def-sfb-right-derived-functor, and the actual module adjunction and exactness are provided by def-weil-pbc-proetale-operations. Applying the formula to j gives the actual unit after inverting Rh_*(Qj), as written. Step 5 uses the latter right-derived definition to compute maps on the two K-injective representatives. I opened the ringed-composition node: unlike an unspecified composition isomorphism, it explicitly says its value is g_* j on a resolution of f_* I. Choosing the identity resolution of h_* J therefore makes its sections comparison the identity. The structural map here is to the point with ring Z, so the coefficient rings need not be constant. The direct-image definition explicitly evaluates at the base-changed object, yielding Gamma_X h_* J = Gamma_X' J.

For steps 6 and 7 I read the statements of the pro-etale inverse-image and operations definitions, the simplicial-object definition, the signed-total definition and the actual restriction augmentation definition. I use the module unit followed by restriction along V_p to X' times_X U_p. Naturality of these specified maps gives the coface equality, coefficient equality and augmentation equality; no claim about a map between arbitrary site objects being cartesian occurs. Both augmentation composites have only the (0,q) component, and I wrote the equality on an arbitrary section. This checks the strict square rather than inferring it from a cohomology identification.

For step 8 the cited homotopy definition gives b h* i - j = d s + s d. I checked the total sign on each bidegree: the horizontal terms have opposite signs and the vertical signs multiply to +1. This proves the coefficient square with exactly the homotopy in the item. Step 9 is direct naturality of section restriction, checked against the same definitions, for both a coefficient chain map and the two refinement routes. Step 10 uses the statement of the ordinary comparison definition: A is the mate of the explicitly prescribed fibre-product pasting B, so the displayed equation for the composite units is its defining equation. Evaluating and restricting that equation gives the composition equality; the composite ring isomorphism is the one in def-sfb-proetale-composite-coefficients, whose full statement I also read. The identity case uses the identity pasting and its mate.

I tested the calculations for E=0, a complex concentrated in one degree, the identity scheme/simplicial map, and the constant final-object augmented diagram. For the homotopy sign I checked p=0 and p=1 separately; omitting (-1)^p would already fail cancellation between those columns. Negative coefficient degrees cause no issue because a strict common lower bound makes every total degree finite. In particular there is no unjustified spectral sequence, sectionwise quasi-isomorphism or claim that the restriction map itself is a quasi-isomorphism. All non-elementary inputs are cited statements; the remaining steps are explicit identities from definitions. Every step is shorter than 2000 characters.

The general homological tools from other units are declared individually in split_report.tool_uses with their purpose. No new nodes restate clauses, no duplicates are introduced, and no statement dispute was found. Search results were read: LeanSearch's derived-unit factorization is relevant generic infrastructure (its Mathlib source was read), LeanFinder's injective-resolution naturalities and Dold–Kan naturalities do not supply the combined theorem, and the grep hits concern truncated hypercover homotopies. A second semantic phrasing was run before concluding no full match.

## Unfinished work

None within the one-level split. Existing dependency nodes retain their own status and are not edited by this delivery. Server validation and delivery are recorded by the required delivery command.
