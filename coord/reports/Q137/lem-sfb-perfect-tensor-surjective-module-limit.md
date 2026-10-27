# Stage-1 delivery: lem-sfb-perfect-tensor-surjective-module-limit

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-perfect-tensor-surjective-module-limit.json: statement split into five proof steps; no new nodes, no Mathlib leaves. Statement and inherited metadata preserved.
- citations.json: every proof-step citation with the verbatim statement of its node.
- report.md: this report.

Mathlib verdict: no match. The five logged searches in searches.jsonl used two LeanFinder phrasings, Loogle, Mathlib grep and LeanSearch. The hits concern condensed internal projectivity, adic completion with extra hypotheses, Tor, exact functors, direct limits, or monoid perfection. None states the item. Previous inherited searches were read and retained. Searches of lean/WeilConjectures by the exact blueprint tag and by derived-limit/tensor concepts found no attachment for the item. The existing bounded-flat K-flat declaration proves a dependency only.

## Attachments

None.

## Wanted literature

None. All required Stacks sources are present.

## Corrections and scope

The imported statement is correct as written. In particular it expressly uses strict towers and the resolution-derived inverse limit, so it avoids the noncanonical-cone problem explained by def-weil-derived-limit. Its seed proof was empty. I supplied the argument without changing the statement. The existing blueprint.from.node is null and the ancestor command returns None; its long inherited from.place and via chain identify the supporting occurrence in the direct-image/deformation route. I preserved them rather than inventing a blueprint ancestor.

The current latest blueprint direct-image proof (3), in sec-six-functors-basics/sk-thm-sf-ctf-stability, was read alongside its DAG unit and chapter. The inherited supporting source is spaces-perfect.tex, Tag 0D3F, lemma-pullback-and-limits, final displayed equality; that proof invokes more-algebra.tex Tag 0D2L. The split concerns exactly this ordinary ring-module input and replaces none of the geometric unit route. This is not the unit's key node, so no unit realization record is changed.

## Not duplicates

No new nodes. Existing lem-trf-finite-presentation-tensor-products, lem-pc-module-bounded-flat-kflat, lem-weil-pbc-surjective-module-complex-tower-limit and the projective/flat/exactness nodes are reused. The sheaf/adic-completion nodes found in the searches have different coefficient objects and additional hypotheses; no special-case duplicate was created.

## Review by Q137

I read Stacks more-algebra.tex, lemma-pseudo-coherent-tensor-limit (0D2L), its input lemma-pseudo-coherent-tensor (0CYB), lemma-derived-tor-quasi-isomorphism (064K), lemma-compute-Rlim-modules (091D), and the following distinguished-triangle lemma (0CQD). I also read the preceding abelian-group proof of the Roos calculation (07KW). In algebra.tex I read lemma-finite-projective (00NX), proposition-fp-tensor (059K), lemma-flat (00HD), lemma-tensor-product-exact (00DF), and the explicit projective-implies-flat sentence in the proof of lemma-local-artinian-characterize-flat (051G). The last sentence is general and does not use that lemma's local Artinian hypotheses. No new node requires a source check.

Step 1 uses the perfect definition for the bounded projective representative, the projective-flat statement for its terms, the bounded-above-flat K-flat statement for the complex, and the module K-flat definition's explicit quasi-isomorphism criterion for replacing a projective resolution of a module by that module. I opened each cited node. These statements apply to ordinary modules over an arbitrary commutative ring, with no Noetherian or finite-cohomology hypothesis. Bounded implies bounded above, and derived tensor is thus computed simultaneously by one P.

Step 2 uses the finite-projective-finitely-presented statement to meet exactly the hypothesis of the canonical tensor/product bijection, and flat-tensor-exact for the sequence 0 to N to the product to the product. All three cited statements were opened; none is being cited for a stronger assertion. The product statement explicitly supplies its pure-tensor formula. This formula intertwines the two one-minus-transition endomorphisms. Taking the kernel proves tensor commutes with this particular inverse limit and yields an actual chain isomorphism, not merely isomorphisms on separate cohomology groups. No surjectivity of 1-s or inverse-limit exactness is used in this step.

Step 3 cites tensor-right-exact for surjectivity of each tensor transition and the existing degreewise-surjective module-complex tower lemma for the projection-normalized Roos triangle. I checked the latter's statement, not its proof: it allows varying commutative rings, so a constant ring tower is a valid specialization; its limit is canonically A and each transition is A-linear. Its assertion is a derived-limit triangle with the actual projection maps. I do not take functorial cone choices or naturality in strict maps from this statement.

Step 4 gives that remaining map explicitly in the strict shifted-cone model. It cites the abstract-derived-category definition for the cone differential, shifts and localization at quasi-isomorphisms; all other work in this step is a direct coordinate argument. Surjectivity of 1-s is proved recursively using precisely the surjective transitions, not a claim that limit preserves epimorphisms. Both surjectivity and injectivity on cohomology of j are proved with the displayed signs. The recursive lifts are only witnesses in that proof; the canonical map j itself makes no choices. The earlier triangle lemma already supplies the derived-limit interpretation. This is a short explicit kernel/cone calculation, not a new theorem being hidden behind a definition citation.

Step 5 verifies naturality by writing the two composites on pure tensors and on both Roos coordinates. The only non-elementary additional fact is the existing bounded-projective derived-morphism representative lemma, whose statement I opened: it is a bijection from homotopy-category maps to derived-category maps out of P. Its bounded-above and projective hypotheses hold. The signed Roos homotopy (-hy,hx) was checked against d(y,x)=(-dy-vx,dx). Consequently the representative argument really descends and supplies naturality in the perfect object, as well as the explicit requested naturality in strict towers. No arbitrary triangulated-cone uniqueness is used.

All off-unit statement tools used in the five steps are declared in split_report.tool_uses, with their ordinary algebraic purpose. They supply generic module tools rather than alter a unit's geometric route. Every citation has a verbatim quote in citations.json. No step exceeds 2000 characters; the longest is about 1050. I checked the delivery-errors B--E cases: no new unsplit proof nodes, no restatement of an item clause as a lemma, no uncited non-elementary fact, no source tag substituted for a node, no use of a cited node's internal proof, and no dependency on a node above this item.

Small cases: the zero ring, zero perfect complex, zero modules and constant identity tower all give the stated identity or zero comparison. A shifted finite-projective module uses exactly the same kernel argument in its sole degree. Arbitrary nonflat N_n are allowed because P, not N_n, resolves the tensor. The differential may be nonzero; commutation with it is checked componentwise. Surjectivity is used degreewise, never on cohomology. Without it the recursive proof of surjectivity of 1-s and the termwise-derived-limit step would fail, which is why that hypothesis is retained. I also checked that no illicit finite-product argument replaces the required infinite product comparison.

## Unfinished work

None in stage 1. Existing dependency nodes retain their own status. No Lean was written or compiled; no repository, launcher or literature file was changed.
