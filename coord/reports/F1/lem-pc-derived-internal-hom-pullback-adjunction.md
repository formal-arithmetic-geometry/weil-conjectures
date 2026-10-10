Files written:

- `dag/nodes/sec-picard-framework/lem-pc-derived-internal-hom-pullback-adjunction.json` (statement, split; no new child nodes, Mathlib no match).
- `citations.json` (verbatim citations for all proof-step uses).

Attachments: none.

WANTED: none.

The source declaration search covered `WeilConjectures/` for the blueprint tag and the internal-Hom/pullback terminology; no sorry-free declaration states this item. The existing generic derived pullback/direct-image adjunction node supplies the counit and bifunctorial Hom bijections. The item proof follows cohomology.tex Remark 08I3, Tag 079W, and Lemma 08DJ: the first step constructs the internal-Hom comparison and its mate, the second identifies the counit composite by the tensor-internal-Hom adjunction and triangle identities, and the third applies the global-sections and pushforward comparisons to compute H^0. I checked each cited node's statement: the generic adjunction really gives Lg^* ⊣ Rg_*, the internal-Hom node really gives the derived internal-Hom functor, the H^0 node gives H^0(RHom)=Hom, and the pushforward-comparison node gives derived sections of Rg_* as sections on T. No intermediate node was created because a comparison map or its counit composite would restate a clause of this item (delivery-errors D1/D2). The proof steps explicitly mention naturality, evaluation compatibility, the two triangle identities, and the map on H^0; small cases g=id and M=O reduce to identities under the same mate calculation.

## Review by F1

I read the target node, its unit `sk-thm-picard-duality`, the ancestor `lem-sc-finite-duality`, and the relevant existing nodes `lem-pc-ringed-spaces-derived-adjoint-general`, `def-pur-derived-internal-hom`, `lem-pur-rhom-global-sections`, and `lem-pc-derived-sections-pushforward-comparison`. Step 1 uses exactly the adjunction and internal-Hom functor stated by those nodes to define the canonical map and its mate. Step 2 uses those same statements for the universal-property/Yoneda calculation and checks that the counit is the one from the cited adjunction; the triangle identities are the standard adjunction identities, while evaluation compatibility is the defining equation in the item. Step 3 uses the exact H^0(RHom) statement and the exact derived-sections-of-pushforward statement, then reads the mate under the adjunction as `phi |-> epsilon_E o Lg^* phi`. I ran the required LeanFinder, Loogle, grep, and LeanSearch searches; the first found only underived Mathlib pullback adjunctions, Loogle and grep found no derived internal-Hom theorem, and LeanSearch was unavailable. I corrected the initial citation quote for `def-pur-derived-internal-hom` to a verbatim sentence from that node. No statement or hypothesis was changed.

## Second reading by F1

- Item statement: checked against `cohomology.tex`, Remark `remark-prepare-fancy-base-change` (Tag 08I3 context), Section `section-global-RHom`, and the adjunction construction used by Tag 079W; the morphism, derived categories, counit, comparison map, composite, naturality, and H^0 description agree hypothesis by hypothesis.
- New node `lem-pc-derived-internal-hom-pullback-adjunction`: checked as a self-contained statement against the same Remark 08I3 construction and the internal-Hom adjunction conclusion used in the blueprint; all notions cite definition/dependency nodes, TeX is written once, and no proof material is embedded in the statement.
- Step 1: checked its use of `lem-pc-ringed-spaces-derived-adjoint-general` and `def-pur-derived-internal-hom`; those statements provide exactly the derived adjunction/counit and the derived internal-Hom functor needed to form the comparison and mate.
- Step 2: checked against the statement of the same adjunction and internal-Hom nodes; the evaluation map, postcomposition with the counit, naturality, and the two triangle identities are the explicit mate calculation, with no uncited theorem used.
- Step 3: checked `lem-pur-rhom-global-sections` for H^0(RHom)=Hom and `lem-pc-derived-sections-pushforward-comparison` for sections after derived pushforward; the cited adjunction node supplies the induced H^0 map `phi |-> epsilon_E o Lg^* phi`.
- Edge cases: `g = id` reduces the comparison and counit composite to identities; `M = 0` and `E = 0` give zero morphisms on both sides; for an affine field scheme the statement specializes to the ordinary derived module adjunction; the empty scheme has the zero derived categories and the same identity conclusion.
- Node audit: grep over `dag/nodes` found no existing exact derived internal-Hom pullback/direct-image statement, and the Mathlib searches recorded in `searches.jsonl` found only underived adjunctions (LeanSearch unavailable); no duplicate, elementary, or item-restating child node exists.
- Changes: none after the first review; the split already had verbatim citations, complete dependency coverage, recorded searches, and a passing preflight.
