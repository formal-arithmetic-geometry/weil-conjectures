# Worker report: lem-trf-total-site-component-restriction

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-total-site-component-restriction.json`: item split into five proof steps; no new nodes; Mathlib searches found no exact result.
- `citations.json`: verbatim quotes for every cited node in every proof step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, title, component-restriction terminology, and the Stacks labels; no sorry-free project declaration states this item.

## WANTED

None.

## What was wrong or corrected

The imported item was unsplit and had no proof. I retained its statement and hypotheses, including coherent (rather than strict) simplicial composition isomorphisms and the unrestricted K-injective conclusion. I did not create a supporting node: the proof is the one-level expansion of Tags 09WF, 09WG and 09WH, while the existing generic injective and K-injective preservation nodes provide the only reusable categorical inputs. The existing derived-components node depends on this item and therefore was not cited, avoiding a cycle.

## Review by Q23

I read the item and its source in `literature/stacks-project/spaces-simplicial.tex`, including the system description before Tag 09WF, the complete proofs of Tag 09WG (`lemma-restriction-to-components-site`) and Tag 09WH (`lemma-restriction-injective-to-component-site`), and the relevant site-morphism definitions. I also read the unit and chapter records, the statements of `def-weil-pbc-sites-and-cohomology` and `def-weil-pbc-simplicial-object`, the Mathlib-leaf statement `lem-exc-rg-right-adjoint-preserves-injectives`, and the generic K-injective theorem `lem-weil-pbc-right-adjoint-preserves-kinjective`.

Step 1 uses the two definition nodes only to instantiate the simplicial-site setting; Tag 09WF supplies the precise compatible-family description and the fact that componentwise isomorphisms detect an isomorphism. Step 2 follows Tag 09WG: the degree-n inclusion preserves coverings and fibre products, and the displayed direct-sum system has transition maps from the coherent composition isomorphisms. I checked the direction of every index (`f_φ : C_n → C_m` for `φ : [m] → [n]`) and the adjunction maps component by component. Step 3 uses the exactness clause in the site-morphism definition for each inverse image and the componentwise abelian-sheaf description; direct sums of exact inverse images are exact, evaluation is exact, and componentwise detection gives conservativity. Step 4 applies the cited injective-preservation statement with the exact left adjoint `g_{n!}` and right adjoint `r_n`; its mono-preservation hypothesis follows from Step 3. Step 5 applies the cited generic right-adjoint K-injective theorem with `u=r_n`, `v=g_{n!}`; its hypotheses are the abelian categories, additive adjunction and exactness established in the preceding steps, and it covers arbitrary K-injective complexes, hence the bounded-below resolutions in Tag 09WH.

I checked small cases: for a constant one-degree simplicial site, the sole summand is the identity and `g_{n!}` is the identity; for a two-degree diagram, the formula has one summand per order-preserving map and the transition maps compose as stated. The four required Mathlib searches were run for this item and recorded in the node; they returned only general sheaf/complex declarations and no total simplicial-site result. No Lean files, compiler, Lake, or build tools were used.
