# Stage-1 report: lem-sfb-semilinear-galois-alteration-domination

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-galois-alteration-domination.json`: statement, split; no exact Mathlib match. Mathematical statement unchanged. Fifteen proof steps, all under 1100 characters, using existing DAG nodes only.
- `citations.json`: one verbatim statement quotation for every node cited in every proof step.
- `searches.jsonl`: the five actual search records produced by msearch.py in this sandbox. The item's inherited searches are also retained in its JSON.
- `report.md`: this report and self-review.

New nodes: 0. New Mathlib leaves: 0. No Lean files written or compiler/build tools run. No repository or launcher files edited; all authored files are in the assigned sandbox.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and the Galois-alteration, domination and semilinear concepts. No project declaration found gives this theorem, and the field/rational-map/normalization Mathlib results do not give it in one specialization. The item had no finished Lean attachment to retain.

## WANTED

WANTED: A. J. de Jong, *Families of curves and alterations* (1997), §§3.2, 3.8 and Situation 5.3, pp.605,608,613, local PDF for lem-sfb-semilinear-galois-alteration-domination. The publisher PDF at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf was read online; no document was downloaded or written into the repository.

## Problems found and changes

The item was a statement-only prerequisite. Its source described a general semilinear form of de Jong's construction, rather than supplying a proof of that form. I supplied the explicit argument, recording `proof_origin.by = agent`. It combines fixed-field normal closure with the conjugate-product graph construction, and does not invoke stable modification, smooth purity, or any SGA source.

The action is allowed to be nonfaithful. Replacing H by its faithful image everywhere would lose the required surjection to H. Only the application of the fixed-field theorem uses the image; the constructed group is the full group of pairs `(h, sigma)` over the original H. The arbitrary inseparable case requires a normal extension, not an unjustified separable Galois closure. The separately chosen Galois closure in the separable case supplies the strengthened clause.

The finite-over-projective node is deliberately used only with affine base Spec k: its statement gives local projectivity over a general base, not a global projective-space embedding. I give the latter for W -> S by an explicit closed graph. The old source of the existing finite-normalization node cites 0359, which labels the Nagata section; the new proof's source pointer uses 0AVK (lemma-nagata-normalization-finite-general) instead. The cited existing node's statement is the finite-type-over-a-field result actually needed; it is not being used outside those hypotheses.

The inherited nearest blueprint ancestor is null, as `tools/blueprint_refs.py ancestor` reports. I retained it and its existing via list; `from.place` already specifies the exact alteration-reduction use through det-thm-sf-ctf-stability-direct-images proof (3), and `split_report.blueprint` now explains the expansion. The current main-20261015 direct-image proof and its unit section were read. The stale unit record's chapter assignment is inherited and not changed. This is not the unit's key statement, so no realization fields are authored.

## Searches and reuse

The whole-DAG search covered normal closure, normal intermediate isomorphisms, fixed fields, normalization in a finite extension, Chow, graph closure, projectivity, and finite-over-dense-open results. The blueprint search covered Galois alteration, semilinear, Chow, fixed field, normalization and graph. Existing normal-closure and automorphism-lifting nodes replace proposed field prerequisites; existing normalization, integral Chow, reduced-closed-structure and projectivity nodes supply the geometric ones. No new statement-only node or duplicate is introduced.

The five new msearch.py calls were the item-specific leanfinder query about normal projective equivariant Galois alteration domination; Loogle `"AlgebraicGeometry", "IsGalois"`; grep `(Galois|galois).*(alteration|modification)|equivariant.*(normaliz|dominat)`; LeanSearch about compatibility with a group acting on the base and its field; and a second leanfinder phrasing about closing generic graphs in conjugate projective models. All five services returned successfully. Loogle and grep returned no hits. I read the semantic hits: IsGaloisGroup fraction-field results, finite-group fixed-field results, relative normalization, rational maps from function fields, and projective elliptic-curve models. They are ingredients or concern different objects; none states this theorem or specializes to all its clauses in one line. No unavailable search is labelled as a negative result and no unrun query was recorded.

## Not duplicates

No new nodes were created. In particular the item cites, rather than duplicates, lem-wf-finite-field-action-fixed-degree, lem-weil-pbc-finite-extension-in-finite-normal-extension, lem-sfb-normal-intermediate-isomorphism-lifts, lem-fin-normalization-extension-finite, lem-weil-pbc-integral-chow-relatively-ample, and lem-weil-pbc-reduced-induced-closed-subscheme.

## Unfinished work

No part of the requested stage-1 split is left unfinished. Existing unsplit prerequisites remain independent DAG work; no proof or status of those nodes was changed. The requested dry run and direct push are performed after this report is written.

## Review by NN

I reviewed the unchanged statement against ILO X Theorem 3.4 Step 4 (printed pp.160–161) and Remark 3.3.2 (printed p.158), and read de Jong's §§3.2 and 3.8 and Situation 5.3 online. The first source permits enlarging an alteration to a normal projective Galois one; de Jong supplies the compatible-lift group and averaging idea. The nonseparable convention permits purely inseparable invariant fields. This proof spells out the general semilinear variant as an agent argument instead of claiming that a source states every extra clause literally.

I opened the statement of every dependency actually used, not just its title or its proof. `citations.json` contains those exact statements, indexed by proof step. I checked the argument as follows.

1. The faithful finite action theorem says finite Galois over the fixed field for a faithful group. I apply it to the image H0, whose fixed field equals K^H, and retain H itself for the eventual lift group. The finite-degree tower argument is the displayed product-of-bases argument. K=k(S) and L=k(T) exist since both schemes are integral.

2. The finite-normal-closure node accepts an arbitrary finite extension, including an inseparable one. The optional finite-Galois-receiving node accepts separable extensions, so I first apply lem-zl-separable-permanence to F subset K subset L. Normal-over-intermediate gives normality of M/K in both cases. These are exactly the cited statements. I read Stacks fields.tex 09DT, 09HB and 0EXM for this choice.

3. The existing normal-intermediate-isomorphism-lifts node permits the two intermediate fields to be K itself; no separability assumption is required. A_h fixes F, as needed. The finite-embeddings node applies to M/F and target M and proves finiteness of Aut_F(M). The defining pair condition proves closure under products and inverses explicitly. For h=1 it identifies the kernel with all Aut_K(M), not with a potentially smaller group. Stacks 0BME and 09H8 are the relevant sources.

4. Normalization-in-residue-field-extension supplies both normal integrality and the actual residue field M at the generic point, not merely an integral map. Taking the point to be the generic point of S matches its finite residue extension hypothesis. Finiteness uses the existing finite-normalization node with S finite type over a field and M/K finite. Finite-over-projective applies to B -> S -> Spec k with affine Noetherian base and the projective S supplied by the item. H-projectivity plus properness gives finite type. I read the 0AVK normalization statement and varieties.tex 0BXR/0GK4. This avoids silently assuming that a generic point is a finite-type k-scheme.

5. The definition of normalization states the affine integral-closure construction and its localization compatibility. Applying an automorphism to a monic equation proves preservation of each ring. The inverse gives equality, and the same ring formulas give compatibility on overlaps and group laws. This is a few-line construction from that cited definition, not a theorem about an uncited quotient.

6. Integral Chow explicitly gives an integral Y and a dense isomorphism open, unlike a general Chow surjection alone. T is proper over k by proper composition, hence separated and finite type. The immersion into projective space is proper by proper-over-separated and then closed by proper-immersion-closed; I checked the separatedness hypothesis for projective space. T_K is a finite integral K-scheme and so Spec L. Its point lies in the Chow isomorphism open, so Y_K remains Spec L. I read coherent.tex 0201, morphisms.tex 01W6 and schemes.tex 01IQ. No action on T or on Y has been assumed.

7. Each Y_j uses its own scalar twist, so h_j v is a k-map for that twisted structure. Projective base change gives the twisted embeddings. Products of closed immersions and Segre give the absolute projective embedding of the product. Since S is separated over k, the equalities defining the fibre product are pullbacks of closed diagonals. The cited proper-fp-permanence statement includes closed-immersion base change; closed-immersion-products includes composition. Neither P nor its factors are assumed geometrically integral. This step is a finite iteration of those statements, not an uncited projective-composition theorem over a general base.

8. I verified the indices: the factor j moves to gj, and f_j=f a_(j inverse), so f_(gj) a_g=f_j. This is the reason the generic tuple is fixed equivariantly. The maps exist from the cited fibre-product universal property; equality on all projections proves the group law. Using j inverse, rather than j, is essential when the group is noncommutative.

9. The reduced-closed-subscheme node supplies existence, affine radical ideals and uniqueness. On P_K the coordinate ring maps onto M because of its M-factor, so the image is a closed point with residue M, not a chosen smaller compositum. The affine closure ideal is a prime kernel, and restriction to the generic fibre localizes that kernel. Thus C_K=Spec M and k(C)=M. The integral-scheme definition licenses reduced plus nonempty irreducible, and the function-field definition includes arbitrary integral schemes. This calculation rules out taking an arbitrary nonstable irreducible component of a product.

10. The action fixes the generic tuple point and hence its closure. Uniqueness in the reduced-closed-subscheme statement is precisely what identifies all restricted composites; no equality of maps is inferred merely from an image inclusion.

11. The absolute-normalization node supplies finite, surjective, birational normalization for the integral finite-type C. The integral-closure-normal lemma and localization-normal-domain give normal local rings. All charts have fraction field M, so normalization keeps the specified generic field and, by localization, the fibre Spec M. Again finite-over-projective is applied only over Spec k, not over S. I checked 0BXR, 0GK4, 034L and 00GY.

12. The dominant-lift node asserts uniqueness for an integral normal source. Here its source is W and its target is the integral C, and g nu is dominant. It therefore gives each action map, its inverse, and the group law by uniqueness. This is the universal property of 035Q(4), not an appeal to a definition for a theorem.

13. The relative projective embedding is proved by a closed graph and product of the absolute embedding. The diagonal is closed since S/k is separated. Properness follows from H-projectivity. Proper-closed-image gives surjectivity because the generic image is dense. Finite-type-over-noetherian gives the Noetherian affine base required by projective-generically-finite. Its generic fibre is exactly Spec M and hence dimension zero, so the cited node gives finiteness over a dense open. I checked this against 0BAI and the actual projective-generically-finite statement, rather than using an uncited generic-finiteness implication.

14. Projection to the identity factor is a global morphism; the fibre-product equality gives r t=b on the whole scheme. No extension of a rational map remains to prove. This is directly the cited fibre-product definition.

15. The fixed-field-purely-inseparable node assumes algebraic normality, established in step 2, and its automorphism group is exactly N by step 3. Its conclusion is therefore M^N/K purely inseparable. The finite-degree clause follows by linear independence in M. In the separable branch the elementary divisibility of minimal polynomials gives separability over K; the finite-Galois-fixed-field node then states exactly M^N=K. I read fields.tex 030M and the finite Galois fixed-field statements 09I1/09DW.

I tested the small cases. For H trivial the lift group is Aut_K(M); for a nonfaithful H the group of pairs still surjects to H even if some pairs act trivially on W. When S has dimension zero, K is its function field, T is finite over S and the graph construction has generic fibre Spec M with no dimension argument to hide. For a purely inseparable L/K in characteristic p the normal-closure branch allows a trivial kernel action and a genuinely larger purely inseparable invariant field. For L/K separable the separate Galois choice forces invariants K. In characteristic zero the inseparable clause means equality. For the identity alteration the construction may take M=K and does not introduce a nontrivial field extension. None of these checks requires k to be perfect or H to act trivially on k.

I also checked B–E of delivery-errors: no new unstated notions or duplicate/clause nodes; all prerequisite quotations are statements, not extracted proof constructions; no reverse edge to a descendant of this item is used; no SGA source appears; all proof steps have Boolean elementary flags and all uses occur in proof_deps. The non-elementary steps are under 2000 characters, and the graph/action calculations are written out rather than hidden by 'standard' or 'transport'. The generic tools from other units are declared in split_report.tool_uses for maintainer review; this preserves the existing alteration route and does not set maintainer-owned tool_uses.
