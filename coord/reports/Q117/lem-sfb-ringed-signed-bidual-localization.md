# Q117: lem-sfb-ringed-signed-bidual-localization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-signed-bidual-localization.json`: statement, split into eight proof steps; not a Mathlib leaf. Statement and statement dependencies unchanged. All eleven proof dependencies already exist.
- `citations.json`: 21 entries, one per step/cited-node pair, quoting the cited statements verbatim.
- `report.md`: this direct-delivery review. `searches.jsonl` contains the actual msearch results; `write_split.py` is a sandbox-only preparation helper.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched `lean/WeilConjectures/` for the item's blueprint tag and for biduality, signed bidual maps, double Hom complexes and `toIhomIhom`. The exact item tag and the signed-chain-map/localization descriptions have no hits. The project contains ordinary sheaf/presheaf biduality in `Algebra/Category/ModuleCat/{Sheaf,Presheaf}/Bidual.lean`, abstract closed-category double-dual identities in `SixFunctors/Etale/Derived/DoubleDual.lean`, and perfect-complex derived biduality in `CategoryTheory/DerivedCategory/Perfect.lean`. None states the product-Hom chain formula together with both fixed-augmentation comparisons for arbitrary unbounded complexes on a commutative ringed site. They do not justify attaching this item.

## WANTED

None. The sources used below are present locally.

## What was wrong or incomplete

The item was an unsplit statement with no proof. I found no statement error: both augmentation assumptions are necessary for the specified comparisons, and the derived equation is correctly typed as an equality from QE to H(QD,O). I preserved its statement, provenance and blueprint ancestry. I supplied the sheaf-level construction (including its behavior on every localized site), the differential calculation, naturality and the comparison through two temporary K-flat resolutions. In particular I did not replace the product Hom with a direct-sum Hom, or assume that E or its ordinary dual D is K-flat. The map beta need not be an isomorphism.

The source is Stacks `sites-cohomology.tex`, Tag 0A8X (`section-hom-complexes`), Tag 0A92 (`lemma-evaluate-and-more`), and Tag 0A97 (`lemma-internal-hom-evaluate`). I also read the construction of RHom and its adjunction in Tags 08J7 and 08J9, and the proof of 0A97. Stacks omits the general functoriality check in 0A97. For the ordinary signs I read `more-algebra.tex`, Tag 0A60 (`lemma-evaluate-and-more`), including the component comparison with the differential, and Tag 0A5Y (`lemma-compose`). The two-resolution argument here provides the precise fixed-model compatibility required by this item, rather than citing the omitted verification as a theorem. Accordingly `proof_origin.by` is `agent`, with the source places recorded.

The blueprint ancestor is `det-thm-sf-ctf-stability-internal-hom`. I read its current main-20261015 proof: paragraph 2, “The formula,” ends by using the coefficient dual of a locally constant perfect complex to identify internal Hom with tensor by its dual. The item's existing ancestry through `lem-sfb-ringed-site-duality-maps` and `lem-sfb-ringed-site-perfect-duality` supplies part of that normalization. The generic calculation stays below this unit route. The item is not the unit's key statement, so no unit realization record was edited.

## Mathlib and reuse searches

All new searches were run through the required msearch command and are copied from `searches.jsonl` into the item without inventing queries. Two LeanFinder phrasings produced global Hom/localization and sheaf-presentation results. LeanSearch produced ordinary module dual evaluation and a shifted-complex evaluation isomorphism. Loogle with `HomologicalComplex, Module.Dual` had no hits; the second query `Module.Dual.eval_naturality` found exactly the ordinary linear-map naturality lemma. The two grep queries searched CategoryTheory and Algebra/Homology. I read `Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean` at its introduction: it constructs a complex of global morphism abelian groups, not the sheaf-internal Hom of this item. I read `Mathlib/LinearAlgebra/Dual/Defs.lean`, including `Module.Dual.eval_naturality` around line 175: it has no complex differential, signs, sheaf internal Hom or derived comparison. Neither is an exact or one-line match for the item. All services used answered successfully; none was recorded as unavailable or as a fictitious negative search.

I searched the DAG for the augmentation/uncurrying models, biduality and the cited Stacks places, and the whole imported blueprint with `blueprint_refs.py search` for `bidual`, `double dual` and `signed`. I reused the normalized model, the fixed representative evaluation, the existing K-flat resolution theorem and Hom invariance; no extra lemma is hidden as a new copy of a clause of the item.

## Not duplicates

No new nodes are proposed. In particular `lem-sfb-hom-kflat-chain-transpose` is a useful existing one-flat-input transposition statement, but the proof here uses the already stipulated normalization directly on two flat-term K-flat inputs. `lem-sfb-ringed-ordinary-evaluation-localization` concerns the different unsigned tensor-to-Hom map and is not used. The parent `lem-sfb-ringed-site-duality-maps` depends on this item; it is not cited back and cannot create a circular proof.

## What remains unfinished

Nothing in the requested one-level split. There is no Lean writing, compiler invocation, or library build in this stage-1 delivery. The maintainer's independent mathematical review remains the next project step after pushing.

## Review by Q117

I read sections B through E of `coord/delivery-errors.md` in full and checked the actual statements of every cited node. Here is what those statements supply in each step, including the hypotheses of the derived comparison.

1. `def-pur-hom-complex` explicitly gives the product indexed by all source degrees, its sectionwise interpretation and componentwise functoriality. `def-pur-sheaf-hom` explicitly defines local Hom sections as maps of restricted sheaves. Thus the formula for beta is specified for every V to U, not just on U-sections, and defines an actual map into the product. Because O is concentrated in degree zero, exactly one source degree can have a nonzero target component. Linearity and compatibility with restriction are immediate from evaluation. This is an elementary construction and uniqueness check, not an appeal to a biduality theorem.

2. `def-pur-hom-complex` states precisely d(f)=d_target f-(-1)^degree f d_source. I substituted this formula twice with zero differential on O. The displayed exponent a+1+a(q+1)+q+1 differs from (a+1)q by 2a+2, so the signs agree for every integer a and q. The only possible component has q=-a-1; all other components vanish in O. This proves the chain condition directly and leaves no unproved Hom differential or convergence fact.

3. The same definition supplies precomposition by f as the map on the first Hom argument. Substituting f(x) gives the displayed equality on all product projections and all restrictions. The degree of a chain map is zero, so no further sign occurs. This is the full naturality argument, with the direction of the double contravariance checked.

4. `def-pur-derived-internal-hom` states the fixed K-injective replacement model and its functorial localization. `lem-pur-rhom-well-defined` states invariance of Hom under a first-variable quasi-isomorphism into a K-injective target (take its target comparison to be the identity of J). `def-weil-abstract-derived-category` states that Q localizes quasi-isomorphisms. The two maps c_E and c_D are quasi-isomorphisms only because the item assumes this; no theorem is claimed to make Hom(-,eta) a quasi-isomorphism for arbitrary complexes. Their localized maps are exactly the named gammas.

5. `lem-pc-kflat-resolution` supplies flat-term K-flat resolutions of every complex, and hence of both E and D on the given ringed site. It does not require boundedness. The Hom-complex functoriality, fixed representative evaluation/localization of `def-coef-hom-representative-evaluation`, and `lem-pur-rhom-well-defined` identify the actual g and h with the two displayed derived composites. The latter theorem's K-injective hypothesis is verified by J=I(O); both p and t are quasi-isomorphisms. This step does not use any assertion that E or D is K-flat, or that c_E is a map to a K-injective Hom complex.

6. `def-coef-ringed-tensor-hom-model` explicitly states uncurrying of a chain map between two K-flat inputs, with formula phi(x)(y), the canonical tensor comparison and the inverse localized augmentation. It applies to g with inputs T,P and target replacement I(O). `lem-sf-ringed-derived-closed-symmetric-monoidal` supplies the counit formula and naturality in the right tensor argument. Together they give the stated u and the actual evaluation composite. I checked the order T,P and the inverse Qeta, so this step cannot accidentally insert a swap sign or an arbitrary comparison map.

7. The same normalized model applies to h with inputs P,T. Substitution of the beta formula gives v with the sign (-1)^(a q). The symmetric monoidal statement explicitly gives that same Koszul sign on K-flat tensor representatives. `def-pur-sheaf-tensor-product` defines tensor as sheafification of sectionwise tensor, and `def-pc-tensor-complex-sheaves` gives its direct-sum total. Thus equality on bilinear local pure tensors determines each sheaf tensor map, and equality on each coproduct inclusion determines the total map. There is no interchange of an infinite sum and a product. I spelled out v=u composed with the symmetry instead of hiding the compatibility in the word “transports.”

8. The closed symmetric monoidal statement explicitly supplies a bijection natural in both tensor inputs and identifies uncurrying with counit evaluation. This yields the displayed formula for the other side after precomposing by Qp and changing the right tensor input by gamma_E Qt. Naturality of its symmetry gives the written equality of the two factorizations. Injectivity of that bijection and cancellation of the isomorphisms Qp and H(Qt,O) are elementary. The derived internal Hom definition supplies functoriality, so H sends the isomorphism Qt to an isomorphism. This step proves the claimed equation using steps 6 and 7; no smaller node simply restates that equation.

I checked the following small cases. For a zero complex or the zero ring every component is zero. For E concentrated in degree a with value Z and zero differential, the coefficient bidual map is (-1)^a times ordinary evaluation, including for negative a; this agrees with the Koszul swap in degrees a,-a. In characteristic two the signs all become one and the differential identity still holds. For the complex Z in degrees 0 and 1 with differential multiplication by 2, D has differential +2 from degree -1 to 0, the double dual has differential -2 from degree 0 to 1, and beta is +evaluation in degree 0 and -evaluation in degree 1; both sides of the chain condition are -2. For the nonflat degree-zero complex Z/2 over Z, the ordinary dual is zero and beta is the zero map; its first Hom augmentation is not a quasi-isomorphism, so the derived comparison is correctly conditional and does not assert false reflexivity. Unbounded E causes no finiteness issue because each coefficient-Hom component lands in a single degree of O, while the temporary P,T tensor uses the direct-sum total explicitly present in the model.

All eight proof steps have fewer than 2,000 characters. The comparison steps are applications of existing normalized models with their hypotheses checked, not embedded independent lemmas. No new unsplit node, new definition, new literature request, or statement dispute is necessary. Off-unit foundational constructions and theorems used as generic tools are declared under `split_report.tool_uses`; they implement the fixed objects of the item and do not replace the unit's geometric proof route. The server's initial `review_split` check passed with zero new nodes; its observation that the unit has no realization recorded is not a request to edit a unit key statement in this non-key item.
