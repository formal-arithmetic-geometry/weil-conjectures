# def-sc-picard-functor

## Files written

- `dag/nodes/sec-abelian-varieties/def-sc-picard-functor.json`: repaired definition split; no new nodes and no Mathlib leaves. The curve hypothesis now explicitly says smooth projective and geometrically integral, with the corresponding existing definition nodes cited. Pic^d is defined as `deg^{-1}(d)`, namely the classes whose degree function is identically d.

## Attachments

None. The source declarations checked below are related constructions but do not state this item exactly.

## WANTED

None.

## What was checked

The current node has `lean_audit.slopmaster2.state = none`. I searched the read-only source with `grep -rn` for `def-sc-picard-functor`, `Picard functor`, `Pic^d`, `picardFunctor`, and the exact blueprint marker `(blueprint: def-sc-picard-functor)` under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`. There is no declaration carrying the item marker. `AlgebraicGeometry.picardFunctor` in `WeilConjectures/AlgebraicGeometry/Picard/Defs.lean:180-182` is the fppf sheafification of the generic relative Picard presheaf for an arbitrary morphism `f : X ⟶ S`; it does not impose the item's proper smooth connected curve hypotheses, use the k-algebra presentation, or define the degree-d subfunctors. `AlgebraicGeometry.picardFunctorDegree` in `WeilConjectures/AlgebraicGeometry/Picard/Jacobian.lean:222-231` sheafifies a field-valued degree subfunctor for `f : X ⟶ Spec k`, but has no smooth/proper/connected assumptions in its declaration and is marked `sk-prop-picard-degree-decomposition`, not this definition. Its support `picardFibreDegree` is at lines 180-196. The source's `picardPresheaf` (`PicardFunctor.lean:331-344`), `picardPresheafDegree` (`Picard/Degree.lean:76-87`), and `picardDegree` (`Picard/Degree.lean:161-170`) were also read; none states the item as a whole. The source sorry map therefore supplies no exact declaration to attach.

Before editing, I searched the DAG and the full blueprint. Existing nodes `def-pc-smooth-projective-curve`, `def-pc-geometrically-irreducible`, `def-pc-picard-functor`, `def-pc-picard-presheaf`, `def-pc-fppf-site`, `def-pc-subfunctor`, `def-pd-fibrewise-degree`, and `def-pd-degree-morphism` already state the component notions, so no duplicate node was created. Blueprint search found the generic `def-pc-picard-functor` as the only same-as reference retained; the degree-decomposition proposition was removed because it contains later representability and translation conclusions rather than the definition itself.

## Review by M1

I read the imported master definition (source place `sec-abelian-varieties/sk-def-av-jacobian/def-sc-picard-functor.md`, node order 447) and checked each clause against its dependencies. The repaired first sentence now introduces a field k, a smooth projective curve, and geometric integrality through `def-pc-smooth-projective-curve` and `def-pc-geometrically-irreducible`; this is the E7 correction to the earlier vague “proper smooth connected curve” wording. The sheafification clause uses `def-pc-picard-presheaf`, `def-pc-fppf-site`, and `def-pc-picard-functor`; Picard values and invertible modules use `def-sc-picard-group` and `def-sc-invertible-module`. The second clause explicitly refers to residue-field fibres through `def-pd-fibrewise-degree`, the degree morphism through `def-pd-degree-morphism`, and the inverse-image subfunctor through `def-pc-subfunctor`; it defines Pic^d as `deg^{-1}(d)` and says its classes have identically d degree on every base. These are definitions, so no proof steps are required and no elementary claim is hidden in a proof.

I checked the existing component node statements, rather than relying on their names: `def-pc-smooth-projective-curve` introduces the smooth/projective curve over a field, `def-pc-geometrically-irreducible` defines geometric integrality via all field extensions, `def-pc-picard-functor` explicitly says fppf sheafification of the relative Picard presheaf, `def-pd-fibrewise-degree` defines the degree on residue-field fibres, and `def-pd-degree-morphism` defines the sheaf-valued degree. The broader `prop-pd-picard-degree-decomposition` was removed from `same_as` because it asserts representability, openness/closedness, subgroup, and translation conclusions not present here. No new node was needed, hence B1-B7 and C1-C7 introduce no new-node obligations. The definition does not assume representability or openness/closedness, and I preserved those limits.

I checked the small cases required by E: `d = 0` gives the degree-zero inverse image; negative `d` is still an integer fibre-degree condition; an empty test base makes the pointwise condition vacuous; and disconnected bases are handled by the degree function on each residue-field fibre. No representability or openness/closedness is inferred. The source declarations mentioned above do not match these hypotheses, so I did not attach them under the Lean-closure rule. The sandbox contains only this repaired item node and this report; no source checkout was written and no build was run.

## Repair of 9d9b9f3b

I repaired every returned point. For E1/B3 and E7, the hypothesis now says “smooth projective curve over a field k which is geometrically integral,” citing `def-pc-smooth-projective-curve` and `def-pc-geometrically-irreducible`; the earlier vague proper/smooth/connected wording is gone. For C4/E4, Pic^d is now explicitly `deg^{-1}(d)` and its elements are classes whose degree function is identically d, with no claim that a global representative is already an invertible module. For C1/C4, the definition names residue-field fibres and cites `def-pd-fibrewise-degree` and `def-pd-degree-morphism`. For B9, `same_as` now retains only `def-pc-picard-functor`; `prop-pd-picard-degree-decomposition` was removed. The source audit and the review above were reread after these edits, and the exact source declarations remain non-attachments.
