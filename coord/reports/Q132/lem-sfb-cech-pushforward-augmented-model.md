# Q132: lem-sfb-cech-pushforward-augmented-model

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cech-pushforward-augmented-model.json: existing statement, now split into six proof steps; no Mathlib match for the complete statement.
- citations.json: fourteen step/node records with verbatim excerpts of the existing cited statements.
- report.md: this report.

No new nodes and no new Mathlib leaves. The earlier sandbox item, its proof route, provenance, and logged searches were retained. I added the explicit uniqueness-of-lifts citation in step 6 and explained additivity in step 2. No Lean was written or compiled; no repository or launcher file was changed.

## Attachments

None. Searching lean/WeilConjectures for the item tag and augmented Cech/pushforward terminology found constructions for more restricted settings, not a declaration covering every clause for an arbitrary ringed-topos morphism with exact module inverse image. They do not supply an attachment to this item.

## WANTED

None. All sources used are present locally.

## Audit findings and corrections

The live item is unsplit with no proof and no released repair note. Its statement and statement dependencies are unchanged. Its ancestor chain and source place were retained; tools/blueprint_refs.py ancestor reports a null blueprint ancestor for this already existing chain. The existing explicit from.place identifies the contribution to main-20261015 sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). This is a formal descent input below that direct-image argument, not a replacement of the unit route. The item is not the unit's key statement, so no realization record was changed.

The existing lem-sfb-cech-injective-column-model, lem-sfb-cech-injective-image-augmentation and lem-sfb-cech-augmentation-normalized-naturality require Cartesian coefficients. Applying them directly to the given f would add a hypothesis. Instead all three are applied to the identity of the source ringed topos, where the coefficient identification is the identity. The resulting injective model is pushed through the actual f_* using lem-sfb-injective-finite-total-derived-comparison. This proves the statement with the given structural ring map.

In the retained draft, step 6 named a homotopy between lifts without citing its existence. I added lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, whose statement gives exactly that homotopy for a quasi-isomorphism into a bounded-below injective target. Both lifts agree after the resolution augmentation. This avoids deducing homotopy invariance after f_* merely from equality of source derived morphisms.

## Not duplicates

No new nodes. The DAG searches for 03FC, injective finite totals and Cech models, and the whole-blueprint Cech search, instead led to reuse of the existing column, augmentation, naturality, finite-total, adjunction and lift-comparison nodes. The imported affine/open-cover Cech nodes returned by the blueprint search have narrower settings and do not state this augmented ringed-topos pushforward model. No replacement node for a clause of the item was introduced.

## Mathlib searches

I read and retained searches.jsonl and the item's recorded results. The logged queries include LeanFinder descriptions of the augmented Cech pushforward model and a second phrasing about pushing forward a first-quadrant augmented complex; Loogle queried "rightDerived", "comp"; grep queried (cech|cosimplicial).*(derived|pushforward)|(derived|pushforward).*(cech|cosimplicial); LeanSearch queried naturality of a canonical augmented Cech descent model. The services returned ordinary nerves, sheaf pushforwards, general derived functors and composition comparisons; grep returned no hits. Mathlib/AlgebraicTopology/CechNerve.lean, lines 77-115, constructs the ordinary augmented nerve. Those hits do not give the coherent nonnegative module complexes with the specified derived columns, total comparison, localization unit, and refinement/resolution compatibilities. Existing Mathlib general tools are already represented by cited nodes. No new node needs additional search records. No unavailable service was relabelled as absence, and no unrun query was added.

## Review by Q132

I read the complete B-E checklist in coord/delivery-errors.md, the stage-1 brief, GOAL.md, the three blueprint levels in SETUP.md, and the item's chapter and unit. I read the current direct-images proof paragraph (3). For the item I read Stacks sites-cohomology.tex Tag 03FC (lemma-injective-module-trivial-cech), including its proof: injectivity kills positive Cech cohomology and the sheaf condition determines degree zero. That tag alone is not asserted to contain the entire enhanced model. The proof is correctly marked agent-written, assembled from existing precise statements. For the derived and adjunction ingredients I read derived.tex Tags 015J (lemma-two-ss-complex-functor, including finite totalization in proof remark (3)), 070J (lemma-bounded-below-injectives-K-injective), 09T5 (lemma-derived-adjoint-functors), 013P (lemma-morphisms-lift), and 013S (lemma-morphisms-equal-up-to-homotopy); sites-cohomology.tex Tag 0D6E (lemma-derived-pushforward-composition); homology.tex Tag 015Z (lemma-adjoint-preserve-injectives); and sites-modules.tex Tags 04IE, 04J4, and 03D7 (localization, relocalization, and the actual module adjunction). There are no new-node sources to audit.

For each step I opened every cited node and read its statement, rather than using its proof as an unstated interface:

1. lem-sfb-cech-injective-column-model supplies a nonnegative resolution, actual cosimplicial operators, K-injective restricted columns and canonical comparisons. lem-sfb-cech-injective-image-augmentation supplies the specified augmentation quasi-isomorphism. Both apply to id_X, whose Cartesian coefficients and exact inverse image are immediate. The covering is still the given epimorphism, and arbitrary slice objects, rather than just representables, are explicitly covered by the augmentation statement.
2. lem-weil-pbc-ringed-sheaf-slice-adjunction states exact restriction and an exact additive left adjoint for arbitrary sheaves of sets on the small site. Applying lem-sp-right-adjoint-preserves-injectives to both slice adjunctions proves termwise injectivity of K. lem-weil-pbc-ringed-topoi-module-adjunction supplies f^* adjoint to the actual module f_* for its structural ring map. Left exactness follows from the adjunction's finite-limit universal property, and additivity from the sectionwise addition, as now written. No flatness of an unspecified coefficient change is assumed.
3. lem-sfb-injective-finite-total-derived-comparison states the isomorphism of entire derived objects, finite-biproduct normalization, termwise-injective total and operator compatibility. Its hypotheses hold with J=K and u=id. Both module categories are Grothendieck by the item; no infinite diagonal is present. def-sfb-right-derived-functor gives the natural derived unit, invertible on the K-injective representatives I and T(K), which identifies the displayed augmentation representative.
4. lem-sfb-derived-composition-adjunction-normalization states the comparison on K-injective representatives and compatibility with the specified composite adjunction. Here L_a=f^*, L_b=v_n^*, L_c=(fv_n)^*, with the canonical composition identification. Both left adjoints are exact, and v_n^*I is K-injective by step 1. Taking the inverse comparison gives precisely the beta_n in the item, with the actual restriction operators.
5. lem-sfb-cech-augmentation-normalized-naturality explicitly identifies the degree-zero projection with the localization unit, its restriction-of-sections representative and its identity adjoint transpose. It is used for id_X before applying Rf_*. lem-sfb-injective-finite-total-derived-comparison preserves the (0,q) inclusions, so no sign or arbitrary automorphism changes this normalization.
6. lem-sfb-cech-augmentation-normalized-naturality supplies lifts, strict induced restrictions and refinement maps commuting with augmentation and resolution comparisons. The added lem-weil-pbc-lift-to-injective-unique-up-to-homotopy supplies a homotopy for any pair of lifts; its target is the nonnegative injective complex J and its quasi-isomorphism is a:N[0] to I. The explicit signed total homotopy is then preserved by the additive f_*; horizontal terms cancel and vertical terms give the difference. The finite-total comparison gives naturality in strict maps, and the normalized composition comparison gives naturality of the derived columns. Thus all assertions concern entire models in the derived category, not only cohomology groups.

The four generic tools from other units are declared in split_report.tool_uses: the two module/slice adjunction tools, preservation of injectives, and uniqueness of lifts. They support the model construction without replacing a unit step. Every proof use has a verbatim citation record; proof_deps is exactly the union of uses. No step exceeds 2000 characters, and none hides an extra comparison theorem: the comparisons and homotopies are explicitly supplied by the cited statements.

I tested the zero module, the identity cover V=1, low total degrees r=0 and r=1, and a split cover. For V=1 the augmented constant cosimplicial model retracts onto N; for N=0 all columns and the total vanish. In degree zero the only summand is (0,0), so the augmentation is exactly the unit. In degree one the horizontal/vertical sign is the stated delta+(-1)^n d; the total homotopy uses the same sign. An empty epimorphic cover can occur only in a degenerate topos, where module objects are zero, so it yields no counterexample. The argument uses no exactness of f_*, no preservation of infinite coproducts by f_*, and no representability assumption on V. No statement dispute was found.

## Unfinished work

None for this one-level split. Existing cited unsplit nodes remain their own stage-1 items. Independent maintainer review remains part of the delivery protocol.
