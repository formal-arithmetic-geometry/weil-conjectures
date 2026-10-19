# Worker report

1. Files written: `dag/nodes/sec-six-functors-basics/det-prop-p1-adjunction-rational-unit-counit.json`, `citations.json`, and this report. No new nodes and no new Mathlib leaves were created.
2. Attachments: none. A source search by the exact blueprint tag and by projective-line, diagonal, rational-adjunction and unit/counit keywords found no sorry-free declaration in `WeilConjectures/` stating all three clauses. Generic Mathlib adjunction declarations and finite-coefficient projective-line declarations are insufficient.
3. WANTED: none.
4. Repair: the dedicated Q149 return required re-splitting the 3339-character first proof step. I preserved the item statement and route, replacing that step with four short steps: properness/Noetherianity, qcqs and the quasi-compact complement, the standing finite-type hypotheses, and the coefficient convention. The existing Mathlib leaves `lem-weil-pbc-locally-noetherian-quasi-separated` and `lem-weil-pbc-noetherian-open-subscheme-noetherian` now carry the topological facts that had been hidden inline. No definition or item clause was moved into a child node.
5. Unfinished mathematics: none. This is stage 1 only; no Lean, compiler, Lake or build tool was run.

## Not duplicates

No new nodes were made. The Noetherian open-subscheme and locally Noetherian quasi-separated facts are existing Mathlib leaves and were cited directly.

## Review by Q149

I read the current shared item, the main-20261015 blueprint item and proof, the `sk-prop-p1-adjunction-rational` unit and chapter, and the triangle sibling. The item statement remains byte-for-byte unchanged. Its three clauses still define the diagonal tensor identification, the unit with the inverse proper-base-change arrow, and the projection-formula/trace counit for the pulled-back condensed coefficients over (E) and the finite-subextension-valued \(\Qlb\). The triangle identities remain in `det-prop-p1-adjunction-rational-triangle`.

The dedicated return was checked first. The old first step was 3339 characters and combined several independent lemmas. It is now four proof steps of 659, 751, 777 and 733 characters. The remaining steps are 1584 characters or shorter, so no proof step exceeds the 2000-character long-step threshold.

Step 1 uses `lemma-nagata-projective-space-base-change-proper` for (q) and the two projective-line projections, `def-weil-proper-morphism` for separated finite type, `lem-weil-pbc-closed-immersion-proper` for properness of the closed diagonal, and `lem-weil-pbc-finite-type-over-noetherian` for Noetherianity after the field, projective-line and product finite-type maps. I checked each cited statement says exactly the property used and that the field has only the two ideals needed for its Noetherian hypothesis.

Step 2 uses the existing Mathlib leaf `lem-weil-pbc-locally-noetherian-quasi-separated` to obtain quasi-separatedness of (Y,P,W), and `lem-weil-pbc-noetherian-open-subscheme-noetherian` to show each (j^{-1}(V)=V\setminus\Delta(P)) is quasi-compact. The cited leaves state those facts for the schemes and open subschemes actually present. `def-weil-finite-type-morphism` supplies the definition of quasi-compact morphism used in the final sentence. This repairs the formerly inline Noetherian-topology argument without adding a duplicate node.

Step 3 checks the standing rational-theorem hypotheses. The item assumes (Y\to\operatorname{Spec}k) separated and finite type. Clause (e) of `lem-weil-pbc-proper-fp-permanence` gives separated and locally finite-type composition for (a_Yq) and (a_Yqp_1); quasi-compactness follows directly because the base field has only empty and whole opens and (P,W) are quasi-compact by Step 1. `def-weil-finite-type-morphism` then gives finite type. This does not assume (Y) is proper.

Step 4 uses the complete statement of `sk-prop-sfb-cartesian-coefficients`: pulled-back condensed coefficient sheaves and their Tate twists identify across all maps, and module pullback is exact. The characteristic assumptions make \(\ell\) invertible on all schemes and the complement, while (E\subset\Qlb) has the required finite-subextension convention.

Step 5 uses `sk-def-sfb-constructible` for the item’s finite constant local models, `det-def-localizing-closure-ctf-equals-bc` for the equality with finite-Tor generators and localizing closures, `det-proper-base-change-unbounded-pullback` for exact pullback, `det-proper-image-localizing-proper` for exact proper pushforward, and `det-thm-sf-pf-field-tensor` for tensor closure. `sk-def-sp-tate-twist` and `sk-def-sfb-constructible` justify the rank-one coefficient and Tate local models. The qcqs hypotheses used here are precisely those established in Steps 1--3.

Step 6 reads the full ringed pro-etale open/closed statement and the Stacks source at Tags 09AA, 09BM and 09AH. It supplies exact closed pushforward, extension by zero, the two restriction identities, and the short exact sequence. Together with exact Cartesian inverse image, `lem-sf-exact-functor-derived-triangulated`, and `sk-def-sfb-derived-categories`, this proves joint conservativity on arbitrary unbounded complexes by applying the sequence to every cohomology sheaf of a cone.

Step 7 uses `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `lem-weil-pbc-proetale-derived-pullback-composition`, and the derived pullback/direct-image adjunction in `sk-def-sfb-module-derived-pushpull` to form the actual map (a_M). The cited open/closed node supplies its diagonal counit and complement restriction; Step 6 supplies joint conservativity. Thus the inverse (a_M^{-1}) has exactly clause (1)’s orientation and is natural.

Step 8 uses `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` with (p_2\Delta=1_P), exact closed pushforward, and the derived-category exact-functor clause. This gives (M\simeq Rp_{2*}\Delta_*M) for unbounded (M).

Step 9 checks the cartesian square ((q,p_2,q,p_1)) against `def-weil-pbc-ambient-ringed-exchange`. For each constant-model generator, `det-def-sfb-constructible-local-model` gives the forward inclusion into the locally finitely presented ring-object category of `sk-def-sfb-bounded-constructible`; the same strata and bounds therefore enter `det-thm-sfb-proper-base-change-rational`. The unbounded extension `det-proper-base-change-unbounded-extension` applies after `det-def-localizing-closure-ctf-equals-bc`. I verified that no converse constructibility inclusion is used and that the inverse exchange has the direction required by clause (2).

Step 10 uses `det-prop-diagonal-tower-trace` and `det-prop-diagonal-tower-coefficients` for the rational diagonal class and trace, the Cartesian coefficient twist comparison, and `det-thm-sf-pf-field-localizing` for the shifted projection formula. The hypotheses \(\ell\) invertible and \(\Lambda=E,\Qlb\) were checked in Step 4; the resulting composite is exactly the displayed unit.

Step 11 applies the same localizing projection formula to (q), (A=\Lambda_P(1)[2]) and (B=K). Tensor symmetry gives the displayed source, and the two diagonal-tower nodes give the trace map and its rational extension. Every object lies in the localizing categories from Step 5.

Step 12 checks the two naturality equations explicitly. `lem-weil-pbc-ringed-projection-mate-exact` supplies exact derived tensor and shift-compatible projection transformations; `det-proper-base-change-unbounded-pullback`, `det-proper-image-localizing-proper`, and `sk-def-sfb-derived-categories` supply exact pullback, proper pushforward and shifts. The triangle sibling is not assumed in this construction.

I checked edge cases (Y=\varnothing), zero (M) and (K), (Y=\operatorname{Spec}k), unbounded complexes, and characteristic \(p\ne\ell\). Empty and zero cases reduce to the unique zero maps; the cone argument is degreewise and therefore covers unbounded objects; the rational coefficient and Tate sheaves have the stated rank-one finite constant models. No finite-coefficient or SGA route was introduced.

The Mathlib searches were run with `msearch.py` under Q149 for the item, and their exact records are in `searches.jsonl`. They returned only generic adjunction/sheafification, scheme permanence, Noetherian topology, Proj chart, pro-etale-site and integral \(\ell\)-adic declarations; none states this full rational pro-etale construction. The inherited item search records were retained. `citations.json` contains one verbatim full statement quote for every step/use pair (44 pairs), and `proof_deps` is exactly the union of those uses. No new node has a duplicate or missing blueprint reference.
