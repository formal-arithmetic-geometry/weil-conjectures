Files written:

- `lem-route-pro-etale-canonical-pullback-composition-exists-unique.json` — repaired statement and three-step split; no Mathlib match.
- `lem-route-pro-etale-module-adjunction-normalized-unique.json` — statement-only supporting lemma; no Mathlib match.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.

Attachments: none. The live declaration `AlgebraicGeometry.Scheme.proEtaleCanonicalPullbackComposition_existsUnique` is still proved by `sorry`, so it is not an attachment.

WANTED: none.

The imported item was machine-generated with a truncated Lean signature ending at `SheafOfModules.IsFlatOnSite (J`; I reconstructed the missing tail from `lean/Sheaf/AlgebraicGeometry/ProEtaleCanonicalPullbackComposition.lean:37-96`. I also corrected the direction of the ordinary comparison `a` to match Lean: it runs from the pullback for `h ≫ k` to the iterated pullback. The existing node `lem-weil-pbc-proetale-derived-pullback-composition` is a genuine existence theorem but does not state uniqueness, so I did not treat it as a duplicate or as an attachment. The new normalized-adjunction node is strictly smaller than the item and does not restate the derived comparison clause.

## Review by NB

I read the complete item declaration and docstring in `lean/Sheaf/AlgebraicGeometry/ProEtaleCanonicalPullbackComposition.lean`, the imported parent route `lem-weil-pbc-proetale-derived-pullback-composition`, the composite-coefficient definition, and the module-adjunction construction. The hypotheses in the rewritten statement match Lean: arbitrary schemes and morphisms, three pro-etale commutative-ring sheaves, two coefficient isomorphisms, and `hc_hk` identifying the composite coefficient. The comparison and `a`, `b`, and factor-map directions were checked against lines 46–95.

Step 1 uses the existing composition theorem for exactly its stated witnesses: normalized adjunctions, the sectionwise direct-image compositor, its conjugate module pullback comparison, the degreewise cochain comparison, and the derived K-flat factor equation. Its K-flat and flatness hypotheses are copied from that theorem, so no properness or morphism-flatness assumption is introduced.

Step 2 uses the new normalized-adjunction lemma, whose statement says that the tensor-unit section formula determines each module adjunction. I checked that this is the specialization of the source construction's `proEtaleRingModuleAdjunction_existsUnique` and the unit formula recorded by `lem-pod-canonical-module-adjunction-unit`; equality of adjunctions is by unit extensionality. The two `d` maps have identical section formulas, so sheaf-module extensionality gives equality. The cited conjugation lemma then makes `a` equal, and equality of `b` follows degree by degree from its displayed equation and homological-complex extensionality.

Step 3 uses the existing flat-term K-flat resolution node and the ringed-topos pullback preservation node with precisely the item’s pro-etale ring map. The representative equation therefore agrees for both candidate comparisons on a K-flat resolution. The resolution quasi-isomorphism becomes invertible after derived localization, and the cited localization universal property transports equality to every derived object. I checked the edge cases of identity morphisms, zero complexes, empty schemes, and non-flat coefficient maps; none adds a hypothesis or changes the statement.
