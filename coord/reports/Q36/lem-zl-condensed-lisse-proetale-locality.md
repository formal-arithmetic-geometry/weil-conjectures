# Stage 1 report: lem-zl-condensed-lisse-proetale-locality

## Worker report

Files written:

- `dag/nodes/sec-zeta-weil/lem-zl-condensed-lisse-proetale-locality.json` — statement node, repaired split.
- `dag/nodes/sec-zeta-weil/lem-zl-dualizable-jointly-conservative-locality.json` — statement-only helper, repaired abstract hypotheses.
- `dag/nodes/sec-zeta-weil/lem-zl-condensed-cover-restriction-conservative.json` — existing statement-only helper, with the pro-etale localization dependencies added.
- `citations.json` — verbatim statement quotes for every cited node at every proof step.

There are no new Mathlib leaves and no WANTED items. The item was checked against Hemo–Richarz–Scholbach, Section 3 (the pullback paragraph before (3.1)), Definition 3.3, and Lemma 4.5. No sorry-free declaration in the project states the item exactly.

This is a repair of the returned delivery. The original Step 1 cited only underived coefficient and pullback-from-point nodes; it now cites the derived tensor-pullback comparison, derived monoidal coherence, the closed derived structure, and the constant-module inverse-image statement. The scalar-extension paragraph explicitly uses inverse image of a site-constant module and the derived pullback/base-change coherence. The conservativity step now identifies the slice pro-etale site and coefficient ring and identifies module inverse image with restriction. The internal-Hom step now cites the derived internal-Hom restriction and slice evaluation/transpose comparisons. The abstract helper no longer treats a pro-etale-specific node as an abstract closed-category definition: its statement explicitly assumes symmetry, internal-Hom adjunctions, a natural Hom comparison, and preservation of transposes. The unsupported sentence about profinite-set covering arguments was removed from Step 5.

## Review by Q36

I read the returned item, both helper nodes, their cited statements, and the Hemo–Richarz–Scholbach source. I also opened the statements of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `lem-sfb-ringed-derived-monoidal-comparisons`, `lem-sf-ringed-derived-closed-symmetric-monoidal`, `lem-sfb-geometric-inverse-image-constant-module`, `lem-weil-proetale-weakly-etale-localization`, `lem-sfb-proetale-object-inverse-image-restriction`, `lem-weil-pbc-ringed-internal-hom-exact-restriction`, and `lem-weil-pbc-ringed-slice-evaluation-transpose`.

Step 1 now takes the coefficient ring isomorphism and underived monoidality from `sk-def-sfb-coefficient-morphisms`, exact module inverse image and its derived functor from `lem-pe-constant-left-module-inverse-image` and `def-weil-pbc-proetale-operations`, and the derived tensor comparison from `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. The monoidal-comparisons statement supplies associator, unit, symmetry, and composition/base-change coherence; the closed derived structure is stated by `lem-sf-ringed-derived-closed-symmetric-monoidal`. For the scalar-extension clause, `lem-sfb-geometric-inverse-image-constant-module` says that inverse image of every site-constant module is the corresponding constant module, while `def-sfb-site-derived-constant-module-functor` defines the derived realization. Thus every fact used in this step is in a cited statement, including the previously missing constant-module and derived-base-change facts.

Step 2 is elementary: applying a strong symmetric monoidal functor to evaluation and coevaluation and using naturality of the tensorator carries both triangle identities across. It uses no unstated lemma.

Step 3 uses the cover-conservativity helper. I checked that its hypotheses cover arbitrary schemes, arbitrary pro-etale covering families, and ordinary unbounded module derived categories. The pro-etale localization statement explicitly identifies $(X_{\mathrm{proet}})/U_i$ with $(U_i)_{\mathrm{proet}}$ and identifies the restricted constant coefficient ring with $\Lambda_{U_i}$; the pro-etale object inverse-image statement identifies the module pullback with this restriction. These are now cited both by the item step and by the helper's statement dependencies, fixing the missing site/coefficient identification.

Step 4 uses the derived tensor comparison and the closed symmetric monoidal derived-category statement. The internal-Hom restriction node supplies the natural derived Hom comparison on the slice, and the slice evaluation/transpose node supplies compatibility of evaluation, transposition, and symmetry. The abstract helper is now applied only after these concrete hypotheses are established. Its repaired statement explicitly includes the tensor--internal-Hom adjunction and the commuting transpose square, so the earlier imprecise phrase “compatible with tensor-unit adjunctions” and the incorrect pro-etale-specific citation are gone.

Step 5 applies the repaired abstract criterion and the joint conservativity helper to obtain the stated equivalence. The old profinite-set argument was deleted because it was unsupported by the helper nodes and was not a conclusion of the item. The remaining sentence only records the absence of quasi-compactness and component bounds, which is part of the item statement.

I checked all hypotheses against the cited statements, including empty covering/index cases, the zero object, identity and single-map covers, arbitrary (possibly infinite) covering families, and unbounded complexes. I searched the DAG and blueprint for each added fact before citing it; the localization, module restriction, derived tensor, monoidal coherence, and internal-Hom nodes are existing nodes rather than duplicates. `citations.json` contains a verbatim full statement quote for every node used by every non-elementary step. No Lean source, compiler, build tool, live project, or launcher file was modified.
