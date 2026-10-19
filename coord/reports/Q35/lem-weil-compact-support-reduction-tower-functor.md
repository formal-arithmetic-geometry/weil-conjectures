# Q35 stage-1 report

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-compact-support-reduction-tower-functor.json` — statement item, marked `split`; the imported eight-step proof and its twenty existing dependencies were audited, with no new DAG nodes.
- `citations.json` — 28 step/node entries, each quoting the cited node verbatim.
- `report.md` — this report.

## Attachments

None. The source search found `WeilConjectures.exists_compactSupportReductionTower` in the generated Lean file `lean/Sheaf/Paper/CompactSupportReductionTower.lean:216`, but its proof is `sorry` (and its formal existential statement is not the natural-language item), so it is not an attachment. No declaration tagged with this item is present in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

## WANTED

None. The proof uses the existing DAG framework statements and the cited Stacks/blueprint sources already recorded in the item.

## What was checked and corrected

The item is the coherent strict reduction-tower prerequisite for the first proof sentence of `lem-weil-compact-support-representative-independence`. I compared the sandbox copy with the current repository node, retained its prior proof, searches, and tool-use declarations, and updated only the split metadata and date. The current `lem-coef-semilinear-derived-sections` statement still supplies coherent section models, evaluation, geometric operations, and coefficient comparisons for arbitrary semilinear sections; its cartesian-first-input restriction applies only to its internal-Hom clause, which no step here uses. The completed coefficient interpretation is retained throughout. All twenty identifiers in `proof_deps` exist and are exactly the union of the `uses` lists; no duplicate or new intermediate statement is needed.

## Review by Q35

I read the item, the `sk-def-sf-operations` unit, the `sec-smooth-purity` chapter, the current blueprint proof of `lem-weil-compact-support-representative-independence`, and the statements of every cited node. I also checked the generated Lean declaration and its `sorry` status as described above.

1. Step 1 constructs the ringed sequence site and identifies its module category with semilinear systems. The cited diagram-site node states the product-site/module equivalence and its exact evaluation; the sheaf-module definition supplies the module category; the K-injective proposition supplies K-injective resolutions on a small ringed site; and `lem-coef-semilinear-derived-sections` supplies the coherent derived-section model and evaluation data. The only size hypothesis used is the smallness already stated for the pro-etale sites and coefficient universes.
2. Step 2 applies the cited ringed-topoi derived-pullback theorem, whose hypotheses are small sites, ring sheaves, a topos morphism, and a ring map. The K-flat-resolution node supplies a flat-term K-flat replacement, and the integral-derived-reduction definition identifies the termwise tensor with (K_n). The displayed quotient-chain identity is checked before localization, so no equality of arbitrary derived diagram lifts is assumed.
3. Step 3 uses the inverse-image definition and the finite constant-ring-map proposition for the maps induced by (j) and (p); both preserve the quotient sections. The weakly-etale-localization node identifies the open site with the slice site, and the exact extension-by-zero node supplies (j_!). The compact-support restriction-of-scalars node supplies the identity (j_!\operatorname{Res}=\operatorname{Res}j_!) and the direct-image coefficient comparison is supplied by the semilinear-section node together with its direct-image restriction-of-scalars comparison. The section theorem is used in its stated geometric scope, including noncartesian outputs of (J_D); its internal-Hom qualification is irrelevant.
4. Step 4 defines the completed-coefficient restriction (U_Y). The restriction-of-scalars node states exactness on modules over the completed coefficient sheaf, and the exact-functor factorization node supplies its derived functor and shift data. The compact-support direct-image definition states (Rf_{!,n}^c=R\bar f_{*,n}j_!), giving the displayed evaluations. The projection identity (q_{m,n}\pi_m=\pi_n) is an elementary consequence of the coefficient quotient maps.
5. Step 5 uses K-injectives from the small ringed-system site, the right-derived-functor node for triangulatedness of (RP_*^{\mathscr S}), and the composite-triangulated-functor node for the four-factor composite. The exact pullback and exact extension/restriction factors are those constructed in steps 2–4, with their shift structures from the cited factorization statements.
6. Step 6 reads the finite-level comparison from the compact-support restriction-of-scalars node. The semilinear-section node supplies its coherent evaluation and adjunction-transpose construction, while the direct-image restriction node gives the normalization on K-injective replacements and explicitly does not require restriction of scalars to preserve K-injectives. The compactification hypotheses are the separated finite-type map and the chosen (j,p) in the item statement; the finite coefficient maps are the stated quotients (A_m\twoheadrightarrow A_n).
7. Step 7 uses the restriction-of-scalars node's transitivity clause and the semilinear-section node's coherence. The remaining equality is the quotient chain-map identity already proved in step 2. The calculation is performed on evaluated maps and coherent homotopies supplied by the section model, rather than inferring equality of tower morphisms solely from evaluations.
8. Step 8 checks the scalar action from the compatible constant sections (R\to\Gamma(W_{\mathrm{proet}},B_W)). The K-injective Hom node supplies the bijection needed to pass the chain-level scalar identities through derived localization, and the linear-functor definition is exactly the additivity and scalar-compatibility conclusion. The scalar section and coefficient action are those in the item statement, so the (R)-linearity hypothesis is the only scalar hypothesis used.

The duplicate search found no blueprint node stating this coherent tower construction itself, and the Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch) found only generic restriction-of-scalars or derived-category declarations, never this varying-coefficient compact-support tower. The exact search commands and their returned results remain in the node's `mathlib_searches` field.

## What could not be finished

Nothing remains for this stage-1 split. The formal Lean declaration mentioned under Attachments remains sorried upstream and is intentionally not treated as completed evidence.
