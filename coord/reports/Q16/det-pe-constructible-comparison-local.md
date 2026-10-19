# Stage-1 report: det-pe-constructible-comparison-local

## Files written

- `dag/nodes/sec-proetale-coefficients/det-pe-constructible-comparison-local.json`: item split into four proof steps; no Mathlib match.
- `dag/nodes/sec-proetale-coefficients/lem-pe-site-sheaf-morphism-gluing.json`: statement-only node; no Mathlib match.
- `citations.json`: verbatim citations for the three non-elementary uses.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its blueprint tag, and the notions `classical`, `constructible comparison`, and pro-étale locality; no declaration states this item. The upstream master checkout was treated only as reference, as required.

## WANTED

None.

## Not duplicates

- `lem-pe-site-sheaf-morphism-gluing` vs `def-weil-pbc-torsor-associated-module`: the existing node defines the module attached to a torsor, while the new node states the general existence and uniqueness of a sheaf morphism glued from overlap-compatible local maps.

- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-site-module-sheaf-gluing`: the existing node glues module-sheaf objects from descent data, whereas the new node glues compatible morphisms between already-given sheaves.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-site-module-sheaf-gluing-aux`: the auxiliary constructs a compatible-tuples module sheaf and local isomorphisms; the new node is the mapping-property uniqueness/existence for maps between fixed sheaves.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-module-object-open-descent`: that node is for module sheaves on a ringed topological space and effective object descent; the new node is for sheaves on an arbitrary site and morphism gluing.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-scheme-morphism-gluing`: the existing Mathlib leaf glues morphisms of schemes, not morphisms of sheaves on a site.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-connected-torsor-module-descent`: that node concerns descent of a connected torsor representation and uses 04TR/04TS internally; it does not state the general sheaf morphism mapping property.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-module-descent-equivalence`: that node proves an equivalence for torsor module descent, not arbitrary compatible sheaf maps.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-associated-module-comparisons`: that node compares modules attached to torsors, not general sheaf morphism gluing.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-equivariant-module-recover-linear`: that node recovers linearity for equivariant torsor maps, not the site-level mapping property.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-graph-evaluation`: that node evaluates torsor graph sections; it does not glue arbitrary sheaf maps.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-ordinary-evaluation-equivariant`: that node is an equivariant ordinary-section calculation, not morphism gluing.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-associated-module`: that node defines an associated torsor module, not compatible-map gluing.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-invariant-sections`: that node identifies invariant sections, not sheaf morphisms.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-diagonal-evaluation-bijective`: that node proves a diagonal evaluation bijection for torsors, not the mapping property.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-associated-module-essential-image`: that node identifies an essential image of associated modules, not arbitrary sheaf maps.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-equivariant-module-is-sheaf`: that node proves an equivariant presheaf is a sheaf, not gluing morphisms.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-section-evaluation-bijective`: that node is a section-evaluation bijection, not map gluing.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-equivariant-presheaf-sheaf`: that node proves a particular equivariant presheaf satisfies the sheaf axiom, not the general mapping property.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-section-evaluation-local`: that node is local section evaluation for torsors, not compatible-map gluing.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-associated-module-full`: that node proves fullness for associated torsor modules, not arbitrary sheaf morphisms.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-diagonal-evaluation`: that node concerns diagonal section evaluation, not sheaf map descent.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-ordinary-evaluation`: that node evaluates ordinary torsor sections, not morphism gluing.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-normalized-graph-evaluation`: that node is a normalized torsor graph calculation, not the site mapping property.
- `lem-pe-site-sheaf-morphism-gluing` vs `lem-weil-pbc-torsor-equivariant-module-diagonal-evaluation`: that node proves a diagonal evaluation statement for equivariant modules, not general sheaf maps.

## Source and statement checks

The item source is `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-pe-constructible-comparison/sk-thm-pe-constructible-comparison-local.proof.md`; I read its complete proof and retained both directions of the statement. The imported item had no chapter/unit record in this overlay, so I followed its explicit blueprint source and did not invent a route outside that proof.

I checked the item against the slopmaster2 source by searching all `WeilConjectures/` files for the item id, the blueprint tag, and its central terminology. There is no declaration to attach, and no declaration with a finished proof was found. The master checkout was not used as evidence of completion.

The new node is the site-level mapping property corresponding to Stacks Tag 04TS. I read `literature/stacks-project/sites.tex` at the definition of glueing data and the mapping-property lemma, and checked that its module-linear addendum follows sectionwise from the same equality. The existing `lem-weil-pbc-site-module-sheaf-gluing` was read in full: its statement supplies effective gluing of module sheaf objects and compatible local isomorphisms, which is exactly the object-gluing input needed in step 3. I also read `det-pe-classical-sheaves-modules`; its statement explicitly supplies existence of étale models for classical module sheaves and full faithfulness of `nu_X^*`.

## Review by Q16

Step 1 is the converse direction. I checked that restriction to an open subscheme is the restriction of both sites and that inverse image is functorial under this restriction, so the step is elementary and uses no hidden theorem. The empty scheme and a one-open cover satisfy the same argument.

Step 2 is the overlap descent construction. I verified every hypothesis of `det-pe-classical-sheaves-modules`: each local restriction is a `Lambda_{X_a}`-module sheaf that is classical, so the node gives a `Lambda`-module sheaf `F_a` on `(X_a)_Et` and an isomorphism `alpha_a`. On `X_a cap X_b`, restriction of inverse image identifies the overlap comparison with a map between inverse images of the restricted `F_a` and `F_b`; the cited node says `nu^*` is fully faithful on module sheaves, so it gives a unique linear `phi_ab`. I checked the cocycle by applying `nu^*` and using faithfulness, and checked the diagonal identity by applying uniqueness to `alpha_a^{-1} alpha_a`.

Step 3 instantiates the existing generic site-module gluing theorem with the small étale site of `X`, the covering open immersions `X_a -> X`, the constant ring sheaf `Lambda`, and the overlap fibre products `X_a x_X X_b = X_ab`. The node's statement supplies exactly a global étale module sheaf `F_0`, local isomorphisms `e_a`, and the overlap equation; no proof detail from that node was used beyond its statement. This is recorded as an off-unit tool use because the generic gluing node belongs to the proper-base-change unit.

Step 4 defines local maps `beta_a = alpha_a` composed with the inverse image of `e_a`. I checked the overlap equality directly from the defining equation for `phi_ab` and the compatibility equation for `e_a`. The new 04TS node then glues these maps uniquely; its module clause gives `Lambda_X`-linearity. Applying the same argument to the local inverses glues an inverse, so the global map is an isomorphism and proves classicality. The local one-open and empty-cover edge cases reduce to the same construction, with no nontrivial cocycle.

Before writing the split I searched the whole DAG and blueprint for the item, the 04TR/04TS tags, and the keywords `glue sheaf`, `morphism gluing`, and `classicality local`. The existing object-gluing nodes were not duplicates because they glue objects or torsor-specific data rather than maps between fixed site sheaves. I ran LeanFinder, Loogle, grep, and LeanSearch for both the item and the new node; the recorded searches are in their JSON files, with unavailable/unknown-identifier responses preserved as such. I ran no compiler, Lake, or Lean build tool and wrote no Lean source.

## What was wrong or incomplete in the imported material

The imported proof cited `det-pe-classical-sheaves-modules` but left the non-elementary effective gluing of étale module sheaves and the final gluing of comparison morphisms implicit. I made the first explicit by citing the existing generic module-sheaf gluing node and the second by adding `lem-pe-site-sheaf-morphism-gluing`. I also removed the imported but unused `det-pe-classical-sheaves-unit` dependency and made the module node the item statement dependency.
The first dry run required the new node to carry explicit site/module definition citations and the imported item to retain `blueprint.from = null`; I added the bracketed definition citations, chapter/unit metadata inherited from the blueprint directory, and restored the imported blueprint metadata.

## What could not be finished

No unresolved mathematical or tool issue remains for this stage-1 split. The new morphism-gluing node is intentionally statement-only and joins the later queue.

## Second reading by Q16

- Item statement: checked against `sk-thm-pe-constructible-comparison-local.md`, hypothesis by hypothesis; the scheme, discrete commutative coefficient ring, pro-étale module sheaf, open cover, both locality directions, and empty/one-open-cover cases are retained.
- Step 1: the original converse started from the wrong premise (local classicality); repaired it to start from global classicality and its global étale model. Checked the first blueprint proof sentence against the two site-localization statements, the comparison presheaf-colimit formula, and the double-plus sheafification statement. The representative restriction along T ×_X U → T supplies both inverse colimit maps; identical covers/refinements supply the sheafification comparison. This step is now non-elementary with its actual inputs cited.
- Step 2: checked against the local-model and overlap-cocycle paragraph and the full statement of `det-pe-classical-sheaves-modules`; full faithfulness supplies the unique linear overlap maps, and faithfulness supplies diagonal and triple-overlap identities.
- Step 3: checked against the étale-sheaf gluing sentence, Tag 04TR (sites-lemma-glue-sheaves), and the full statement of `lem-weil-pbc-site-module-sheaf-gluing`; the final object X, slice identification, open cover, constant coefficient ring, set of cover indices, overlap fibre products, cocycle including repeated indices, and resulting linear isomorphisms match. Added the constant-ring restriction verification using the identical-cover double-plus argument from step 1.
- Step 4: checked against the final blueprint proof sentence, Tag 03EM (sites-modules-lemma-internal-hom), Tag 04TQ (sites-lemma-glue-maps), and the full statement of `lem-pur-sheaf-hom-cover-gluing`; wrote the actual overlap equation for β_a = β_b, cited the Zariski-cover clause of `sk-def-pe-site`, and instantiated module-map gluing with final object X and coefficients Λ_X. The inverse maps agree because equal isomorphisms have equal inverses, and unique gluing forces both inverse equations. The empty cover and singleton cover cases remain valid.
- Existing dependency `det-pe-classical-sheaves-modules`: reread its module-equivalence statement; it supplies exactly the local model, full faithfulness, and faithfulness used in step 2.
- Existing dependency `lem-weil-pbc-site-module-sheaf-gluing`: reread its Tag 04TR statement; it supplies object gluing, not morphism gluing, and is used only in step 3.
- Existing dependency `lem-pur-sheaf-hom-cover-gluing`: reread its Tag 03EM/04TQ statement and proof; it supplies the module-map gluing required in step 4.
- Removed node `lem-pe-site-sheaf-morphism-gluing`: found to duplicate the module-map clause of `lem-pur-sheaf-hom-cover-gluing` for this item's actual use, so it was deleted and step 4 now cites the existing reviewed node.

I read the Stacks source at Tags 04TR/04TS (sites-lemma-glue-sheaves / sites-lemma-mapping-property-glue), 04TQ (sites-lemma-glue-maps), 03EM (sites-modules-lemma-internal-hom), and the plus-construction theorem 00WB. The item statement equals the current main-20261015 blueprint statement; no disputed statement or target correction is needed. On a field every nonempty Zariski cover includes the point, and the argument reduces to its étale model; for the zero sheaf every map is the unique zero map; for the empty scheme the empty cover forces unique sections and unique module maps, so the same construction is valid. No quasi-compactness, Noetherian, finite-ring or separation hypothesis was added.

Changes: removed the duplicate new node and replaced it by the already reviewed module-map gluing node; corrected step 1's premise and made its comparison restriction argument explicit; expanded the coefficient restriction and final overlap/inverse equations; updated `proof_deps`, the split summary and tool explanations, and regenerated `citations.json` with an exact statement quote for every dependency at every actual citation. The earlier worker sections above are retained as history; the final delivery creates **zero new nodes and zero Mathlib leaves**. All cited inputs were opened, and a dependency traversal of the repaired overlay found 353 reachable nodes and no cycle.

The generic tools from other units are the étale/pro-étale site-localization statements and the double-plus theorem for step 1, object descent for step 3, and module-map descent for step 4. They justify precisely the blueprint's restriction and gluing sentences; no different unit route is substituted, and no maintainer-owned top-level `tool_uses` field was written. The module equivalence remains the same-unit mathematical input.

I independently ran the more general LeanFinder query “maps of sheaves glue uniquely over a covering site”, a Loogle search for `"sheafHom"`, and a source grep for `presheafHom_isSheaf|sheafHom|amalgamate_map`, recorded by msearch.py in `searches.jsonl`. The semantic hits concern section amalgamation and local extensionality; the module-map theorem already exists in the DAG, so no Mathlib leaf or replacement node is introduced. The earlier natural-language Loogle query returned a parse error and gives no evidence of a match or non-match. No Lean, Lake, compiler, or build tool was run.

The first worker’s Loogle unknown-identifier result and doubled-Mathlib grep directory were inconclusive, so I corrected their verdicts and recorded the actual second-reader queries and results on the item. This changes no statement or proof route.

Validation: the repaired split passed deliver.py --no-push preflight at 6382b20633. The first push then caught a concurrent update to `sk-def-pe-site` (an explicit scheme-definition citation and an fpqc-definition reference were added). I reread the updated statement; its Zariski-cover clause is unchanged and still proves step 4. I refreshed that citation to quote precisely this stable clause and reran delivery checks.
