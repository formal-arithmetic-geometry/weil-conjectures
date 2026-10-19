# Worker report

## Files written

- `dag/nodes/sec-zeta-weil/lem-zl-generic-fiber-components-section.json`: item split into seven steps; statement unchanged. Mathlib searches find component topology and discrete constant-sheaf results, not the full theorem.
- `dag/nodes/sec-zeta-weil/lem-zl-affine-component-site-projection.json`: one new statement-only, unsplit node; no Mathlib match after two LeanFinder phrasings, Loogle, LeanSearch and source grep.
- `citations.json`: verbatim statement quotations for all 26 step/node citations.

## Attachments

None. No declaration for the item tag or full notion was found under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/`. Searches of the algebraic-geometry, pro-etale and topology source find component topology and ind-etale interfaces, not this diagram or its coefficient-compatible topos equivalence. No Lean was written or compiled.

## WANTED

None. Both Hemo–Richarz–Scholbach and Bhatt–Scholze PDFs and the Stacks sources needed here are present and were read locally.

## Problems found

The item statement agrees with Hemo–Richarz–Scholbach Theorem 4.13, irreducible case, diagram (4.4). Its extra assertions about module derived categories and constant scalar realization are consequences of that geometric equivalence, proved explicitly in step 7. No correction of the item statement or unit route was needed. The blueprint ancestor remains `prop-zl-smooth-proper-relative-purity`, through the three recorded intermediate nodes; this item supplies the generic-fibre argument used by its condensed-lisse input.

An unused existing node, `lem-weil-pbc-flat-generalizations-lift`, reverses the specialization direction. Its statement says flat maps lift specializations. This is false for the flat map Spec k(t) -> Spec k[t]: the generic point specializes to (t), but the source has no point over (t). Stacks 03HV, `morphisms.tex`, `lemma-generalizations-lift-flat`, says GENERALIZATIONS lift. I have not edited that other worker's node. Step 2 instead cites the existing correct `lem-sc-flat-going-down` (Stacks 00HS, `algebra.tex`, `lemma-flat-going-down`) and spells out the relevant prime inclusions.

## Not duplicates

lem-zl-affine-component-site-projection vs lem-zl-condensed-wcontractible-lisse-evaluation: the existing node constructs a component map only for w-contractible affine schemes and asserts an equivalence on dualizable complexes. The new node treats every affine scheme and arbitrary sheaves of sets on its component site, with the inverse-image formula on qcqs objects. It does not assert the item's generic-fibre surjectivity, section, or topos equivalence.

lem-zl-affine-component-site-projection vs lem-weil-pbc-condensed-point-basis-evaluation: the existing node evaluates coefficients pulled back from the absolute profinite point only on weakly contractible objects. The new node concerns arbitrary sheaves on the RELATIVE profinite site over pi_0(T), for any affine T, evaluated on all qcqs pro-etale W.

lem-zl-affine-component-site-projection vs lem-weil-pbc-proetale-point-components-maps: the existing node is a Hom/test-object bijection for weakly contractible objects, not a morphism of relative component topoi or its inverse-image formula.

The whole DAG was searched by `4.2.13`, component/topos/site phrases, and by `03H4`, `03HV`, and going-down for the existing tools. Whole-blueprint searches included `components`, `profinite`, `connected component`, `component projection`, `component map`, `generalizations`, `slice topos`, and `4.2.13`. No blueprint node states the new general comparison. The new node uses a Bhatt–Scholze source, not a Stacks tag shared with another node. Candidate Mathlib `continuousMapPresheafEquivOfTotallyDisconnectedSpace`, read at Mathlib/AlgebraicGeometry/Sites/ConstantSheaf.lean:90–99, concerns continuous functions with a totally disconnected target; it does not supply the component-site geometric morphism. Loogle's connectedComponentsHomeomorph requires an open geometrically connected morphism, hypotheses unavailable here and a different conclusion.

## Review by Q41

I read the chapter and unit records, the unchanged item's statement, Hemo–Richarz–Scholbach's printed page 12 (Theorem 4.13 and diagram (4.4)), Bhatt–Scholze's Lemma 2.2.8 on printed page 10 and the paragraph preceding Lemma 4.2.13 plus its proof on printed pages 30–31. The new node is precisely their general affine component projection and evaluation formula, with algebraic operations transported by finite products. It remains a statement only, without a proof sketch in its statement or proof dependencies. The item is not replaced by a renamed clause: its seven steps carry the prime argument, splitting, square, basis equivalence, coefficient identification, and derived transport.

Step 1 uses exactly the affine tensor-product fibre identification in `lem-weil-pbc-fibre-product-affine-spectra`, base-change stability in `lem-weil-pbc-ind-etale-stability`, affine qcqs in `lem-weil-pbc-affine-scheme-qcqs`, spectrality in `lem-weil-pbc-qcqs-scheme-spectral`, and profiniteness in `lem-pe-spectral-components-profinite`. I checked all five statements. All schemes to which these are applied are affine. Continuity of the induced component map follows directly by composing with the quotient projection, so no general topos statement is smuggled into this step.

Step 2 uses weak etaleness from the stability statement and flatness from the actual ring definition, not a flatness preservation theorem inferred from a definition. I checked Stacks 00HS: p_0 is contained in p, and q_0 is contained in q, with contractions as required. The closure of the point q_0 is connected and contains q, which explains why the lift stays in the component. I read the cited `lem-a1-space-fibre-product-point` and Stacks 03H4, `spaces-properties.tex`, `lemma-points-cartesian`: schemes are allowed as the algebraic-space base and their points over the same base point lift to a fibre-product point. No claim that |V| -> |U| is surjective is made. The step obtains only surjectivity on components.

Step 3 reads extremal disconnectedness directly from the definition `sk-def-pe-wlocal` and uses the precise continuous-section theorem `lem-weil-pbc-extremally-disconnected-component-section`. Both spaces are compact Hausdorff by step 1; the target S, rather than the source S_eta, is the extremally disconnected space. No claim that V is w-contractible is needed.

Step 4 uses the new node's explicit locally ringed-space construction. The natural comparison is written on points (v,e) and on structure sheaves, so it proves the square rather than appealing to unnamed functoriality. This finite-limit associativity calculation is the one elementary step. The morphism on profinite sites is induced by E -> E x_S S_eta, with the correct direction for geometric inverse image.

Step 5 uses all three clauses of `det-pe-condensed-point-basis`, the homeomorphism in `lem-weil-pbc-locally-constant-prime-spectrum`, the actual basis/refinement and sheaf-detection assertions in `lem-weil-pbc-ind-etale-basis`, and both composition and maps-between-ind-etale-algebras clauses of `lem-weil-pbc-ind-etale-stability`. The small pro-etale site definition supplies the covering criterion, and `lem-weil-pbc-site-equivalence-is-morphism-of-sites` supplies sheaf equivalence for the covering-preserving equivalence. These statements were opened, not inferred from their titles. In particular, arbitrary maps of profinite sets, not only finite locally constant maps, give arrows; finite jointly surjective families are fpqc covers of affine schemes. Affineness of V is established before applying the basis theorem. The ind-etale classification needs only a separably closed field, so the algebraically closed Omega in the item suffices.

Step 6 uses the new node's actual evaluation formula to identify the equivalence with the specified pi_V. `lem-weil-pbc-geometric-field-proetale-evaluation` identifies the absolute geometric field site with the profinite point. The equality with the profinite structure morphism is checked on Omega[E] using the explicit base-change functor in `def-weil-proetale-inverse-image`: it sends E to S_eta x E, with its projection to S_eta. This pins down the direction of the geometric morphism. The test-object description in `sk-def-sfb-pullback-from-point` and the definition `sk-def-sfb-pulled-back-coefficients` then identify the same pullback of every condensed ring on both sides. This retains all condensed coefficients; it makes no finite/discrete or flat-coefficient reduction.

Step 7 uses clause (2) of `lem-weil-pbc-equivalence-injective-resolutions` only for exactness of the resulting additive module equivalence. It does NOT use bounded-below resolutions to claim the unbounded result. Instead the termwise inverse equivalences preserve cohomology and quasi-isomorphisms, and their unit/counit descend to the localization. `def-sfb-site-derived-constant-module-functor` explicitly defines discrete constant realization by this termwise construction. The tensor isomorphism is exactly the statement of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, which allows arbitrary complexes and structural ring maps. The constant scalar map is tracked on each scalar a. Thus every non-elementary tensor fact has a cited statement, and no boundedness or coefficient flatness hypothesis has been added.

I checked empty U (both component spaces empty and their section unique), X a field, a nonreduced irreducible affine X (use its generic prime, not an integral-domain assumption), and an arbitrary algebraically closed Omega extending the generic residue field. For the new general node, T empty and E empty yield the empty relative site construction; E=P gives T itself; finite E pulled back from a finite set gives exactly the finite clopen subdivision construction. General affine T need not be w-contractible or reduced. All seven steps are under 2000 characters; the derived localization and relative basis identification are spelled out rather than hidden as 'standard'. All external proof tools are declared in split_report.tool_uses; their purposes are generic tools within the HRS argument, not replacements of unit-level steps. No SGA source is used.

## Unfinished work

Only the new general affine component-site projection node is left unsplit, as required by one-level splitting. No unresolved claim in the item's proof is left uncited.
