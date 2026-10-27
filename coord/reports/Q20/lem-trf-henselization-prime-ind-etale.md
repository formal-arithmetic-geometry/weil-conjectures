# Q20 stage-1 repair: lem-trf-henselization-prime-ind-etale

## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-henselization-prime-ind-etale.json`: unchanged statement, three-step assembly (1245 characters).
- `dag/nodes/sec-trace-formula/lem-trf-prime-pair-colimit-ind-etale-model.json`: new statement-only construction lemma, status `unsplit`, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-initial-henselian-colimit-comparison.json`: new statement-only comparison and cocone lemma, status `unsplit`, no Mathlib match.
- `report.md`, delivered as `coord/reports/Q20/lem-trf-henselization-prime-ind-etale.md`. Sandbox-only validation inputs: `citations.json`, `searches.jsonl`.

Attachments: none. The exact blueprint tag and declaration name do not occur under `lean/WeilConjectures/`; concept searches found the existing pair-henselization and mapping tools, not a project theorem of this item or either new helper. `lean/Sheaf/TraceFormula/HenselizationPrimeIndEtale.lean` still ends its theorem with `sorry`, so it is not an attachment. No Lean was changed, and no compiler, Lake, global build, git command in the read repository, launcher edit, or subagent was used.

WANTED: none for this repair. The historical Q84 report requested Hübner–Schmidt for motivation only; that document remains unnecessary for this Stacks proof.

## Repair of the return

The dedicated handoff names returned head `e2a95534abdca96856ae1c3b80c5b78fb624dc06`. Contrary to the generic repair preamble, the supplied sandbox contained only four dispatcher marker files and no node, report or search log. I copied the live item and preserved the live Q84 report locally before editing. The seven live proof paragraphs have exactly the lengths quoted in the return: 638, 826, 607, 748, 758, 887, 295. Thus the readable live proof is the returned 4759-character baseline. No previous sandbox work was overwritten. The original item searches and all non-stage-1 metadata remain unchanged; the delivery tool overlays the repair on current server main.

The return has one substantive instruction: distribute the proof among at least two comparable new unsplit statements, keeping the item's statement and at most 3000 characters of assembly. The construction helper takes old Steps 1–3 plus the composition calculation of old Step 7 (2366 characters of original work). It constructs the particular pair-colimit over the prime localization, with its local structure, residue identification, and both relative and original-base ind-etaleness. The comparison helper takes old Steps 4–6 (2393 characters): constructing both maps with different universal properties, proving the inverse identities without presupposing the residue field of H, and transferring the full specified colimit cocone. The helpers are independent queue items: neither cites the other or the parent, neither has proof steps or proof dependencies, and neither states the full assertion for an arbitrary henselization at a prime. The item uses both contracts to assemble its conclusion.

All seven original paragraphs are preserved verbatim below with an explicit assignment. This is an extraction into two work items, not a shortened substitute for the original argument. No mathematical defect or statement dispute was found. Nothing remains unfinished in the requested stage-1 extraction; the new helper proofs are deliberately future work.

## Review by Q20

I read the node, its Lean statement and sorry, `GOAL.md`, the trace-formula chapter, `sk-i-curve-zero`, and the current `blueprint_update` of `lem-trf-local-term-locality`. The ancestor now follows contracting correspondences; this item is an existing historical auxiliary branch. I retained that ancestry and route and did not change the ancestor, unit, chapter, or any target. The new nodes' `blueprint.from.node` is the ancestor printed by `blueprint_refs.py ancestor`; their via lists insert this item before its previous via chain. Their places specify exactly which old auxiliary proof paragraphs they carry. Blueprint searches for henselization, pair-henselization, 08HR, 0A03, and henselian colimits did not give an imported node stating either helper. The broad localization search returned other uses of localization, none stating the construction or comparison.

For the item source I read Stacks `algebra.tex` Tag 04GN (`lemma-henselization`), including all four conclusions and its pointed etale colimit, and Tag 04GQ (`definition-henselization`). These describe the ordinary henselization, but the given H is characterized only by the universal property in `def-weil-pbc-henselization-at-prime`. The new comparison lemma is precisely what connects that arbitrary H to a constructed colimit. Neither the item nor the helpers silently assumes H already has an etale presentation or the residue field k.

For the model helper I read `more-algebra.tex` Tags 0A02 (`lemma-henselization`, the construction and proof) and 0A03 (`lemma-henselization-local-ring`, the locality and identification). I also read `algebra.tex` Tag 00CR (`lemma-localization-colimit`) and `proetale.tex` Tag 097K (`lemma-composition-ind-etale`), as well as the retained cited finite-presentation/localization node. The category in the statement is exactly the pair-neighborhood category, not the category of local algebras and not a strict-henselization category. The existing pair theorem supplies essential smallness, filteredness, a ring-colimit with henselian pair (C,mC), and the structural quotient isomorphism. The skeleton makes the diagram small. The model helper additionally has to prove C local, the structure map local, that its ring cocone is also universal as an R-algebra cocone, and ind-etaleness over the original A. Those assertions are part of its statement, not facts borrowed from the proof of a definition. Its first source is not claimed to state the entire strengthened original-base formulation verbatim: the report records the localization and composition arguments extracted with it.

The locality argument remains exactly the old finite quotient argument: for z in J, D=C/(1-z) is finite cyclic even over a non-Noetherian C; JD=D forces D/JD=0, and the two idempotents 0 and 1 have the same reduction. The unique lifting in `def-weil-pbc-henselian-terminology` forces D=0 and 1-z invertible. Since C/J is the nonzero field k, an element outside J is a unit, and eta_C contracts J to m. These are the previously established local structure and residue data now assigned to the construction worker. The R-algebra universality of the ring colimit uses a stage of the nonempty diagram: u eta_C = u iota_i eta_i = mu_i eta_i. No Noetherianity or finite presentation of the whole localization A_p is asserted.

For the comparison helper I read `algebra.tex` Tag 08HR (`lemma-map-into-henselian-colimit`) and its existence and uniqueness conditions, and `categories.tex` Tag 002F (`definition-colimit`). The source C is an ind-etale R-algebra, hence a filtered etale colimit. Its maximal ideal contracts to m because eta_C is local; the same holds for eta_H. The prescribed residue map is e_H composed with e_C inverse, a k-algebra map, even though e_H is not assumed invertible. Tag 08HR produces f. Initiality of H produces g since C is henselian local. The residue of gf is identity because it agrees with identity after the isomorphism e_C; Tag 08HR uniqueness gives gf=id_C. Initiality of H gives fg=id_H separately. Any local R-map out of C induces the same forced residue map, so the stated uniqueness of f is justified, not just uniqueness after an unspecified residue choice.

The comparison helper's arbitrary base P clause is the full old cocone calculation, applied along P to R. It asserts ring universality and P-algebra universality, not just existence of a bare isomorphism. For a compatible ring cocone mu_i, take its unique mediator u:C to T and use ug. The equations (ug)(f lambda_i)=mu_i and vf=u imply the existence and uniqueness conditions. If the cocone is over P, any stage of the nonempty filtered index gives u eta_C=eta_T, now for the P-structure, so the mediator is P-linear. This uses no etaleness property of the D_i until the final ind-etale consequence; etaleness and finite presentation are explicit hypotheses there. The stronger P formulation keeps the original-base A presentation from the model helper rather than identifying maps only abstractly.

For new item Step 1 I opened the model helper statement: its hypotheses are A commutative and p prime, exactly those available. It explicitly gives a local henselian C, the structural isomorphism on residue fields, and both ind-etale maps that Step 2 needs. Step 1 does not read any future proof of that helper.

For new item Step 2 I opened `def-weil-pbc-henselization-at-prime`: it explicitly says H is henselian local, its structure map is local, and every local map R to a henselian local T factors uniquely through H. I checked these are exactly the hypotheses of the comparison helper, whose statement supplies both inverse maps and the cocone clause over any P. I opened `def-weil-pbc-ind-etale-algebra`: its filtered finitely presented etale presentation is what is selected for A to C, and setting P=A in the helper transfers precisely that presentation to the actual H. There is no assumption that the diagram over A already has an R-algebra structure at each stage.

For new item Step 3 I reread the ind-etale definition. Its definition applies immediately to the same small filtered diagram and transferred cocone. R-linearity of f means f eta_C=eta_H, so the induced A-map is the canonical composite in the unchanged statement. This final step is elementary assembly from the earlier isomorphism and the cited definition. All non-elementary statements used in the item are actual cited node statements, with every step/node quotation in `citations.json` and reproduced below. The parent proof dependency list is exactly the union of the proof-step uses.

I checked delivery-errors B–E against both new files. Each introduces all rings, maps, ideals, categories and structural isomorphisms. Every non-basic notion has an existing definition citation; local homomorphism is also defined inline in the comparison statement. The model explicitly cites the existing pair construction for its chosen C, so this is a statement dependency rather than an untracked pointer to somebody's proof. TeX is escaped once in decoded strings. Both nodes have empty proof, empty proof_deps, null proof_origin, `unsplit` status, and actual three-kind Mathlib records including a second semantic phrasing. No invented proof sketch was put inside their statements. Existing definitions and existing pair/map/localization/stability nodes are retained, not duplicated by one helper per old clause. No node depends on its parent, and no current unit route is replaced.

The actual search hits were read: Mathlib `Algebra.Etale.of_isLocalizationAway` in `RingTheory/Etale/Basic.lean:252` is only the single principal localization result; `Algebra.FormallyEtale.of_isLocalization` at line 179 is formal etaleness, not ind-etale construction. `RingHom.Etale.ofLocalizationSpanTarget` in `RingTheory/RingHom/Etale.lean:73` is a locality-of-property lemma (its semantic search prose was misleading), not etaleness of an arbitrary localization. `HenselianLocalRing` and `HenselianLocalRing.TFAE` in `RingTheory/Henselian.lean:108,119` express root lifting for an already given local ring. `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime` in `RingTheory/Polynomial/UniversalFactorizationRing.lean:694` constructs a single factorization-lifting neighborhood. `StandardEtalePair.homEquiv` and `hom_ext` concern a single standard-etale algebra. None states either helper or a one-line specialization of it. The search logs preserve the actual query text, hit names and digests. The original item's 2026-10-18 searches are preserved unchanged; new log entries are not retroactively attributed to that earlier search.

Small cases: when A is a field, p=0, R=A and the closed-fiber condition forces each B_i to be structurally A; C=A and the comparison reduces to the identity over A. When R is already henselian local, its identity local map is initial, and the inverse-map argument forces C and H to be R over the specified maps. Nonreduced and non-Noetherian local rings still admit the same cyclic-quotient locality argument. A zero ring has no prime, so does not supply a spurious instance of the model. The comparison statement has genuine local rings with proper maximal ideals; a zero target is excluded by those hypotheses. Empty diagrams are excluded by filteredness; the P-algebra mediator computation always has a stage. No separable closure, algebraic closure, finite-dimensionality or Noetherianity is used.

What was corrected is the allocation of work: the formerly monolithic item has become two similar-sized unsplit statements and a short assembly. The original local-ind-etale prerequisite criticized in the prior Q84 repair has not been revived: the new construction helper explicitly retains the existing general pair theorem and additionally assembles the original-base localization and composition work. The comparison helper is generic for an arbitrary C and an independent presentation base P, not restricted to that pair construction. The original complete argument and the prior report are retained in the sandbox for continuity.

## Not duplicates

The following compares all nonmerged nodes sharing any source tag, rather than only the first twelve printed by the delivery tool. The near mathematical matches are discussed explicitly; shared-source neighbors with different mathematical objects are identified by their actual scope.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux: the existing statement concerns Existence of an epimorphic pointed affine model for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-cocone-restriction: the existing statement concerns Unique restriction of a local cocone across prime localization for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-def-sbc-etale-triples-prime-localization-cocone-relation: the existing statement concerns Compatible cocone legs across prime localization for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-comparison: the existing statement concerns Ring-colimit comparison across prime localization with fixed algebra structures for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model-pointing: the existing statement concerns Affine model pointing compatibility for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-cocone-equiv: the existing statement concerns Natural equivalence of pointed-etale cocones across prime localization for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux: the existing statement concerns Affine model and factorization data for a component extension for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-cocone-extension: the existing statement concerns Unique extension of a global cocone across prime localization for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique: the existing statement concerns Uniqueness of a compatible local component leg for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-compatible: the existing statement concerns Existence of a compatible descended affine model for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-component-extension: the existing statement concerns A unique compatible leg on one local pointed etale triple for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-factorization: the existing statement concerns Cocone-leg extension and morphism factorization for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-component-extension-exists: the existing statement concerns Existence of a compatible local component leg for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model: the existing statement concerns Affine model data for component extension for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-sbc-depth-three-completed-quotient-lift: the existing statement is an algebraization/lifting theorem for finite etale algebras away from a completed local closed subset under depth hypotheses; the new model has no completion, depth, or punctured cover.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-epi: the existing statement concerns The descended compatible map is an epimorphism for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model-structure: the existing statement concerns Affine model structure descent for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs new-lem-sbc-prime-localization-etale-algebra-model: the existing statement concerns Unpointed etale algebra model at a prime for pointed etale triples and their field-valued evaluations across localization; the new model is the maximal-ideal pair-colimit with no auxiliary field pointing, with henselian locality and original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-trf-normal-tensor-component-join-model: the existing statement concerns normal-domain tensor products of two arbitrary henselizations and component embeddings in a separable closure; it does not construct the single pair-colimit model and depends on the present item, so it is not a usable proof shortcut.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-trf-component-ind-etale-local-henselian: the existing result concerns quotient component rings T_Z and their local henselian structures; the new model constructs a pair-colimit at a prime, without a connected component or component quotient.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-sfb-snc-universal-residual-charts: the existing theorem constructs special regular SNC residual charts with parameter-root towers and finite-etale covers; the new model works for every prime of an arbitrary ring with no regularity or SNC data.

- lem-trf-prime-pair-colimit-ind-etale-model vs def-sfb-snc-residual-chart-data: the existing node defines SNC residual-chart packages and does not assert the arbitrary-prime model construction.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-sc-bounded-free-stalk-complex-local-lift: the existing statement concerns Spreading standard finite free stalk differential matrices to an affine open for complexes of sheaves, stalks and restriction to open neighborhoods; the new model concerns rings and henselian pair-colimits, not complexes or derived morphisms.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-sc-bounded-free-stalk-complex-lift: the existing statement concerns Lifting a bounded free stalk complex without a derived comparison for complexes of sheaves, stalks and restriction to open neighborhoods; the new model concerns rings and henselian pair-colimits, not complexes or derived morphisms.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-sc-perfect-stalk-quasi-iso-detection: the existing statement concerns Detecting a quasi-isomorphism of perfect complexes on a neighbourhood for complexes of sheaves, stalks and restriction to open neighborhoods; the new model concerns rings and henselian pair-colimits, not complexes or derived morphisms.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-sc-perfect-open-stalk-derived-hom-descent: the existing statement concerns Descent of derived Hom between open strictly perfect stalks for complexes of sheaves, stalks and restriction to open neighborhoods; the new model concerns rings and henselian pair-colimits, not complexes or derived morphisms.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-sc-perfect-stalk-derived-hom-lift: the existing statement concerns Lifting a derived stalk morphism to a local chain map for complexes of sheaves, stalks and restriction to open neighborhoods; the new model concerns rings and henselian pair-colimits, not complexes or derived morphisms.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-sc-perfect-stalk-derived-iso-spread: the existing statement concerns Extending a derived stalk isomorphism between existing perfect models for complexes of sheaves, stalks and restriction to open neighborhoods; the new model concerns rings and henselian pair-colimits, not complexes or derived morphisms.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-per-local-pair-henselization-comparison: the existing result identifies the pair-henselization with the ordinary henselization over a local base R; the new model does not assert initiality or identify an arbitrary H, and adds ind-etaleness over the earlier original ring A using the principal-localization diagram and composition. Neither statement is a one-line specialization of the other.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-factors-through-localization-of-smooth: the existing theorem factors a finitely presented algebra map through a single principal localization; it does not construct a henselian pair-colimit.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-pair-henselization-sections: the existing statement supplies lifting of sections for an etale algebra over a pair-colimit; the new model is a local-ring and original-base ind-etale construction.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-localization-of-localization: the existing theorem describes a composite localization and nested denominator sets; the new model is a henselian local pair-colimit, not another localization identity.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-henselization-stage-map: the existing statement factors a map from one etale pair neighborhood into a henselian pair; it does not construct a local colimit or prove original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-localization-colimit-principal-localizations: the existing result is the general principal-localization colimit, used as a tool in the retained construction argument; it supplies no henselian pair-colimit or local model.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-henselization-colimit: the existing statement commutes henselization with a directed system of pairs; the new model uses one maximal-ideal pair over one prime localization and asserts original-base ind-etaleness.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-etale-section-idempotent-splitting: the existing statement concerns A section of an etale algebra splits off a factor for an etale algebra with a section or a refinement; it does not give a local henselian pair-colimit ind-etale over the original A.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-etale-section-neighbourhood-refinement: the existing statement concerns Refining a quotient section to an etale pair neighbourhood for an etale algebra with a section or a refinement; it does not give a local henselian pair-colimit ind-etale over the original A.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-smooth-over-essentially-smooth-base: the existing statement represents an essentially smooth composite as a localization of a smooth algebra; no arbitrary-prime henselian pair-colimit is asserted.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-pair-henselization-colimit: the existing statement gives a colimit cocone and henselian pair for any (B,J); the new model additionally proves locality, localness of the structural map, and ind-etaleness from the original A.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-etale-section-idempotent-splitting-core: the existing statement concerns Core idempotent decomposition for an etale algebra with a section or a refinement; it does not give a local henselian pair-colimit ind-etale over the original A.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-pair-henselization-essentially-small: the existing statement only gives essential smallness of the general pair category; the new model includes the local henselian colimit and the two-base ind-etale conclusions.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-pair-henselization-stage-sections: the existing statement lifts a section at a stage of a cocone with a quotient bijection, even without colimit universality; it does not establish the local henselian original-base model.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-affine-closed-henselian-neighborhood-colimit: the existing statement realizes cohomology of an affine closed immersion using henselian neighborhoods, etale sheaves and diagrams of abelian groups; it does not construct the arbitrary-prime ring model of this helper.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-pair-henselization-filtered: the existing statement gives filteredness of the pair category only; it supplies no local henselian vertex or original-base ind-etale conclusion.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-etale-section-localization: the existing statement concerns Localization equivalence from an idempotent kernel for an etale algebra with a section or a refinement; it does not give a local henselian pair-colimit ind-etale over the original A.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-henselization-universal-property: the existing result gives factorization through a specified pair-henselization to a henselian pair; it does not give local-ring structure or the original A-ind-etale construction.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-etale-algebra-filtered-colimit-descent: the existing theorem descends an etale algebra over a colimit to some stage; the new model constructs a henselian local vertex and proves the original-base structure map ind-etale.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-weil-pbc-pair-henselization: the existing theorem gives the general pair construction, its henselian ideal and quotient, but does not prove its ring is local or the map from a pre-localization ring A ind-etale. It is a statement dependency of the new model, not a replacement for that theorem.

- lem-trf-initial-henselian-colimit-comparison vs lem-sfb-diagonal-tensor-colimit-hom-ext: the existing result detects equality via diagonal tensor colimit legs in a monoidal category; it does not compare local algebras or preserve their ring cocones.

- lem-trf-initial-henselian-colimit-comparison vs def-coef-bounded-filtered-subcategory-system: the existing node defines a system of bounded subcategories and its comparison map; it gives no initial-henselian-local isomorphism.

- lem-trf-initial-henselian-colimit-comparison vs lem-coef-ordinary-directed-cover-colimit: the existing theorem assembles colimits over a directed cover of an index category; it does not supply the isomorphism C to an initial henselian local algebra required here.

- lem-trf-initial-henselian-colimit-comparison vs lem-coef-small-direct-colimit-lifting: the existing theorem proves closure of a lifting class using relative latching maps over a direct category; it neither concerns henselian algebras nor gives the comparison isomorphism.

- lem-trf-initial-henselian-colimit-comparison vs lem-weil-pbc-filtered-colimit-algebras-elementwise: the existing statement compares algebra and ring colimits and gives element representatives; it neither constructs inverse maps to an initial henselian algebra nor transfers a colimit to it.

- lem-trf-initial-henselian-colimit-comparison vs lem-weil-pbc-strict-henselization-map-exists: the existing statement gives existence, without uniqueness, of a compatible strict-henselization map for schemes and separable closures; the new helper concerns ordinary initial local algebras, inverse identities, and arbitrary-base colimit cocones.

- lem-trf-initial-henselian-colimit-comparison vs def-weil-pbc-filtered-colimit-smooth-algebras: the existing node defines a filtered smooth algebra presentation; it supplies no comparison of henselian local algebras or transported cocone theorem.

- lem-trf-initial-henselian-colimit-comparison vs def-weil-pbc-category-colimit: the existing node defines colimit cocones and their universal property; it does not assert the henselian-local comparison theorem.

- lem-trf-initial-henselian-colimit-comparison vs lem-weil-pbc-map-into-henselian-colimit: the existing mapping theorem gives one map from an etale colimit with specified contraction and residue map; the new helper combines it with an independent initial H to prove both inverse identities and transfer every cocone over an arbitrary P.

- lem-trf-initial-henselian-colimit-comparison vs def-galois-finite-limits-colimits: the existing node defines finite diagrams and finite limits/colimits; the new helper uses possibly infinite filtered etale diagrams and proves a comparison theorem.

- lem-trf-initial-henselian-colimit-comparison vs lem-per-local-pair-henselization-comparison: the existing theorem concerns the particular pair-henselization; the new helper allows any ind-etale henselian local C with structural residue isomorphism and proves all cocone transfers over any earlier base P. The existing theorem does not provide that general two-base cocone contract.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-per-ordinary-henselian-pointed-neighbourhood-limit: the existing existence statement uses a directed system of pointed etale A-neighborhoods, not the specified whole pair-neighborhood colimit over R, and does not state its simultaneous R-algebra colimit property. Identifying these constructions is separate work.

- lem-trf-initial-henselian-colimit-comparison vs lem-per-pointed-etale-limit-henselization: the existing statement assumes a directed presentation by pointed etale A-algebras with chosen compatible residue pointings; the new statement starts with local R-algebras, ind-etaleness and a single structural residue isomorphism, and additionally transfers every presentation over any P. It neither assumes those pointings nor requires H to have any presentation.

- lem-trf-prime-pair-colimit-ind-etale-model vs lem-trf-henselization-prime-ind-etale: the new statement constructs a fixed C from its pair-neighborhood diagram, with locality and residue data, and makes no assertion for an arbitrary initial H. The item needs the independent comparison lemma to reach that arbitrary H.

- lem-trf-initial-henselian-colimit-comparison vs lem-trf-henselization-prime-ind-etale: the new statement assumes a suitable concrete local ind-etale C already exists and proves its comparison with initial H and cocone transfer. It does not construct C for A_p or establish the original A-ind-etale map needed by the item.

## Original argument assigned to the new work items

These are the complete former proof paragraphs, retained verbatim as future-worker handoff material. They are not proof steps of the new unsplit nodes. The model takes original Steps 1–3; its original-base conclusion uses the same composition calculation as Step 7 with H there replaced by its constructed C. The comparison takes original Steps 4–6 and states the cocone transfer for arbitrary presentation base P, so its P=A instance also applies to the presentation already produced over A.

### Original step 1 → lem-trf-prime-pair-colimit-ind-etale-model

Set $R=A_{\mathfrak p}$ and $S=A\setminus\mathfrak p$. Since $\mathfrak p$ is prime, $1\in S$ and $s,t\in S$ imply $st\in S$. Apply [lem-weil-pbc-localization-colimit-principal-localizations] with $P=A$: $R$ is the filtered colimit of $A_s$, indexed by the small divisibility preorder on $S$, with its canonical structural map from $A$. Apply clause (2) of [lem-weil-pbc-etale-algebra-finite-presentation-localization] to the identity etale map $A\to A$ to see that $A\to A_s$ is etale, and then clause (1), now to $A\to A_s$, to see that each $A_s$ has finite presentation. Thus $A\to R$ is ind-etale by [def-weil-pbc-ind-etale-algebra].

Existing statements used: lem-weil-pbc-localization-colimit-principal-localizations, lem-weil-pbc-etale-algebra-finite-presentation-localization, def-weil-pbc-ind-etale-algebra.

### Original step 2 → lem-trf-prime-pair-colimit-ind-etale-model

Put $\mathfrak m=\mathfrak pR$ and $k=R/\mathfrak m$. The ring $R$ is local: a fraction $a/s$ outside $\mathfrak pR$ has $a\notin\mathfrak p$, and then $s/a$ is its inverse; $\mathfrak pR$ is proper since a prime contains no denominator in $S$. Apply [lem-weil-pbc-pair-henselization] to $(R,\mathfrak m)$. Its category of etale $R$-algebras $B$ with $k\xrightarrow{\sim}B/\mathfrak mB$ is essentially small and filtered; take a small skeleton for the stated colimit and denote the diagram by $(B_i)$ and its colimit coprojections by $\iota_i:B_i\to C$. This gives an $R$-algebra structure $\eta_C:R\to C$, a henselian pair $(C,J)$ with $J=\mathfrak mC$, and an induced isomorphism $e_C:k\xrightarrow{\sim}C/J$. Each $B_i$ has finite presentation by clause (1) of [lem-weil-pbc-etale-algebra-finite-presentation-localization].

Existing statements used: lem-weil-pbc-pair-henselization, lem-weil-pbc-etale-algebra-finite-presentation-localization.

### Original step 3 → lem-trf-prime-pair-colimit-ind-etale-model

The henselian pair from Step 2 is local by a direct use of [def-weil-pbc-henselian-terminology]. For $z\in J$, the finite cyclic $C$-algebra $D=C/(1-z)$ has $JD=D$, so $D/JD=0$. Its sole idempotent has both $0$ and $1$ of $D$ as lifts; uniqueness gives $D=0$, so $1-z$ is a unit of $C$. If $x\notin J$, the field $C/J\cong k$ supplies $y\in C$ with $1-xy\in J$, so $xy$ and hence $x$ are units. Thus $C$ is local with maximal ideal $J$ and is henselian local because $(C,J)$ is henselian. The structural residue-field isomorphism $e_C:k\to C/J$ also gives $\eta_C^{-1}(J)=\mathfrak m$, so $\eta_C$ is local.

Existing statements used: def-weil-pbc-henselian-terminology.

### Original step 4 → lem-trf-initial-henselian-colimit-comparison

Write $\eta_H:R\to H$ for the given local map. By [def-weil-pbc-henselization-at-prime], $H$ is henselian local. Put $k_C=C/\mathfrak m_C=C/J$. Its local structure map induces $e_H:k\to k_H=H/\mathfrak m_H$. Apply [lem-weil-pbc-map-into-henselian-colimit] with base $R$, source algebra $C$, target $H$, prime $\mathfrak q=\mathfrak m_C$, and residue map $\tau=e_H\circ e_C^{-1}:k_C\to k_H$. Locality of $\eta_C$ and $\eta_H$ gives contraction $\mathfrak m$ on both sides, and $\tau$ is a $k$-algebra map. The lemma gives a local $R$-algebra map $f:C\to H$. Apply the defining universal property of $H$, with henselian local target $C$ and local map $\eta_C$, to obtain a local $R$-algebra map $g:H\to C$. Thus $f\eta_C=\eta_H$ and $g\eta_H=\eta_C$.

Existing statements used: def-weil-pbc-henselization-at-prime, lem-weil-pbc-map-into-henselian-colimit.

### Original step 5 → lem-trf-initial-henselian-colimit-comparison

Both $g\circ f$ and $\mathrm{id}_C$ are local $R$-algebra endomorphisms of $C$. On residue fields, $(\overline g\circ\overline f)\circ e_C=e_C$, since both maps are over $R$; cancel the isomorphism $e_C$ to get $\overline g\circ\overline f=\mathrm{id}_{k_C}$. Uniqueness in [lem-weil-pbc-map-into-henselian-colimit], now with source and henselian target $C$, prime $\mathfrak m_C$ and residue map $\mathrm{id}_{k_C}$, gives $g\circ f=\mathrm{id}_C$. Both $f\circ g$ and $\mathrm{id}_H$ are local maps satisfying $h\eta_H=\eta_H$, so the uniqueness in [def-weil-pbc-henselization-at-prime], with target $H$, gives $f\circ g=\mathrm{id}_H$. Hence $f$ and $g$ are inverse $R$-algebra isomorphisms. This does not assume in advance that $H$ has residue field $k$.

Existing statements used: lem-weil-pbc-map-into-henselian-colimit, def-weil-pbc-henselization-at-prime.

### Original step 6 → lem-trf-initial-henselian-colimit-comparison

Use the same small filtered diagram $(B_i)$ and replace its colimit coprojections by $j_i=f\circ\iota_i:B_i\to H$. These form a cocone since $f$ is an $R$-algebra map. To verify the colimit property of [def-weil-pbc-category-colimit], take any compatible $R$-algebra cocone $\mu_i:B_i\to T$. The original colimit gives a unique $u:C\to T$ with $u\iota_i=\mu_i$. This $u$ respects $R$: choose any stage $i$ (the index category is nonempty) with structural map $\eta_i:R\to B_i$; then $u\eta_C=u\iota_i\eta_i=\mu_i\eta_i=\eta_T$. Then $u\circ g:H\to T$ satisfies $(u\circ g)j_i=u\iota_i=\mu_i$. Conversely, if $v:H\to T$ has $vj_i=\mu_i$, uniqueness for $C$ gives $v\circ f=u$, whence $v=u\circ g$. Thus $H$, with its given structural map $\eta_H=f\eta_C$, is a filtered colimit of the same etale finitely presented $R$-algebras. By [def-weil-pbc-ind-etale-algebra], $R\to H$ is ind-etale.

Existing statements used: def-weil-pbc-category-colimit, def-weil-pbc-ind-etale-algebra.

### Original step 7 → lem-trf-prime-pair-colimit-ind-etale-model

Steps 1 and 6 give ind-etale maps $A\to R$ and $R\to H$ for the specified structural maps. Apply the composition clause of [lem-weil-pbc-ind-etale-stability] to conclude that the canonical composite $A\to A_{\mathfrak p}\to H$ is ind-etale. No argument or cited statement required Noetherianity.

Existing statements used: lem-weil-pbc-ind-etale-stability.

## Citation evidence

Every statement quoted below was opened and checked against the use in the corresponding new assembly step.

```json
[
 {
  "step": 1,
  "node": "lem-trf-prime-pair-colimit-ind-etale-model",
  "quote": "Let $A$ be a commutative ring, $\\mathfrak p\\subset A$ a prime ideal, $R=A_{\\mathfrak p}$, $\\mathfrak m=\\mathfrak pR$ and $k=R/\\mathfrak m$ [def-weil-pbc-localization-at-prime]. Let $\\mathcal E$ have as objects the etale $R$-algebras $B$ [def-weil-etale-morphism] for which the structural map $k\\to B/\\mathfrak mB$ is an isomorphism, and all $R$-algebra maps as morphisms. Choose a small skeleton $I$ of $\\mathcal E$ and a colimit cocone $(C,(\\iota_i:B_i\\to C))$ of its underlying ring diagram, with structural map $\\eta_C:R\\to C$, as in [lem-weil-pbc-pair-henselization]. Then $I$ is filtered, every $B_i$ is finitely presented over $R$ [def-weil-pbc-finitely-presented-algebra], and this same cocone is a colimit in commutative $R$-algebras [def-weil-pbc-category-colimit]. The ring $C$ is henselian local [def-weil-pbc-henselian-terminology], its maximal ideal is $J=\\mathfrak mC$, the map $\\eta_C$ is local, and the structural map $e_C:k\\xrightarrow{\\sim}C/J$ is an isomorphism. The three specified maps $A\\to R$, $R\\xrightarrow{\\eta_C}C$, and their composite $A\\to C$ are ind-etale [def-weil-pbc-ind-etale-algebra]. No Noetherian hypothesis is imposed."
 },
 {
  "step": 2,
  "node": "def-weil-pbc-henselization-at-prime",
  "quote": "Let $A$ be a commutative ring and $\\mathfrak p\\subset A$ a prime ideal. A commutative ring $H$ with an $A_{\\mathfrak p}$-algebra structure and a henselian-local-ring structure is a *henselization of $A_{\\mathfrak p}$* if the structural map $A_{\\mathfrak p}\\to H$ is local and, for every henselian local ring $T$ and every local map $g:A_{\\mathfrak p}\\to T$, there is a unique local map $h:H\\to T$ with $h\\circ(A_{\\mathfrak p}\\to H)=g$."
 },
 {
  "step": 2,
  "node": "lem-trf-initial-henselian-colimit-comparison",
  "quote": "Let $(R,\\mathfrak m,k)$ be a commutative local ring, where $k=R/\\mathfrak m$. Let $C,H$ be henselian local rings [def-weil-pbc-henselian-terminology] with local structural maps $\\eta_C:R\\to C$ and $\\eta_H:R\\to H$; a map of local rings is local when the inverse image of the target maximal ideal is the source maximal ideal. Suppose that $R\\to C$ is ind-etale [def-weil-pbc-ind-etale-algebra] and that its structural residue map $e_C:k\\to k_C=C/\\mathfrak m_C$ is an isomorphism. Assume only the following universal property for $H$: for every henselian local ring $T$ and local map $a:R\\to T$, there is exactly one local map $b:H\\to T$ with $b\\eta_H=a$. Then there are unique local $R$-algebra maps $f:C\\to H$ and $g:H\\to C$, with $gf=\\mathrm{id}_C$ and $fg=\\mathrm{id}_H$. In particular $f$ is an isomorphism over the specified maps from $R$; no residue-field identification or etale-colimit presentation of $H$ is assumed. Moreover, for any commutative ring $P$ with a ring map $P\\to R$, any small filtered diagram $(D_i)$ of commutative $P$-algebras, and any colimit cocone $(C,(\\lambda_i:D_i\\to C))$ of its underlying rings inducing the specified composite $P\\to R\\to C$ [def-weil-pbc-category-colimit], the maps $f\\lambda_i:D_i\\to H$ make $H$ a colimit of the same diagram both in rings and in commutative $P$-algebras, for the composite $P\\to R\\to H$. If all $D_i$ are etale [def-weil-etale-morphism] and finitely presented over $P$ [def-weil-pbc-finitely-presented-algebra], this gives an ind-etale presentation of that specified map $P\\to H$."
 },
 {
  "step": 2,
  "node": "def-weil-pbc-ind-etale-algebra",
  "quote": "Let $A$ be a commutative ring and let $B$ be an $A$-algebra. The\n$A$-algebra $B$ is *ind-etale* if it is a filtered colimit of etale\n$A$-algebras of finite presentation [def-weil-pbc-scheme-conventions]. It is\n*ind-Zariski* if such a presentation can be chosen with terms finite products\nof localizations $A_f$. The corresponding affine scheme $\\operatorname{Spec}B$\nis an inverse limit of affine etale schemes, with affine transition maps. The\nring map $A\\to B$ is *weakly etale* when the induced map\n$\\operatorname{Spec}B\\to\\operatorname{Spec}A$ is weakly etale in\n[def-weil-pbc-scheme-conventions]; equivalently, $B$ is flat as an $A$-module\nand is flat as a module over $B\\otimes_A B$ via the multiplication map\n$B\\otimes_A B\\to B$."
 },
 {
  "step": 3,
  "node": "def-weil-pbc-ind-etale-algebra",
  "quote": "Let $A$ be a commutative ring and let $B$ be an $A$-algebra. The\n$A$-algebra $B$ is *ind-etale* if it is a filtered colimit of etale\n$A$-algebras of finite presentation [def-weil-pbc-scheme-conventions]. It is\n*ind-Zariski* if such a presentation can be chosen with terms finite products\nof localizations $A_f$. The corresponding affine scheme $\\operatorname{Spec}B$\nis an inverse limit of affine etale schemes, with affine transition maps. The\nring map $A\\to B$ is *weakly etale* when the induced map\n$\\operatorname{Spec}B\\to\\operatorname{Spec}A$ is weakly etale in\n[def-weil-pbc-scheme-conventions]; equivalently, $B$ is flat as an $A$-module\nand is flat as a module over $B\\otimes_A B$ via the multiplication map\n$B\\otimes_A B\\to B$."
 }
]
```
