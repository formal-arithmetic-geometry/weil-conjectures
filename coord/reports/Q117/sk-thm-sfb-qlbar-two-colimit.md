# Q117: sk-thm-sfb-qlbar-two-colimit

## Files written

- `dag/nodes/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit.json`: repaired split, with the exact existing statement and Lean record retained. The six finite-descent steps are retained, apart from updating Step 5's forward reference. The former two long cocone steps are now eight short steps with explicit dependencies.
- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-scalar-tower-coherence.json`: one new statement-only lemma, status unsplit. It supplies canonical tensor reassociation, its tower equation, identity comparisons, and their termwise exact-derived versions for module objects in abelian sheaves. Mathlib verdict: no exact match. The ordinary-module theorem `ModuleCat.extendScalars_assoc` is a candidate, not a leaf for this sheaf module-object and derived assertion.
- `dag/units/sk-thm-sfb-qlbar-two-colimit.json`: only `realized` and `realized_by`; the unit's statement and its ten proof paragraphs are realized by the repaired key node.
- `citations.json`: 36 step citations, each quoting the cited statement verbatim. Complete statements are quoted to retain their hypotheses and coefficient-category conventions.

There is one new node and no new Mathlib leaves. Neither Lean files nor live project or launcher files were written.

## Attachments

None. I searched the supplied slopmaster2 `WeilConjectures/` tree for the blueprint id, two-colimit and coefficient-descent terminology, and the exact `constructibleCocone` / `derivedExtendScalarsSubfield` names. No declaration there states every clause. The audit names a TwoColimit module that is absent in the supplied slopmaster2 tree; that is stale-location evidence, not a finished attachment. I read the corresponding reference-only master `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean`: the preservation lemmas and object/Hom descent theorems are explicitly sorry, and the final three-field constructor uses those sorry theorems. Its conclusion covers the cocone clause, not all four assertions as independent proved declarations. This source therefore does not justify ATTACH.

## WANTED

None. The current blueprint, Stacks source, and Mathlib sources needed for this repair are available locally.

## What was wrong and what changed

The dedicated return in `coord/returns/Q117.md` requires the hidden arguments of the long final step to be extracted, while retaining the statement and route. I found three arguments there: existence of a common finite field, coherence of tensor comparisons after scalar extension, and eventual equality in a filtered Hom colimit. The first and third already have exact existing DAG statements. I cite `def-weil-finite-subextension-directed-set` and `lem-weil-pbc-filtered-colimit-sets-elementwise`, rather than create duplicates. The middle argument has no matching sheaf-module-object tower statement, so it becomes `lem-sfb-flat-scalar-tower-coherence`. The equally long preceding cocone-construction step contained the same comparison construction and is repaired using this lemma as well.

This is not a replacement of descent by the existing cocone-surjectivity or cocone-injectivity clauses. The item still descends a morphism by the Hom bijection, chooses a representative, and writes the conjugation producing a morphism between the directly extended original objects. The new lemma contains no constructibility or finite-descent assertion, and no 2-colimit conclusion. It is a smaller generic tensor comparison fact. The scalar-tower lemma remains unsplit, with no proof or proof dependencies.

The exact imported statement, its hypotheses, `lean` and `lean_audit`, all blueprint import fields and earlier search history are retained. No statement dispute or unit-route departure was found. The proof origin remains agent: the blueprint's proof is agent-written, and the coherence calculation is made explicit from the tensor construction rather than attributed as a stated theorem to Stacks.

## Searches and Mathlib assessment

I searched the whole DAG and blueprint for common finite subextensions, filtered-colimit representatives/equality, tensor associativity, change of rings, scalar tower and tensor coherence, then read the plausible statements. I also searched the project Lean source before creating the new node. `searches.jsonl` records the actual msearch invocations, including both semantic phrasings, Loogle and two source grep searches. All returned successfully. The first Loogle query and the CategoryTheory grep returned no hits; the corrected Loogle query and Algebra/Category grep found ordinary-module associativity. The new node records those searches exactly as run.

I read `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`, lines 984–1034: `extendScalarsComp` is an adjunction-conjugate comparison for modules over ordinary rings; `extendScalarsComp_hom_app_one_tmul` gives its tensor formula and `extendScalars_assoc` proves the coherence equation. This is useful implementation material but does not state the same theorem about internal module objects in sheaves and the descended comparisons on their unbounded derived categories. The second semantic search also found `Bimod.triangle_bimod`; I read the bimodule definition, associator and pentagon locations in `Mathlib/CategoryTheory/Monoidal/Bimod.lean`. Bimodule coherence is background, but identifying that tensor construction with the actual scalar-extension functors and passing it through derived localization is additional work. Neither candidate makes the complete new statement a one-line Mathlib specialization.

## Not duplicates

lem-sfb-flat-scalar-tower-coherence vs lem-weil-scalar-extension-composition: the latter treats the rationalized category of integral lattices for finite field extensions and asserts composition compatibility, not the explicit three-map coherence equation for arbitrary sheaf ring objects and exact-derived extensions.

lem-sfb-flat-scalar-tower-coherence vs lem-pc-graded-scalar-extension-coherence: the latter is a degreewise statement for complexes of ordinary modules over a ring diagram; it does not concern sheaf module objects or their derived localization.

lem-sfb-flat-scalar-tower-coherence vs def-sfb-derived-extend-comp-iso: that definition supplies a two-step natural isomorphism to the algebraic-closure coefficient category; its statement does not give the finite-to-finite comparison or the three-map tower equation.

lem-sfb-flat-scalar-tower-coherence vs lem-weil-pbc-etale-module-ring-iso-tensor: both source records refer to Stacks 03CZ, but the existing lemma concerns tensoring along an isomorphism of ring sheaves and its compatibility with a given pullback comparison. It does not give scalar-tower associativity.

lem-sfb-flat-scalar-tower-coherence vs lem-weil-derived-scalar-extension-restriction-adjunction: the shared 03CZ reference concerns the tensor/restriction adjunction; this existing node is an integral-to-torsion derived adjunction, not tower coherence.

lem-sfb-flat-scalar-tower-coherence vs lem-coef-finite-free-extension: the shared 03CZ background does not make its finite-coefficient six-operation comparison a statement about arbitrary sheaf ring-object towers.

lem-sfb-flat-scalar-tower-coherence vs lem-weil-pbc-ringed-topoi-module-adjunction: this existing node asserts the module pullback/direct-image adjunction. The new node asserts comparisons and their associativity equation, not an adjunction.

lem-sfb-flat-scalar-tower-coherence vs sk-thm-sfb-qlbar-two-colimit: the new node has no finite-field descent, constructible categories or 2-colimit conclusion; it isolates the tensor identity used in the retained proof.

lem-sfb-flat-scalar-tower-coherence vs lem-weil-sheaf-scalar-extension-ring-iso: this newly synchronized node shares the 03CZ source tag, but assumes one ring-sheaf map is an isomorphism and identifies its scalar extension with the transported module structure. It has no comparison between successive extensions, no three-map tower equation, and no derived localization assertion. Thus it does not state the new lemma.

## Review by Q117

I read the current main-20261015 chapter and key unit, the item's `_section.md` and proof file, and the statements of every node cited by the repaired proof. The main source proves lisse, Hom and bounded-object descent first and then obtains the ordinary-category 2-colimit; the repair follows that order. I also read Stacks `categories.tex`, Section Tag 04AX (`section-directed-colimits`), including the representative and eventual-equality description immediately following `definition-directed`. This supports precisely the two set-colimit uses here. For the new tensor lemma I read Stacks `sites-modules.tex`, Tag 03CZ (`lemma-adjointness-tensor-restrict`), its preceding definition of sheafified change of rings, and Tag 03CU for the presheaf tensor adjunction. These supply the tensor construction; the three-map coherence equation is the explicitly extracted argument of the blueprint, not a verbatim theorem of 03CZ. No SGA source is used.

For Step 1, I checked the standing setting really assumes separated finite type over a field. The finite-type definition supplies quasi-compactness; separatedness gives a closed diagonal using the proper-morphism definition's separated clause, without assuming properness of X. The affine quotient description of a closed immersion, affine qcqs lemma and quasi-separated definition show the diagonal is quasi-compact. Clause (2) of the qcqs permanence node applies with affine base Spec k. Thus the qcqs hypothesis of lisse descent is available.

For Step 2, I checked that the flatness nodes state preservation of finite limits for exactly the pulled-back coefficient ring maps. The current change-of-scalars clause (2) gives right exactness, and the ambient module categories are abelian. Thus the functors are exact; the exact-functor clause of the derived-category statement identifies the unbounded derived functor with the termwise functor. No assertion about an arbitrary nonflat ring map is made.

Steps 3, 4 and 5 cite, respectively, clause (1) of the existing lisse descent statement, clause (3) of the derived-Hom descent statement for every integer r, and the existing bounded-object descent statement including its finite enlargement clause. I checked each statement actually names the pulled-back condensed coefficients or its defining dependencies. The lisse lemma needs only qcqs, already checked, while the other two require the standing scheme. No lattice category is substituted for the module-object category. Step 6 uses the rational-coefficient equality in the coefficient-heart statement and the explicit fullness in the bounded-constructible definition to identify precisely the ambient Hom sets.

Step 7 checks the ambient categories from the actual derived scalar-extension definitions, including the clarified paragraph of the extension-to-Qlb node identifying it as condensed coefficient change. Step 8 uses exactly the two constructibility-preservation assertions and the four full-subcategory/restricted-functor definitions. Step 9 cites the new scalar-tower lemma for the actual formulas and coherence identity, and the two transitivity definitions and cocone definition only for what they define. I checked the domain of its equation is Phi_F(T_HF(T_EH K)) and both sides land in Phi_E K. Exactness for every map and composite in E_X → H_X → F_X → QbarX comes from Step 2; restriction is legitimate by Step 8. Thus this step does not take the formula or coherence from a definition that only says an isomorphism exists.

For Step 10, the finite-subextension statement itself says composita are finite and the index is a nonempty directed set. The fields are a set of subfields of the fixed closure, so the relevant preorder category is small in a containing universe. The upper cone containing H is nonempty and remains directed. The new lemma's tower and unit equations supply the functorial Hom transitions. This verifies the small filtered hypothesis required for the colimit node, rather than applying a small-category theorem to an unspecified large index.

Step 11 is only substitution of the already proved object descent into the Obj definition. Step 12 uses surjectivity from the earlier Hom assertion and clause (1) of the elementwise colimit lemma to select an actual stage F and morphism h. The inverse theta is on the target side in the conjugated morphism phi_H, so its type is Phi_H A → Phi_H B. Step 13 is elementary conjugation algebra after citing the new coherence equation: g = alpha_2 h alpha_1^{-1} has source T_E1,F K_1 and target T_E2,F K_2, and cancellation yields the Hom-surj formula with the correct theta orientations. No unidentified comparison is hidden in the word 'transport'. Step 14 uses injectivity of the already established Hom bijection and exactly clause (3) of the set-colimit lemma, whose small filtered hypothesis was checked in Step 10. It supplies one transition on both g and g', as required, not two possibly different maps.

After the first full dry run passed at 67f07759c0, the push-time duplicate gate found the newly synchronized lem-weil-sheaf-scalar-extension-ring-iso. I opened and read its entire statement, checked its invertible-map hypothesis and specified sheafification normalization, and added the explicit distinction above. Its assertion does not subsume tower coherence; no mathematical or node change was needed.

I tested the new statement when all ring maps are identities, when adjacent rings coincide, for the zero module and zero rings, and on a site with one object. The comparisons reduce to tensor units, remain well typed, and impose neither injectivity nor nonzero-ring assumptions. The exact-derived clause explicitly assumes exactness of every functor used, including composites; its general nonflat version is not asserted. Natural maps commute with differentials termwise, and equality of natural maps survives localization. For the item I checked empty X, zero complexes, negative shifts, rank zero, equal coefficient fields and morphisms already defined over the common field. The fixed-field index includes the field itself. All formulas and citations still apply; no strict extension is required.

I checked B–E of delivery-errors against the files: the one new node is self-contained, statement-only and searched; its notions have definition dependencies; none of its assertions is a clause of finite descent. All cited statements are recorded verbatim in citations.json. Source tags are given with their actual labels, and the distinction between a source's tensor background and the agent's coherence argument is explicit. Generic off-unit tools are declared in split_report.tool_uses for the maintainer to judge; I did not change maintainer-owned tool_uses. Every proof step is below 2000 characters (largest 801), because the non-elementary comparison fact is an actual cited node, not because an unchanged long argument was merely broken into paragraphs.

## Remaining work

Stage 1 for the new scalar-tower lemma remains open by design: it has a complete statement, searched candidates, exact source context, and no proof. No part of this item's split is left unfinished. Independent maintainer review follows the direct delivery.
