# Q157: lem-sfb-field-extension-irreducible-components

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-extension-irreducible-components.json: statement item, now split into eight proof steps. The statement and statement dependencies are unchanged; no exact Mathlib match was found.
- citations.json: 42 citations, one for each step/node pair, with a verbatim copy of the cited statement.
- searches.jsonl: actual searches made by msearch.py. The inherited item searches remain intact in the node; new logged searches were appended.
- report.md: this report. write_split.py is only a sandbox-local construction script.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for irreducibleComponents, irreducible components, and field-base-change terminology. GenericComponentsSplit and FiniteFieldClosedComponentDescent concern finite-type/descent problems; the curve affine-base-change assertions concern regular curves. No project declaration states all the unrestricted assertions here. I did not infer completion from sorry declarations.

## WANTED

None. All sources used are present under literature/stacks-project.

## Faults and changes

The live item had no proof. Its Stacks statement is correct, including the actual image of a component (not merely the closure), nonemptiness, and arbitrary field extensions of possibly infinite degree. I kept it unchanged. The source uses separable closures; I use an algebraic closure Omega of K and the relative algebraic closure A of k inside Omega, which provides the same commuting square with algebraic vertical extensions and an algebraically closed horizontal base. This is a choice of closures inside the same source argument, not a replacement of the unit route.

The sandbox initially contained only dispatcher brief markers: no item, report, search log or delivery receipt survived. A process check found no active Q157 deliver.py or msearch.py invocation before I started work. I did not repeat an interrupted mutation. No repository or launcher file was written, no git command was run by me, and no Lean or build tool was run.

The existing blueprint.from.node is null: tools/blueprint_refs.py ancestor reports None for this lineage. I retained that inherited field and its explicit non-unspecified place and via chain. Whole-blueprint searches for irreducible component, 04KW and 04KX found no blueprint statement of this result. The latest blueprint direct-images proof was read; this item remains an auxiliary algebraic-geometric tool in the existing alteration/Picard lineage. I did not change chapter or unit records.

## Not duplicates

No new nodes are proposed. The whole-DAG searches found the existing generic-point criterion lem-trf-field-extension-residual-generic-components, field-tensor theorem lem-weil-pbc-field-tensor-irreducible, and component/open-map theorems; I reuse them. The first controls generic points but does not say an entire component maps onto its closure. lem-sfb-finite-scalar-extension-generic-points only treats finite extensions and residue degrees. The two field-extension Stacks tags also occur in the parent lem-sfb-group-local-minimal-prime, whose group-specific neutral-component statement is different. None is a reason to create a duplicate.

## Review by Q157

I read Stacks varieties.tex, labels lemma-inverse-image-irreducible (04KW) and lemma-image-irreducible (04KX), including both complete proofs and the preceding separably-closed-field component proof. The first proof uses flat lifting of generalizations; the second first reduces through a closed-field square and then uses integrality and closedness, before proving surjectivity using the nonempty inverse image. I preserved these mechanisms, and did not make the false inference that an arbitrary flat projection is closed. Supporting sources opened were schemes.tex 01J3 for the closed-subscheme realization; morphisms.tex lemma-generalizations-lift-flat (03HV); algebra.tex lemma-base-change-integral (02JK), lemma-going-up-closed (00HZ) and lemma-separably-closed-irreducible (00I7); varieties.tex 038F; topology.tex 037A; and fields.tex 09GR with the statements of 09GJ, 09GT as recorded in the existing Mathlib leaves. There are no newly created nodes requiring source review.

For step 1 I opened each of lem-pc-field-extension-flat, lem-weil-pbc-flat-morphism-base-change, lem-pc-field-extension-surjective, lem-weil-pbc-surjective-base-change, lem-weil-pbc-scheme-sober, lem-sc-irreducible-components-cover, def-sc-generic-point, def-weil-irreducible-components and lem-trf-field-extension-residual-generic-components. The first four give flatness and surjectivity for exactly an arbitrary field-extension projection. The sobriety statement and component-cover statement give existence/uniqueness and maximality used in the explicit no-proper-generalization argument. The residual-generic-component statement's forward implication gives exactly the generic-point image assertion. I take no actual-image theorem from that statement. Its hypotheses impose no Noetherianity, algebraicity or separability.

For step 2, lem-weil-pbc-closed-subset-closed-subscheme gives an actual closed immersion with image T; it is not just a definition. lem-weil-pbc-closed-immersion-base-change supplies the closed immersion after base change. def-weil-closed-immersion includes the affine quotient description, def-weil-residue-field supplies the induced residue-field map, and def-pc-scheme-fibre supplies the canonical map from Spec of a residue field. The fibre-product definition supplies the unique paired map. I wrote out why the ideal is killed at every point over T, so the identification with the set inverse image does not assume that arbitrary set containment implies scheme factorization. This is a few-line quotient argument and is correctly marked elementary with its existing inputs cited.

For step 3 the residual-generic-component statement is applied to the irreducible closed subscheme Z, whose sole component has generic point eta. The closed immersion's subspace topology lets the no-proper-generalization criterion be used both in Z_K and X_K. I explicitly check that a generalization of xi is still above eta and therefore in Z_K. The component-cover theorem then gives the union, while step 1's surjectivity gives nonemptiness. This step neither assumes components are finite in number nor assumes their generic local rings are fields. Its citations to sobriety, component coverage, generic points and component maximality say precisely these facts.

For step 4, def-weil-finite-integral-morphism gives the affine integral definition, and algebraicity over a field gives a monic equation by dividing the leading coefficient. lem-sbc-integral-morphism-base-change applies to this integral spectrum map without finite-degree hypotheses. pqf-lem-integral-univclosed gives universally closed, and def-weil-proper-morphism gives closedness by the identity base change. The generic-point input is the same unrestricted forward implication already checked. Continuity and the closure of a singleton show both inclusions in r(B)=T; this is why actual images are obtained. Step 5 is only component selection from steps 2--3 plus maximality from def-weil-irreducible-components; no new result is hidden there.

For step 6, def-pc-scheme-fibre includes the homeomorphism to the set-theoretic fibre, and def-pc-fibre-product plus lem-weil-pbc-fibre-product-affine-spectra gives Spec(kappa(y) tensor_F E). def-weil-residue-field makes kappa(y) an F-field extension. lem-weil-pbc-field-tensor-irreducible applies to these two field extensions over separably closed F and supplies irreducibility including nonemptiness. lem-sc-scheme-over-field-universally-open supplies openness of this exact projection for unrestricted Y and E. lem-sc-open-map-irreducible-fibres-components supplies both actual images and preimages as mutually inverse component maps, with continuity, openness and all nonempty irreducible fibres verified. This is the source's 038F/037A argument, using the more precise existing tensor input rather than adding a separably-closed version of the item's own image clause.

For step 7, lem-pc-algebraic-closure-exists-unique supplies Omega, and lem-weil-pbc-relative-algebraic-closure-algclosed supplies A inside Omega with exactly algebraicity over k and algebraic closedness. I wrote the elementary successive-root argument for separable closedness instead of silently appealing to an uncited field theorem. def-weil-algebraic-closure and def-kun-separably-closed state the respective meanings. The fibre-product universal property gives the commuting square. The algebraic case is applied only to Omega/K and A/k; the separably-closed case is applied only over A. Thus Omega/A need not be algebraic. Taking D above C uses surjectivity proved in step 5, not an unjustified lifting of entire components under an arbitrary map. Step 8 uses only the earlier inverse-image union, the proven image statement and component maximality. citations.json copies an actual statement for every cited node in all eight steps.

I checked small cases: X empty (the component map is the empty surjection); K=k; X=Spec C over R and K=C (two components can map to the same component, so no bijection is asserted in general); inseparable extensions (nilpotents do not affect component arguments); X=Spec k(t) and K=k(u) (the residual tensor spectrum is not assumed zero dimensional); and an arbitrary disconnected or non-quasi-compact X (the proof never lists finitely many components or chooses a finite affine cover). The proof uses neither finite type nor reducedness of X or T. No step exceeds 2000 characters; the closure square and all auxiliary comparisons are written out rather than hidden behind “standard” or “transports”.

Against delivery-errors B--E: there are no new hollow, duplicate, elementary or clause-restatement nodes; all non-elementary inputs are cited statements, not facts taken from cited proofs or definitions; sources are recorded by label and tag; no new assumptions or weakened conclusion are introduced; the assembly makes no circular use of the item. The two off-unit statement tools are declared in split_report.tool_uses with their specific purpose (generic-point image under flat field extension and separably-closed field tensor irreducibility). They supply general algebraic-geometric tools and do not replace the constructibility unit's route. All remaining proof inputs are definitions or Mathlib leaves.

## Unfinished work

None in the natural-language split. Stage 2 and Lean work remain outside this assignment.
